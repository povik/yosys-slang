//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/SystemSubroutine.h"
#include "slang/diagnostics/CompilationDiags.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/LookupDiags.h"
#include "slang/driver/Driver.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/text/Json.h"
#include "slang/util/Util.h"

#include "kernel/bitpattern.h"
#include "kernel/celltypes.h"
#include "kernel/fmt.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"

#include "version.h"
#include "initial_eval.h"
#include "slang_frontend.h"
#include "diag.h"
#include "async_pattern.h"
#include "variables.h"

namespace slang_frontend {

void SynthesisSettings::addOptions(slang::CommandLine &cmdLine) {
	cmdLine.add("--dump-ast", dump_ast, "Dump the AST");
	cmdLine.add("--no-proc", no_proc, "Disable lowering of processes");
	// TODO: deprecate; now on by default
	cmdLine.add("--compat-mode", compat_mode,
				"Be relaxed about the synthesis semantics of some language constructs");
	cmdLine.add("--keep-hierarchy", keep_hierarchy,
				"Keep hierarchy (experimental; may crash)");
	cmdLine.add("--best-effort-hierarchy", best_effort_hierarchy,
				"Keep hierarchy in a 'best effort' mode");
	cmdLine.add("--ignore-timing", ignore_timing,
				"Ignore delays for synthesis");
	cmdLine.add("--ignore-initial", ignore_initial,
				"Ignore initial blocks for synthesis");
	cmdLine.add("--ignore-assertions", ignore_assertions,
				"Ignore assertions and formal statements in input");
	cmdLine.add("--unroll-limit", unroll_limit_,
				"Set unrolling limit (default: 4000)", "<limit>");
	// TODO: deprecate; now on by default
	cmdLine.add("--extern-modules", extern_modules,
				"Import as an instantiable blackbox any module which was previously "
				"loaded into the current design with a Yosys command; this allows composing "
				"hierarchy of SystemVerilog and non-SystemVerilog modules");
	cmdLine.add("--no-implicit-memories", no_implicit_memories,
				"Require a memory style attribute to consider a variable for memory inference");
	cmdLine.add("--empty-blackboxes", empty_blackboxes,
				"Assume empty modules are blackboxes");
	cmdLine.add("--ast-compilation-only", ast_compilation_only,
				"For developers: stop after the AST is fully compiled");
	cmdLine.add("--no-default-translate-off-format", no_default_translate_off,
				"Do not interpret any comment directives marking disabled input unless specified with '--translate-off-format'");
}

namespace ast = slang::ast;
namespace syntax = slang::syntax;
namespace parsing = slang::parsing;

ast::Compilation *global_compilation;
const slang::SourceManager *global_sourcemgr;

slang::SourceRange source_location(const ast::Symbol &obj)			{ return slang::SourceRange(obj.location, obj.location); }
slang::SourceRange source_location(const ast::Expression &expr)		{ return expr.sourceRange; }
slang::SourceRange source_location(const ast::Statement &stmt)		{ return stmt.sourceRange; }
slang::SourceRange source_location(const ast::TimingControl &stmt)	{ return stmt.sourceRange; }

template<typename T>
std::string format_src(const T &obj)
{
	auto sm = global_sourcemgr;
	auto sr = source_location(obj);

	if (!sm->isFileLoc(sr.start()) || !sm->isFileLoc(sr.end()))
		return "";

	if (sr.start() == sr.end()) {
		auto loc = sr.start();
		std::string fn{sm->getFileName(loc)};
		return Yosys::stringf("%s:%d.%d", fn.c_str(),
			(int) sm->getLineNumber(loc), (int) sm->getColumnNumber(loc));
	} else {
		std::string fn{sm->getFileName(sr.start())};
		return Yosys::stringf("%s:%d.%d-%d.%d", fn.c_str(),
			(int) sm->getLineNumber(sr.start()), (int) sm->getColumnNumber(sr.start()),
			(int) sm->getLineNumber(sr.end()), (int) sm->getColumnNumber(sr.end()));
	}
}

};

#include "addressing.h"

namespace slang_frontend {

// step outside slang_frontend namespace for a minute, to patch in
// unimplemented() into the SlangInitial evaluator
};
slang::ast::Statement::EvalResult SlangInitial::EvalVisitor::visit(const slang::ast::Statement &stmt)
{
	unimplemented(stmt);
}
namespace slang_frontend {

const RTLIL::IdString id(const std::string_view &view)
{
	return RTLIL::escape_id(std::string(view));
}

static const RTLIL::IdString module_type_id(const ast::InstanceBodySymbol &sym)
{
	ast_invariant(sym, sym.parentInstance && sym.parentInstance->isModule());
	std::string instance = sym.getHierarchicalPath();
	if (instance == sym.name)
		return RTLIL::escape_id(std::string(sym.name));
	else
		return RTLIL::escape_id(std::string(sym.name) + "$" + instance);
}

static const RTLIL::Const convert_svint(const slang::SVInt &svint)
{
	std::vector<RTLIL::State> bits;
	bits.reserve(svint.getBitWidth());
	for (int i = 0; i < (int) svint.getBitWidth(); i++)
	switch (svint[i].value) {
	case 0: bits.push_back(RTLIL::State::S0); break;
	case 1: bits.push_back(RTLIL::State::S1); break;
	case slang::logic_t::X_VALUE: bits.push_back(RTLIL::State::Sx); break;
	case slang::logic_t::Z_VALUE: bits.push_back(RTLIL::State::Sz); break;
	}
	return bits;
}

static const RTLIL::Const convert_const(const slang::ConstantValue &constval)
{
	log_assert(!constval.bad());
	log_assert(!constval.isReal());
	log_assert(!constval.isShortReal());
	log_assert(!constval.isUnbounded());
	log_assert(!constval.isMap());
	log_assert(!constval.isQueue());
	log_assert(!constval.isUnion());

	if (constval.isInteger()) {
		return convert_svint(constval.integer());
	} else if (constval.isUnpacked()) {
		std::vector<RTLIL::State> bits;
		bits.reserve(constval.getBitstreamWidth());

		auto elems = constval.elements();
		for (auto it = elems.rbegin(); it != elems.rend(); it++) {
			auto piece = convert_const(*it);
			bits.insert(bits.end(), piece.begin(), piece.end());
		}

		log_assert(bits.size() == constval.getBitstreamWidth());
		return bits;
	} else if (constval.isString()) {
		RTLIL::Const ret = convert_svint(constval.convertToInt().integer());
		ret.flags |= RTLIL::CONST_FLAG_STRING;
		return ret;
	} else if (constval.isNullHandle()) {
		return {};
	}

	log_abort();
}

static const RTLIL::Const reverse_data(RTLIL::Const &orig, int width)
{
	std::vector<RTLIL::State> bits;
	log_assert(orig.size() % width == 0);
	bits.reserve(orig.size());
	for (int i = orig.size() - width; i >= 0; i -= width)
		bits.insert(bits.end(), orig.begin() + i, orig.begin() + i + width);
	return bits;
}

template<typename T>
void transfer_attrs(T &from, RTLIL::AttrObject *to)
{
	auto src = format_src(from);
	if (!src.empty())
		to->attributes[ID::src] = src;

	for (auto attr : global_compilation->getAttributes(from)) {
		to->attributes[id(attr->name)] = convert_const(attr->getValue());

		// slang converts string literals to integer constants per the spec;
		// we need to dig into the syntax tree to recover the information
		if (attr->getSyntax() &&
			attr->getSyntax()->kind == syntax::SyntaxKind::AttributeSpec &&
			attr->getSyntax()->template as<syntax::AttributeSpecSyntax>().value &&
			attr->getSyntax()->template as<syntax::AttributeSpecSyntax>().value->expr->kind ==
				syntax::SyntaxKind::StringLiteralExpression) {
			to->attributes[id(attr->name)].flags |= RTLIL::CONST_FLAG_STRING;
		}
	}
}
template void transfer_attrs<const ast::Symbol>(const ast::Symbol &from, RTLIL::AttrObject *to);

#define assert_nonstatic_free(signal) \
	for (auto bit : (signal)) \
		log_assert(!(bit.wire && bit.wire->get_bool_attribute(ID($nonstatic))));

};

#include "cases.h"
#include "memory.h"

namespace slang_frontend {

static Yosys::pool<VariableBit> detect_possibly_unassigned_subset(Yosys::pool<VariableBit> &signals, Case *rule, int level=0)
{
	Yosys::pool<VariableBit> remaining = signals;
	bool debug = false;

	for (auto &action : rule->actions) {
		if (debug) {
			log_debug("%saction %s<=%s (mask %s)\n", std::string(level, ' ').c_str(),
					  "FIXME" /* log_signal(action.lvalue) */, log_signal(action.unmasked_rvalue), log_signal(action.mask));
		}

		if (action.mask.is_fully_ones())
		for (auto bit : action.lvalue)
			remaining.erase(bit);
	}

	for (auto switch_ : rule->switches) {
		if (debug) {
			log_debug("%sswitch %s\n", std::string(level, ' ').c_str(), log_signal(switch_->signal));
		}

		if (remaining.empty())
			break;

		Yosys::pool<VariableBit> new_remaining;
		Yosys::BitPatternPool pool(switch_->signal);
		for (auto case_ : switch_->cases) {
			if (!switch_->signal.empty() && pool.empty())
				break;

			if (debug) {
				log_debug("%s case ", std::string(level, ' ').c_str());
				for (auto compare : case_->compare)
					log_debug("%s ", log_signal(compare));
				log_debug("\n");
			}

			bool selectable = false;
			if (case_->compare.empty()) {
				// we have reached a default, by now we know this case is full
				selectable = pool.take_all() || switch_->signal.empty();
			} else {
				for (auto compare : case_->compare) {
					if (!compare.is_fully_const()) {
						if (!pool.empty())
							selectable = true;
					} else {
						if (pool.take(compare))
							selectable = true;
					}
				}
			}

			if (selectable) {
				for (auto bit : detect_possibly_unassigned_subset(remaining, case_, level + 2))
					new_remaining.insert(bit);
			}
		}

		if (switch_->full_case || pool.empty())
			remaining.swap(new_remaining);
	}

	return remaining;
}

bool ProcessTiming::implicit() const
{
	return triggers.empty();
}

// extract trigger for side-effect cells like $print, $check
void ProcessTiming::extract_trigger(NetlistContext &netlist, Yosys::Cell *cell, RTLIL::SigBit enable)
{
	auto &params = cell->parameters;

	cell->setPort(ID::EN, netlist.LogicAnd(background_enable, enable));

	if (implicit()) {
		params[ID::TRG_ENABLE] = false;
		params[ID::TRG_WIDTH] = 0;
		params[ID::TRG_POLARITY] = {};
		cell->setPort(ID::TRG, {});
	} else {
		params[ID::TRG_ENABLE] = true;
		params[ID::TRG_WIDTH] = triggers.size();
		std::vector<RTLIL::State> pol_bits;
		RTLIL::SigSpec trg_signals;
		for (auto trigger : triggers) {
			pol_bits.push_back(trigger.edge_polarity ? RTLIL::S1 : RTLIL::S0);
			trg_signals.append(trigger.signal);
		}
		params[ID::TRG_POLARITY] = RTLIL::Const(pol_bits);
		cell->setPort(ID::TRG, trg_signals);
	}
}

// For $check, $print cells
void ProceduralContext::set_effects_trigger(RTLIL::Cell *cell)
{
	timing.extract_trigger(netlist, cell, case_enable());
}

RTLIL::SigBit inside_comparison(EvalContext &eval, RTLIL::SigSpec left,
								const ast::Expression &expr)
{
	require(expr, !expr.type->isUnpackedArray());

	if (expr.kind == ast::ExpressionKind::ValueRange) {
		const auto& vexpr = expr.as<ast::ValueRangeExpression>();
		require(expr, vexpr.rangeKind == ast::ValueRangeKind::Simple);
		ast_invariant(expr, vexpr.left().type->isMatching(*vexpr.right().type));
		return eval.netlist.LogicAnd(
			eval.netlist.Ge(left, eval(vexpr.left()), vexpr.left().type->isSigned()),
			eval.netlist.Le(left, eval(vexpr.right()), vexpr.right().type->isSigned())
		);
	} else {
		RTLIL::SigSpec expr_signal = eval(expr);
		require(expr, expr_signal.size() == left.size());

		if (expr.type->isIntegral()) {
			require(expr, expr_signal.is_fully_const());
			return eval.netlist.EqWildcard(left, expr_signal);
		} else {
			return eval.netlist.Eq(left, expr_signal);
		}
	}
}

bool NetlistContext::is_inferred_memory(const ast::Symbol &symbol)
{
	return detected_memories.count(&symbol);
}

bool NetlistContext::is_inferred_memory(const ast::Expression &expr)
{
	return expr.kind == ast::ExpressionKind::NamedValue &&
			is_inferred_memory(expr.as<ast::NamedValueExpression>().symbol);
}

std::string format_wchunk(RTLIL::SigChunk chunk)
{
	log_assert(chunk.wire != nullptr);
	if (chunk.width == chunk.wire->width)
		return chunk.wire->name.c_str();
	else if (chunk.width)
		return Yosys::stringf("%s[%d]", chunk.wire->name.c_str(), chunk.offset);
	else
		return Yosys::stringf("%s[%d:%d]", chunk.wire->name.c_str(), chunk.offset, chunk.offset + chunk.width);
}

const ast::InstanceBodySymbol &get_instance_body(SynthesisSettings &settings, const ast::InstanceSymbol &instance)
{
	if (!settings.disable_instance_caching && instance.getCanonicalBody())
		return *instance.getCanonicalBody();
	else
		return instance.body;
}

using VariableState = ProceduralContext::VariableState;

void VariableState::set(VariableBits lhs, RTLIL::SigSpec value)
{
	log_assert((int) lhs.size() == value.size());

	for (int i = 0; i < (int) lhs.size(); i++) {
		VariableBit bit = lhs[i];

		if (!revert.count(bit)) {
			if (visible_assignments.count(bit))
				revert[bit] = visible_assignments.at(bit);
			else
				revert[bit] = RTLIL::Sm;
		}

		visible_assignments[bit] = value[i];
	}
}

RTLIL::SigSpec VariableState::evaluate(NetlistContext &netlist, VariableBits vbits)
{
	RTLIL::SigSpec ret;
	for (auto vbit : vbits) {
		if (visible_assignments.count(vbit)) {
			ret.append(visible_assignments.at(vbit));
		} else {
			log_assert(vbit.variable.kind == Variable::Static);
			RTLIL::SigBit bit{netlist.wire(*vbit.variable.get_symbol()), vbit.offset};
			ret.append(bit);
		}
	}
	return ret;
}

RTLIL::SigSpec VariableState::evaluate(NetlistContext &netlist, VariableChunk vchunk)
{
	RTLIL::SigSpec ret;
	for (int i = 0; i < vchunk.bitwidth(); i++) {
		if (visible_assignments.count(vchunk[i])) {
			ret.append(visible_assignments.at(vchunk[i]));
		} else {
			log_assert(vchunk.variable.kind == Variable::Static);
			RTLIL::SigBit bit{netlist.wire(*vchunk.variable.get_symbol()), vchunk.base + i};
			ret.append(bit);
		}
	}
	return ret;
}

void VariableState::save(Map &save)
{
	revert.swap(save);
}

std::pair<VariableBits, RTLIL::SigSpec> VariableState::restore(Map &save)
{
	VariableBits lreverted;
	RTLIL::SigSpec rreverted;

	for (auto pair : revert)
		lreverted.push_back(pair.first);
	std::sort(lreverted.begin(), lreverted.end());

	//rreverted.reserve(lreverted.size());
	for (auto bit : lreverted)
		rreverted.append(visible_assignments.at(bit));

	for (auto pair : revert) {
		if (pair.second == RTLIL::Sm)
			visible_assignments.erase(pair.first);
		else
			visible_assignments[pair.first] = pair.second;
	}

	save.swap(revert);
	return {lreverted, rreverted};
}

struct StatementVisitor : public ast::ASTVisitor<StatementVisitor, true, false> {
public:
	NetlistContext &netlist;
	ProceduralContext &context;
	EvalContext &eval;
	UnrollLimitTracking &unroll_limit;

	StatementVisitor(ProceduralContext &context)
		: netlist(context.netlist), context(context), eval(context.eval), unroll_limit(context.unroll_limit) {}

	struct SwitchHelper {
		Case *parent;
		Case *&current_case;
		Switch *sw;

		using VariableState = ProceduralContext::VariableState;

		VariableState &vstate;
		VariableState::Map save_map;
		std::vector<std::tuple<Case *, VariableBits, RTLIL::SigSpec>> branch_updates;
		bool entered = false, finished = false;

		SwitchHelper(Case *&current_case, VariableState &vstate, RTLIL::SigSpec signal)
			: parent(current_case), current_case(current_case), vstate(vstate)
		{
			sw = parent->add_switch(signal);
		}

		~SwitchHelper()
		{
			log_assert(!entered);
			log_assert(branch_updates.empty() || finished);
		}

		SwitchHelper(const SwitchHelper&) = delete;
		SwitchHelper& operator=(const SwitchHelper&) = delete;
		SwitchHelper(SwitchHelper&& other)
			: parent(other.parent), current_case(other.current_case),
			  sw(other.sw), vstate(other.vstate), entered(other.entered),
			  finished(other.finished)
		{
			branch_updates.swap(other.branch_updates);
			save_map.swap(other.save_map);
			other.entered = false;
			other.finished = false;
		}

		void enter_branch(std::vector<RTLIL::SigSpec> compare)
		{
			save_map.clear();
			vstate.save(save_map);
			log_assert(!entered);
			log_assert(current_case == parent);
			current_case = sw->add_case(compare);
			entered = true;
		}

		void exit_branch()
		{
			log_assert(entered);
			log_assert(current_case != parent);
			Case *this_case = current_case;
			current_case = parent;
			entered = false;
			auto updates = vstate.restore(save_map);
			branch_updates.push_back(std::make_tuple(this_case, updates.first, updates.second));
		}

		void branch(std::vector<RTLIL::SigSpec> compare,
					std::function<void()> f)
		{
			// TODO: extend detection
			if (compare.size() == 1 && compare[0].is_fully_def() &&
					sw->signal.is_fully_def() && sw->signal != compare[0]) {
				// dead branch
				return;
			}

			enter_branch(compare);
			f();
			exit_branch();
		}

		void finish(NetlistContext &netlist)
		{
			VariableBits updated_anybranch;
			for (auto &branch : branch_updates)
				updated_anybranch.append(std::get<1>(branch));
			updated_anybranch.sort_and_unify();

			// end-of-scope variables
			Yosys::pool<Variable> eos_variables;

			auto &va = vstate.visible_assignments;
			for (auto bit : updated_anybranch)
			if (bit.variable.kind != Variable::Static && !va.count(bit))
				eos_variables.insert(bit.variable);

			for (auto chunk : updated_anybranch.chunks()) {
				if (chunk.variable.kind != Variable::Static &&
						eos_variables.count(chunk.variable)) {
					for (int i = 0; i < chunk.bitwidth(); i++)
						log_assert(!va.count(chunk[i]));

					continue;
				}

				RTLIL::IdString new_id;
				if (auto symbol = chunk.variable.get_symbol())
					new_id = netlist.new_id(RTLIL::unescape_id(netlist.id(*symbol)) + chunk.slice_text());
				else
					new_id = netlist.new_id();

				RTLIL::SigSpec w_default = vstate.evaluate(netlist, chunk);
				RTLIL::Wire *w = netlist.canvas->addWire(new_id, chunk.bitwidth());
				if (sw->statement)
					transfer_attrs(*sw->statement, w);
				parent->aux_actions.push_back(RTLIL::SigSig(w, w_default));
				vstate.set(chunk, w);
			}

			for (auto &branch : branch_updates) {
				Case *rule;
				VariableBits target;
				RTLIL::SigSpec source;
				std::tie(rule, target, source) = branch;

				int done = 0;
				for (auto chunk : target.chunks()) {
					if (eos_variables.count(chunk.variable)) {
						done += chunk.bitwidth();
						continue;
					}

					// get the wire (or some part of it) which we created up above
					RTLIL::SigSpec target_w;
					for (int i = 0; i < chunk.bitwidth(); i++) {
						log_assert(va.count(chunk[i]));
						target_w.append(va.at(chunk[i]));
					}

					rule->aux_actions.push_back(RTLIL::SigSig(target_w,
						source.extract(done, chunk.bitwidth())));
					done += chunk.bitwidth();
				}
			}

			finished = true;
		}
	};

	void handle(const ast::ImmediateAssertionStatement &stmt)
	{
		if (netlist.settings.ignore_assertions.value_or(false))
			return;

		std::string flavor;
		switch (stmt.assertionKind) {
		case ast::AssertionKind::Assert:
			flavor = "assert";
			break;
		case ast::AssertionKind::Assume:
			flavor = "assume";
			break;
		case ast::AssertionKind::CoverProperty:
			flavor = "cover";
			break;
		default:
			netlist.add_diag(diag::AssertionUnsupported, stmt.sourceRange);
			return;
		}

		auto cell = netlist.canvas->addCell(netlist.new_id(), ID($check));
		context.set_effects_trigger(cell);
		cell->setParam(ID::FLAVOR, flavor);
		cell->setParam(ID::FORMAT, std::string(""));
		cell->setParam(ID::ARGS_WIDTH, 0);
		cell->setParam(ID::PRIORITY, --context.effects_priority);
		cell->setPort(ID::ARGS, {});
		cell->setPort(ID::A, netlist.ReduceBool(eval(stmt.cond)));
	}

	void handle(const ast::ConcurrentAssertionStatement &stmt) {
		if (!netlist.settings.ignore_assertions.value_or(false)) {
			netlist.add_diag(diag::SVAUnsupported, stmt.sourceRange);
		}
	}

	RTLIL::SigSpec handle_call(const ast::CallExpression &call)
	{
		RTLIL::SigSpec ret;

		require(call, !call.isSystemCall());
		auto subroutine = std::get<0>(call.subroutine);
		auto arg_symbols = subroutine->getArguments();

		std::vector<RTLIL::SigSpec> arg_in, arg_out;

		for (int i = 0; i < (int) arg_symbols.size(); i++) {
			const ast::Expression *arg = call.arguments()[i];
			auto dir = arg_symbols[i]->direction;

			if (dir == ast::ArgumentDirection::In || dir == ast::ArgumentDirection::InOut)
				arg_in.push_back(eval(*arg));
			else
				arg_in.push_back({});
		}

		slang::SourceLocation loc = call.sourceRange.start();

		{
			EnterAutomaticScopeGuard scope_guard(eval, subroutine);

			for (auto& member : subroutine->members())
			if (ast::VariableSymbol::isKind(member.kind)) {
				auto& var = member.as<ast::VariableSymbol>();

				if (var.kind == ast::SymbolKind::FormalArgument ||
						var.flags.has(ast::VariableFlags::CompilerGenerated))
					var.visit(*this);
			}

			for (int i = 0; i < (int) arg_symbols.size(); i++) {
				auto dir = arg_symbols[i]->direction;
				if (dir == ast::ArgumentDirection::In || dir == ast::ArgumentDirection::InOut)
					context.do_simple_assign(loc, eval.variable(*arg_symbols[i]), arg_in[i], true);
			}

			{
				RegisterEscapeConstructGuard escape_guard(context, EscapeConstructKind::FunctionBody,
														  subroutine);
				subroutine->getBody().visit(*this);
			}

			for (int i = 0; i < (int) arg_symbols.size(); i++) {
				auto dir = arg_symbols[i]->direction;
				if (dir == ast::ArgumentDirection::Out || dir == ast::ArgumentDirection::InOut)
					arg_out.push_back(eval(*arg_symbols[i]));
				else
					arg_out.push_back({});
			}

			if (subroutine->returnValVar)
				ret = eval(*subroutine->returnValVar);
		}

		for (int i = 0; i < (int) arg_symbols.size(); i++) {
			const ast::Expression *arg = call.arguments()[i];
			auto dir = arg_symbols[i]->direction;

			if (dir == ast::ArgumentDirection::Out || dir == ast::ArgumentDirection::InOut)
				context.assign_rvalue(arg->as<ast::AssignmentExpression>(), arg_out[i]);
		}

		return ret;
	}

	void handle_display(const ast::CallExpression &call)
	{
		auto cell = netlist.canvas->addCell(netlist.new_id(), ID($print));
		transfer_attrs(call, cell);
		context.set_effects_trigger(cell);
		cell->parameters[ID::PRIORITY] = --context.effects_priority;
		std::vector<Yosys::VerilogFmtArg> fmt_args;
		for (auto arg : call.arguments()) {
			log_assert(arg);
			Yosys::VerilogFmtArg fmt_arg = {};
			// TODO: location info in fmt_arg
			switch (arg->kind) {
			case ast::ExpressionKind::StringLiteral:
				fmt_arg.type = Yosys::VerilogFmtArg::STRING;
				fmt_arg.str = std::string{arg->as<ast::StringLiteral>().getValue()};
				fmt_arg.sig = {};
				break;
			case ast::ExpressionKind::Call:
				if (arg->as<ast::CallExpression>().getSubroutineName() == "$time") {
					fmt_arg.type = Yosys::VerilogFmtArg::TIME;
					break;
				} else if (arg->as<ast::CallExpression>().getSubroutineName() == "$realtime") {
					fmt_arg.type = Yosys::VerilogFmtArg::TIME;
					fmt_arg.realtime = true;
					break;
				} else {
					[[fallthrough]];
				}
			default:
				fmt_arg.type = Yosys::VerilogFmtArg::INTEGER;
				fmt_arg.sig = eval(*arg);
				fmt_arg.signed_ = arg->type->isSigned();
				break;
			}
			fmt_args.push_back(fmt_arg);

		}
		Yosys::Fmt fmt = {};
		// TODO: insert the actual module name
		fmt.parse_verilog(fmt_args, /* sformat_like */ false, /* default_base */ 10,
						  std::string{call.getSubroutineName()}, netlist.canvas->name);
		if (call.getSubroutineName() == "$display")
			fmt.append_literal("\n");
		fmt.emit_rtlil(cell);
	}

	void handle(const ast::ExpressionStatement &stmt)
	{
		eval(stmt.expr);
	}

	void handle(const ast::BlockStatement &blk)
	{
		require(blk, blk.blockKind == ast::StatementBlockKind::Sequential)
		EnterAutomaticScopeGuard guard(context.eval, blk.blockSymbol);
		blk.body.visit(*this);
	}

	void handle(const ast::StatementList &list)
	{
		Variable disable = context.get_disable_flag();

		std::vector<SwitchHelper> sw_stack;

		for (auto &stmt : list.list) {
			RTLIL::SigSpec disable_rv = disable ? context.substitute_rvalue(disable) : RTLIL::S0;
			if (!disable_rv.is_fully_const()) {
				auto &b = sw_stack.emplace_back(context.current_case, context.vstate, disable_rv);
				b.sw->statement = stmt;
				b.enter_branch({RTLIL::S0});
				context.current_case->statement = stmt;

				// From a semantical POV the following is a no-op, but it allows us to
				// do more constant folding.
				context.do_simple_assign(slang::SourceLocation::NoLocation, disable, RTLIL::S0, true);
			} else if (disable_rv.as_bool()) {
				break;
			} else {
				log_assert(!disable_rv.as_bool());
			}

			stmt->visit(*this);
		}

		for (auto it = sw_stack.rbegin(); it != sw_stack.rend(); it++) {
			it->exit_branch();
			it->finish(netlist);
		}
	}

	void handle(const ast::ConditionalStatement &cond)
	{
		require(cond, cond.conditions.size() == 1);
		require(cond, cond.conditions[0].pattern == NULL);

		RTLIL::SigSpec condition = netlist.ReduceBool(
			eval(*cond.conditions[0].expr)
		);
		SwitchHelper b(context.current_case, context.vstate, condition);
		b.sw->statement = &cond;

		b.branch({RTLIL::S1}, [&](){
			context.current_case->statement = &cond.ifTrue;
			cond.ifTrue.visit(*this);
		});

		if (cond.ifFalse) {
			b.branch({}, [&](){
				context.current_case->statement = &cond.ifTrue;
				cond.ifFalse->visit(*this);
			});
		}
		b.finish(netlist);

		// descend into an empty switch so we force action priority for follow-up statements
		context.current_case = context.current_case->add_switch({})->add_case({});
	}

	void handle(const ast::CaseStatement &stmt)
	{
		bool match_x, match_z;
		using Condition = ast::CaseStatementCondition;
		switch (stmt.condition) {
		case Condition::WildcardJustZ:
			match_x = false;
			match_z = true;
			break;
		case Condition::WildcardXOrZ:
			match_x = match_z = true;
			break;
		default:
			match_x = match_z = false;
			break;
		}

		RTLIL::SigSpec dispatch = eval(stmt.expr);
		SwitchHelper b(context.current_case, context.vstate,
					   stmt.condition == ast::CaseStatementCondition::Inside ?
					   RTLIL::SigSpec(RTLIL::S1) : dispatch);

		b.sw->statement = &stmt;
		switch (stmt.check) {
		case ast::UniquePriorityCheck::Priority:
			b.sw->full_case = true;
			break;
		case ast::UniquePriorityCheck::Unique:
			b.sw->full_case = true;
			b.sw->parallel_case = true;
			break;
		case ast::UniquePriorityCheck::Unique0:
			b.sw->parallel_case = true;
			break;
		case ast::UniquePriorityCheck::None:
			break;
		}

		for (auto item : stmt.items) {
			std::vector<RTLIL::SigSpec> compares;
			for (auto expr : item.expressions) {
				log_assert(expr);

				if (stmt.condition == ast::CaseStatementCondition::Inside) {
					require(stmt, stmt.expr.type->isIntegral());
					compares.push_back(inside_comparison(eval, dispatch, *expr));
					continue;
				}

				RTLIL::SigSpec compare = eval(*expr);
				log_assert(compare.size() == dispatch.size());
				require(stmt, !match_z || compare.is_fully_const());
				for (int i = 0; i < compare.size(); i++) {
					if (compare[i] == RTLIL::Sz && match_z)
						compare[i] = RTLIL::Sa;
					if (compare[i] == RTLIL::Sx && match_x)
						compare[i] = RTLIL::Sa;
				}
				compares.push_back(compare);
			}
			require(stmt, !compares.empty());
			b.branch(compares, [&]() {
				context.current_case->statement = item.stmt;
				item.stmt->visit(*this);
			});
		}

		if (stmt.defaultCase) {
			b.branch(std::vector<RTLIL::SigSpec>{}, [&]() {
				context.current_case->statement = stmt.defaultCase;
				stmt.defaultCase->visit(*this);
			});
		}
		b.finish(netlist);

		// descend into an empty switch so we force action priority for follow-up statements
		context.current_case = context.current_case->add_switch({})->add_case({});
	}

	RTLIL::Wire *add_nonstatic(RTLIL::IdString id, int width)
	{
		RTLIL::Wire *wire = netlist.canvas->addWire(id, width);
		wire->attributes[ID($nonstatic)] = context.current_case->level;
		return wire;
	}

	void handle(const ast::WhileLoopStatement &stmt) {
		RegisterEscapeConstructGuard guard1(context, EscapeConstructKind::Loop, &stmt);
		std::vector<SwitchHelper> sw_stack;
		unroll_limit.enter_unrolling();
		while (true) {
			RTLIL::SigSpec cv = netlist.ReduceBool(eval(stmt.cond));
			RTLIL::SigSpec break_rv = context.vstate.evaluate(netlist, guard1.flag);
			RTLIL::SigSpec joint_break = netlist.LogicOr(netlist.LogicNot(cv), break_rv);

			if (!joint_break.is_fully_const()) {
				auto &b = sw_stack.emplace_back(context.current_case, context.vstate, joint_break);
				b.sw->statement = &stmt;
				b.enter_branch({RTLIL::S0});
				context.current_case->statement = &stmt.body;

				// From a semantical POV the following is a no-op, but it allows us to
				// do more constant folding.
				context.do_simple_assign(slang::SourceLocation::NoLocation, guard1.flag, RTLIL::S0, true);
			} else if (joint_break.as_bool()) {
				break;
			} else {
				log_assert(!joint_break.as_bool());
			}

			{
				RegisterEscapeConstructGuard guard2(context, EscapeConstructKind::LoopBody, &stmt);
				stmt.body.visit(*this);
			}

			if (!unroll_limit.unroll_tick(&stmt))
				break;
		}
		unroll_limit.exit_unrolling();

		for (auto it = sw_stack.rbegin(); it != sw_stack.rend(); it++) {
			it->exit_branch();
			it->finish(netlist);
		}

		context.current_case = context.current_case->add_switch({})->add_case({});
	}

	void handle(const ast::ForLoopStatement &stmt) {
		for (auto init : stmt.initializers)
			eval(*init);

		if (!stmt.stopExpr) {
			netlist.add_diag(diag::MissingStopCondition, stmt.sourceRange.start());
			return;
		}

		RegisterEscapeConstructGuard guard1(context, EscapeConstructKind::Loop, &stmt);

		std::vector<SwitchHelper> sw_stack;
		unroll_limit.enter_unrolling();
		while (true) {
			RTLIL::SigSpec cv = netlist.ReduceBool(eval(*stmt.stopExpr));

			if (!cv.is_fully_const()) {
				auto &b = sw_stack.emplace_back(context.current_case, context.vstate, cv);
				b.sw->statement = &stmt;
				b.enter_branch({RTLIL::S1});
				context.current_case->statement = &stmt.body;
			} else if (!cv.as_bool()) {
				break;
			} else {
				log_assert(cv.as_bool());
			}

			{
				RegisterEscapeConstructGuard guard2(context, EscapeConstructKind::LoopBody, &stmt);
				stmt.body.visit(*this);
			}

			RTLIL::SigSpec break_rv = context.substitute_rvalue(guard1.flag);

			if (!break_rv.is_fully_const()) {
				auto &b = sw_stack.emplace_back(context.current_case, context.vstate, break_rv);
				b.sw->statement = &stmt;
				b.enter_branch({RTLIL::S0});
				context.current_case->statement = &stmt.body;
			} else if (break_rv.as_bool()) {
				break;
			} else {
				log_assert(!break_rv.as_bool());
			}

			for (auto step : stmt.steps)
				eval(*step);

			if (!unroll_limit.unroll_tick(&stmt))
				break;
		}
		unroll_limit.exit_unrolling();

		for (auto it = sw_stack.rbegin(); it != sw_stack.rend(); it++) {
			it->exit_branch();
			it->finish(netlist);
		}

		context.current_case = context.current_case->add_switch({})->add_case({});
	}

	void handle(const ast::EmptyStatement&) {}

	void init_nonstatic_variable(const ast::ValueSymbol &symbol) {
		Variable target = eval.variable(symbol);
		log_assert((bool) target);

		if (!target.bitwidth())
			return;

		RTLIL::SigSpec initval;
		if (symbol.getInitializer())
			initval = eval(*symbol.getInitializer());
		else
			initval = convert_const(symbol.getType().getDefaultValue());

		context.do_simple_assign(
			symbol.location,
			target,
			initval,
			true
		);
	}

	void handle(const ast::VariableSymbol &symbol) {
		if (symbol.lifetime != ast::VariableLifetime::Static) {
			init_nonstatic_variable(symbol);
		}
	}
	void handle(const ast::VariableDeclStatement &stmt) {
		stmt.symbol.visit(*this);
	}

	void handle(const ast::BreakStatement &brk)
	{
		context.signal_escape(brk.sourceRange.start(), EscapeConstructKind::Loop);
	}\

	void handle(const ast::ContinueStatement &brk)
	{
		context.signal_escape(brk.sourceRange.start(), EscapeConstructKind::LoopBody);
	}

	void handle(const ast::ReturnStatement &stmt)
	{
		auto subroutine = context.get_current_subroutine();
		log_assert(subroutine);

		if (stmt.expr) {
			ast_invariant(stmt, subroutine->subroutineKind == ast::SubroutineKind::Function);
			log_assert(subroutine->returnValVar);
			context.do_simple_assign(stmt.sourceRange.start(), eval.variable(*subroutine->returnValVar),
									 eval(*stmt.expr), true);
		}

		context.signal_escape(stmt.sourceRange.start(), EscapeConstructKind::FunctionBody);
	}

	void handle(const ast::TimedStatement &stmt)
	{
		if (!netlist.settings.ignore_timing.value_or(false))
			netlist.add_diag(diag::GenericTimingUnsyn, stmt.timing.sourceRange);

		stmt.stmt.visit(*this);
	}

	void handle(const ast::Statement &stmt)
	{
		netlist.add_diag(diag::LangFeatureUnsupported, stmt.sourceRange.start());
	}

	void handle(const ast::Expression &expr)
	{
		unimplemented(expr);
	}
};

int EvalContext::find_nest_level(const ast::Scope *scope)
{
	const ast::Scope *upper_scope = scope;

	while (upper_scope && !scope_nest_level.count(upper_scope))
		upper_scope = upper_scope->asSymbol().getParentScope();

	ast_invariant(scope->asSymbol(), upper_scope != nullptr);
	return scope_nest_level.at(upper_scope);
}

Variable EvalContext::variable(const ast::ValueSymbol &symbol)
{
	if (ast::VariableSymbol::isKind(symbol.kind) &&
			symbol.as<ast::VariableSymbol>().lifetime == ast::VariableLifetime::Automatic) {
		return Variable::from_symbol(&symbol, find_nest_level(symbol.getParentScope()));
	} else {
		return Variable::from_symbol(&symbol);
	}
}

VariableBits EvalContext::lhs(const ast::Expression &expr)
{
	ast_invariant(expr, expr.kind != ast::ExpressionKind::Streaming);
	VariableBits ret;

	if (!expr.type->isFixedSize()) {
		auto &diag = netlist.add_diag(diag::FixedSizeRequired, expr.sourceRange);
		diag << expr.type->toString();
		goto error;
	}

	switch (expr.kind) {
	case ast::ExpressionKind::NamedValue:
	case ast::ExpressionKind::HierarchicalValue: // TODO: raise error if there's a boundary
		{
			const ast::ValueSymbol &symbol = expr.as<ast::ValueExpressionBase>().symbol;
			if (netlist.is_inferred_memory(symbol)) {
				netlist.add_diag(diag::BadMemoryExpr, expr.sourceRange);
				goto error;
			}

			if (symbol.kind == ast::SymbolKind::ModportPort \
					&& !netlist.scopes_remap.count(symbol.getParentScope())) {
				ret = lhs(*symbol.as<ast::ModportPortSymbol>().getConnectionExpr());
				break;
			}

			ret = variable(symbol);
		}
		break;
	case ast::ExpressionKind::RangeSelect:
		{
			const ast::RangeSelectExpression &sel = expr.as<ast::RangeSelectExpression>();
			Addressing<VariableBits> addr(netlist.eval, sel);
			VariableBits inner = lhs(sel.value());
			ret = addr.extract(inner, sel.type->getBitstreamWidth());
		}
		break;
	case ast::ExpressionKind::Concatenation:
		{
			const ast::ConcatenationExpression &concat = expr.as<ast::ConcatenationExpression>();
			for (auto op : concat.operands())
				ret = {ret, lhs(*op)};
		}
		break;
	case ast::ExpressionKind::ElementSelect:
		{
			const ast::ElementSelectExpression &elemsel = expr.as<ast::ElementSelectExpression>();
			require(expr, elemsel.value().type->isBitstreamType() && elemsel.value().type->hasFixedRange());
			Addressing<VariableBits> addr(*this, elemsel);
			ret = addr.extract(lhs(elemsel.value()), elemsel.type->getBitstreamWidth());
		}
		break;
	case ast::ExpressionKind::MemberAccess:
		{
			const auto &acc = expr.as<ast::MemberAccessExpression>();
			require(expr, acc.member.kind == ast::SymbolKind::Field);
			const auto &member = acc.member.as<ast::FieldSymbol>();
			require(acc, member.randMode == ast::RandMode::None);
			return lhs(acc.value()).extract(member.bitOffset,
											expr.type->getBitstreamWidth());
		}
		break;
	case ast::ExpressionKind::Conversion:
		{
			const ast::ConversionExpression &conv = expr.as<ast::ConversionExpression>();
			if (conv.operand().kind != ast::ExpressionKind::Streaming) {
				const ast::Type &from = conv.operand().type->getCanonicalType();
				const ast::Type &to = conv.type->getCanonicalType();
				if (to.isBitstreamType() && from.isBitstreamType() &&
						from.getBitstreamWidth() == to.getBitstreamWidth()) {
					ret = lhs(conv.operand());
					break;
				}
			}
		}
		[[fallthrough]];
	default:
		netlist.add_diag(diag::UnsupportedLhs, expr.sourceRange);
		goto error;
	}

	if (0) {
	error:
		ret = Variable::dummy(expr.type->getBitstreamWidth());
	}

	log_assert(expr.type->isFixedSize());
	log_assert(ret.size() == (int) expr.type->getBitstreamWidth());
	return ret;
}

RTLIL::SigSpec EvalContext::connection_lhs(ast::AssignmentExpression const &assign)
{
	ast_invariant(assign, !assign.timingControl);
	const ast::Expression *rsymbol = &assign.right();

	if (rsymbol->kind == ast::ExpressionKind::EmptyArgument) {
		// early path
		VariableBits ret = lhs(assign.left());
		return netlist.convert_static(ret);
	}

	while (rsymbol->kind == ast::ExpressionKind::Conversion)
		rsymbol = &rsymbol->as<ast::ConversionExpression>().operand();
	ast_invariant(assign, rsymbol->kind == ast::ExpressionKind::EmptyArgument);
	ast_invariant(assign, rsymbol->type->isBitstreamType());

	RTLIL::SigSpec ret = netlist.canvas->addWire(netlist.new_id(), rsymbol->type->getBitstreamWidth());
	netlist.GroupConnect(
		netlist.convert_static(lhs(assign.left())),
		apply_nested_conversion(assign.right(), ret)
	);
	return ret;
}

RTLIL::SigSpec EvalContext::operator()(ast::Symbol const &symbol)
{
	switch (symbol.kind) {
	case ast::SymbolKind::ModportPort:
		{
			if (!netlist.scopes_remap.count(symbol.getParentScope()))
				return (*this)(*symbol.as<ast::ModportPortSymbol>().getConnectionExpr());
		}
		[[fallthrough]];
	case ast::SymbolKind::Net:
	case ast::SymbolKind::Variable:
	case ast::SymbolKind::FormalArgument:
		{
			log_assert(ast::ValueSymbol::isKind(symbol.kind));
			Variable var = variable(symbol.as<ast::ValueSymbol>());
			log_assert((bool) var);
			RTLIL::SigSpec value;
			if (procedural)
				value = procedural->substitute_rvalue(var);
			else
				value = netlist.convert_static(var);
			return value;
		}
		break;
	case ast::SymbolKind::Parameter:
		{
			auto &valsym = symbol.as<ast::ValueSymbol>();
			require(valsym, valsym.getInitializer());
			auto exprconst = valsym.getInitializer()->eval(this->const_);
			require(valsym, exprconst.isInteger());
			return convert_svint(exprconst.integer());
		}
		break;
	default:
		ast_unreachable(symbol);
	}
}

VariableBits EvalContext::streaming_lhs(ast::StreamingConcatenationExpression const &expr)
{
	require(expr, expr.isFixedSize());
	VariableBits cat;

	for (auto stream : expr.streams()) {
		require(*stream.operand, !stream.withExpr);
		auto& op = *stream.operand;
		VariableBits item;

		if (op.kind == ast::ExpressionKind::Streaming)
			item = streaming_lhs(op.as<ast::StreamingConcatenationExpression>());
		else
			item = lhs(*stream.operand);

		cat = {cat, item};
	}

	require(expr, expr.getSliceSize() <= std::numeric_limits<int>::max());
	int slice = expr.getSliceSize();
	if (slice == 0) {
		return cat;
	} else {
		VariableBits reorder;
		for (int i = 0; i < cat.size(); i += slice)
			reorder = {reorder, cat.extract(i, std::min(slice, cat.bitwidth() - i))};
		return reorder;
	}
}

RTLIL::SigSpec EvalContext::streaming(ast::StreamingConcatenationExpression const &expr)
{
	require(expr, expr.isFixedSize());
	RTLIL::SigSpec cat;

	for (auto stream : expr.streams()) {
		require(*stream.operand, !stream.withExpr);
		auto& op = *stream.operand;
		RTLIL::SigSpec item;

		if (op.kind == ast::ExpressionKind::Streaming)
			item = streaming(op.as<ast::StreamingConcatenationExpression>());
		else
			item = (*this)(*stream.operand);

		cat = {cat, item};
	}

	require(expr, expr.getSliceSize() <= std::numeric_limits<int>::max());
	int slice = expr.getSliceSize();
	if (slice == 0) {
		return cat;
	} else {
		RTLIL::SigSpec reorder;
		for (int i = 0; i < cat.size(); i += slice)
			reorder = {reorder, cat.extract(i, std::min(slice, cat.size() - i))};
		return reorder;
	}
}

RTLIL::SigSpec EvalContext::apply_conversion(const ast::ConversionExpression &conv, RTLIL::SigSpec op)
{
	const ast::Type &from = conv.operand().type->getCanonicalType();
	const ast::Type &to = conv.type->getCanonicalType();

	log_assert(op.size() == (int) from.getBitstreamWidth());

	if (from.isIntegral() && to.isIntegral()) {
		op.extend_u0((int) to.getBitWidth(), to.isSigned());
		return op;
	} else if (from.isBitstreamType() && to.isBitstreamType()) {
		require(conv, from.getBitstreamWidth() == to.getBitstreamWidth());
		return op;
	} else {
		unimplemented(conv);
	}
}

RTLIL::SigSpec EvalContext::apply_nested_conversion(const ast::Expression &expr, RTLIL::SigSpec op)
{
	if (expr.kind == ast::ExpressionKind::EmptyArgument) {
		return op;
	} else if (expr.kind == ast::ExpressionKind::Conversion) {
		auto &conv = expr.as<ast::ConversionExpression>();
		RTLIL::SigSpec value = apply_nested_conversion(conv.operand(), op);
		return apply_conversion(conv, value);
	} else {
		log_abort();
	}
}

RTLIL::SigSpec EvalContext::operator()(ast::Expression const &expr)
{
	RTLIL::Module *mod = netlist.canvas;
	RTLIL::SigSpec ret;
	size_t repl_count;

	// TODO: Interconnect (untyped) is unimplemented, waiting on slang width resolution
	if (expr.type->isUntypedType())
		unimplemented(expr);

	ast_invariant(expr, expr.kind != ast::ExpressionKind::Streaming);
	if (!(expr.type->isFixedSize() || expr.type->isVoid())) {
		auto &diag = netlist.add_diag(diag::FixedSizeRequired, expr.sourceRange);
		diag << expr.type->toString();
		goto error;
	}

	if (/* flag for testing */ !ignore_ast_constants ||
			expr.kind == ast::ExpressionKind::IntegerLiteral ||
			expr.kind == ast::ExpressionKind::RealLiteral ||
			expr.kind == ast::ExpressionKind::UnbasedUnsizedIntegerLiteral ||
			expr.kind == ast::ExpressionKind::NullLiteral ||
			expr.kind == ast::ExpressionKind::StringLiteral) {
		auto const_result = expr.eval(this->const_);
		if (const_result) {
			ret = convert_const(const_result);
			goto done;
		}
	}

	switch (expr.kind) {
	case ast::ExpressionKind::Assignment:
		{
			auto &assign = expr.as<ast::AssignmentExpression>();
			ast_invariant(expr, procedural != nullptr);

			if (assign.timingControl && !netlist.settings.ignore_timing.value_or(false))
				netlist.add_diag(diag::GenericTimingUnsyn, assign.timingControl->sourceRange);

			const ast::Expression *lvalue_save = lvalue;
			lvalue = &assign.left();
			procedural->assign_rvalue(assign, ret = (*this)(assign.right()));

			// TODO: this is a fixup for a specific scenario, we need to
			// check if there isn't some other general handling of return
			// values we should be doing
			if (assign.left().kind == ast::ExpressionKind::Streaming)
				ret = {};

			lvalue = lvalue_save;
			break;
		}
	case ast::ExpressionKind::Inside:
		{
			auto &inside_expr = expr.as<ast::InsideExpression>();
			RTLIL::SigSpec left = (*this)(inside_expr.left());
			RTLIL::SigSpec hits;
			require(inside_expr, inside_expr.left().type->isIntegral());

			for (auto elem : inside_expr.rangeList())
				hits.append(inside_comparison(*this, left, *elem));

			ret = netlist.ReduceBool(hits);
			ret.extend_u0(expr.type->getBitstreamWidth());
			break;
		}
	case ast::ExpressionKind::NamedValue:
	case ast::ExpressionKind::HierarchicalValue:
		{
			const ast::Symbol &symbol = expr.as<ast::ValueExpressionBase>().symbol;
			if (netlist.is_inferred_memory(symbol)) {
				netlist.add_diag(diag::BadMemoryExpr, expr.sourceRange);
				goto error;
			}

			ret = (*this)(symbol);
		}
		break;
	case ast::ExpressionKind::UnaryOp:
		{
			const ast::UnaryExpression &unop = expr.as<ast::UnaryExpression>();
			RTLIL::SigSpec left = (*this)(unop.operand());

			using UnOp = ast::UnaryOperator;

			if (unop.op == UnOp::Postincrement || unop.op == UnOp::Preincrement) {
				require(expr, procedural != nullptr);
				RTLIL::SigSpec add1 = netlist.Biop(
						ID($add), left, {RTLIL::S0, RTLIL::S1},
						unop.operand().type->isSigned(), unop.operand().type->isSigned(),
						left.size());
				procedural->do_simple_assign(expr.sourceRange.start(),
											 lhs(unop.operand()), add1, true);
				ret = (unop.op == UnOp::Preincrement) ? add1 : left;
				break;
			}

			if (unop.op == UnOp::Postdecrement || unop.op == UnOp::Predecrement) {
				require(expr, procedural != nullptr);
				RTLIL::SigSpec sub1 = netlist.Biop(
						ID($sub), left, {RTLIL::S0, RTLIL::S1},
						unop.operand().type->isSigned(), unop.operand().type->isSigned(),
						left.size());
				procedural->do_simple_assign(expr.sourceRange.start(),
											 lhs(unop.operand()), sub1, true);
				ret = (unop.op == UnOp::Predecrement) ? sub1 : left;
				break;
			}

			bool invert = false;

			RTLIL::IdString type;
			switch (unop.op) {
			case UnOp::Minus: type = ID($neg); break;
			case UnOp::Plus: type = ID($pos); break;
			case UnOp::LogicalNot: type = ID($logic_not); break;
			case UnOp::BitwiseNot: type = ID($not); break;
			case UnOp::BitwiseOr: type = ID($reduce_or); break;
			case UnOp::BitwiseAnd: type = ID($reduce_and); break;
			case UnOp::BitwiseNand: type = ID($reduce_and); invert = true; break;
			case UnOp::BitwiseNor: type = ID($reduce_or); invert = true; break;
			case UnOp::BitwiseXor: type = ID($reduce_xor); break;
			case UnOp::BitwiseXnor: type = ID($reduce_xnor); break;
			default:
				ast_unreachable(unop);
			}

			ret = netlist.Unop(
				type, left, unop.operand().type->isSigned(), expr.type->getBitstreamWidth()
			);

			if (invert)
				ret = netlist.LogicNot(ret);
		}
		break;
	case ast::ExpressionKind::BinaryOp:
		{
			const ast::BinaryExpression &biop = expr.as<ast::BinaryExpression>();
			RTLIL::SigSpec left = (*this)(biop.left());
			RTLIL::SigSpec right = (*this)(biop.right());

			bool invert;
			switch (biop.op) {
			case ast::BinaryOperator::WildcardEquality:
				invert = false;
				if (0) {
			case ast::BinaryOperator::WildcardInequality:
				invert = true;
				}
				if (!right.is_fully_const()) {
					netlist.add_diag(diag::NonconstWildcardEq, expr.sourceRange);
					ret = netlist.canvas->addWire(netlist.new_id(), expr.type->getBitstreamWidth());
					return ret;
				}
				return netlist.Unop(
					invert ? ID($logic_not) : ID($reduce_bool),
					netlist.EqWildcard(left, right),
					false, expr.type->getBitstreamWidth()
				);
			default:
				break;
			}

			bool a_signed = biop.left().type->isSigned();
			bool b_signed = biop.right().type->isSigned();

			RTLIL::IdString type;
			switch (biop.op) {
			case ast::BinaryOperator::Add:      type = ID($add); break;
			case ast::BinaryOperator::Subtract: type = ID($sub); break;
			case ast::BinaryOperator::Multiply:	type = ID($mul); break;
			case ast::BinaryOperator::Divide:	type = ID($div); break;
			case ast::BinaryOperator::Mod:		type = ID($mod); break;
			case ast::BinaryOperator::BinaryAnd: type = ID($and); break;
			case ast::BinaryOperator::BinaryOr:	type = ID($or); break;
			case ast::BinaryOperator::BinaryXor:	type = ID($xor); break;
			case ast::BinaryOperator::BinaryXnor:	type = ID($xnor); break;
			case ast::BinaryOperator::Equality:		type = ID($eq); break;
			case ast::BinaryOperator::Inequality:	type = ID($ne); break;
			case ast::BinaryOperator::CaseInequality: type = ID($nex); break;
			case ast::BinaryOperator::CaseEquality: type = ID($eqx); break;
			case ast::BinaryOperator::GreaterThanEqual:	type = ID($ge); break;
			case ast::BinaryOperator::GreaterThan:		type = ID($gt); break;
			case ast::BinaryOperator::LessThanEqual:	type = ID($le); break;
			case ast::BinaryOperator::LessThan:			type = ID($lt); break;
			case ast::BinaryOperator::LogicalAnd:	type = ID($logic_and); break;
			case ast::BinaryOperator::LogicalOr:	type = ID($logic_or); break;
			case ast::BinaryOperator::LogicalImplication: type = ID($logic_or); left = netlist.LogicNot(left); a_signed = false; break;
			case ast::BinaryOperator::LogicalEquivalence: type = ID($eq); left = netlist.ReduceBool(left); right = netlist.ReduceBool(right); a_signed = b_signed = false; break;
			case ast::BinaryOperator::LogicalShiftLeft:	type = ID($shl); break;
			case ast::BinaryOperator::LogicalShiftRight:	type = ID($shr); break;
			case ast::BinaryOperator::ArithmeticShiftLeft:	type = ID($sshl); break;
			case ast::BinaryOperator::ArithmeticShiftRight:	type = ID($sshr); break;
			case ast::BinaryOperator::Power:	type = ID($pow); break;
			default:
				ast_unreachable(biop);
			}

			// fixups
			if (type.in(ID($shr), ID($shl)))
				a_signed = false;
			if (type.in(ID($shr), ID($shl), ID($sshr), ID($sshl)))
				b_signed = false;

			ret = netlist.Biop(
				type, left, right,
				a_signed, b_signed, expr.type->getBitstreamWidth()
			);
		}
		break;
	case ast::ExpressionKind::Conversion:
		{
			const ast::ConversionExpression &conv = expr.as<ast::ConversionExpression>();
			if (conv.operand().kind != ast::ExpressionKind::Streaming) {
				ret = apply_conversion(conv, (*this)(conv.operand()));
			} else {
				const ast::Type &to = conv.type->getCanonicalType();
				ast_invariant(conv, to.isBitstreamType());

				// evaluate the bitstream
				auto &stream_expr = conv.operand().as<ast::StreamingConcatenationExpression>();
				RTLIL::SigSpec stream = streaming(stream_expr);

				// pad to fit target size
				ast_invariant(conv, stream.size() <= (int) expr.type->getBitstreamWidth());
				ret = {stream, RTLIL::SigSpec(RTLIL::S0, expr.type->getBitstreamWidth() - stream.size())};
			}
		}
		break;
	case ast::ExpressionKind::IntegerLiteral:
		{
			const ast::IntegerLiteral &lit = expr.as<ast::IntegerLiteral>();
			ret = convert_svint(lit.getValue());
		}
		break;
	case ast::ExpressionKind::RangeSelect:
		{
			const ast::RangeSelectExpression &sel = expr.as<ast::RangeSelectExpression>();
			Addressing<RTLIL::SigSpec> addr(*this, sel);
			ret = addr.shift_down((*this)(sel.value()), sel.type->getBitstreamWidth());
		}
		break;
	case ast::ExpressionKind::ElementSelect:
		{
			const ast::ElementSelectExpression &elemsel = expr.as<ast::ElementSelectExpression>();

			if (netlist.is_inferred_memory(elemsel.value())) {
				int width = elemsel.type->getBitstreamWidth();
				RTLIL::IdString id = netlist.id(elemsel.value()
										.as<ast::NamedValueExpression>().symbol);
				RTLIL::Cell *memrd = netlist.canvas->addCell(netlist.new_id(), ID($memrd_v2));
				memrd->setParam(ID::MEMID, id.str());
				memrd->setParam(ID::CLK_ENABLE, false);
				memrd->setParam(ID::CLK_POLARITY, false);
				memrd->setParam(ID::TRANSPARENCY_MASK, RTLIL::Const(0, 0));
				memrd->setParam(ID::COLLISION_X_MASK, RTLIL::Const(0, 0));
				memrd->setParam(ID::CE_OVER_SRST, false);
				memrd->setParam(ID::ARST_VALUE, RTLIL::Const(RTLIL::Sx, width));
				memrd->setParam(ID::SRST_VALUE, RTLIL::Const(RTLIL::Sx, width));
				memrd->setParam(ID::INIT_VALUE, RTLIL::Const(RTLIL::Sx, width));
				memrd->setPort(ID::CLK, RTLIL::Sx);
				memrd->setPort(ID::EN, RTLIL::S1);
				memrd->setPort(ID::ARST, RTLIL::S0);
				memrd->setPort(ID::SRST, RTLIL::S0);
				// TODO: signedness
				RTLIL::SigSpec addr = (*this)(elemsel.selector());
				memrd->setPort(ID::ADDR, addr);
				memrd->setParam(ID::ABITS, addr.size());
				ret = netlist.canvas->addWire(netlist.new_id(), width);
				memrd->setPort(ID::DATA, ret);
				memrd->setParam(ID::WIDTH, width);
				transfer_attrs(expr, memrd);
				break;
			}

			Addressing<RTLIL::SigSpec> addr(*this, elemsel);
			ret = addr.mux((*this)(elemsel.value()), elemsel.type->getBitstreamWidth());
		}
		break;
	case ast::ExpressionKind::Concatenation:
		{
			const ast::ConcatenationExpression &concat = expr.as<ast::ConcatenationExpression>();
			for (auto op : concat.operands())
				ret = {ret, (*this)(*op)};
		}
		break;
	case ast::ExpressionKind::SimpleAssignmentPattern:
	case ast::ExpressionKind::StructuredAssignmentPattern:
		{
			repl_count = 1;

			if (0) {
	case ast::ExpressionKind::ReplicatedAssignmentPattern:
				repl_count = *expr.as<ast::ReplicatedAssignmentPatternExpression>()
								.count().eval(const_).integer().as<size_t>();
			}

			auto &pattern_expr = static_cast<const ast::AssignmentPatternExpressionBase&>(expr);

			ret = {};
			for (auto elem : pattern_expr.elements())
				ret = {ret, (*this)(*elem)};
			ret = ret.repeat(repl_count);
		}
		break;
	case ast::ExpressionKind::ConditionalOp:
		{
			const auto &ternary = expr.as<ast::ConditionalExpression>();

			require(expr, ternary.conditions.size() == 1);
			require(expr, !ternary.conditions[0].pattern);

			ret = netlist.Mux(
				(*this)(ternary.right()),
				(*this)(ternary.left()),
				netlist.ReduceBool((*this)(*(ternary.conditions[0].expr)))
			);
		}
		break;
	case ast::ExpressionKind::Replication:
		{
			const auto &repl = expr.as<ast::ReplicationExpression>();
			auto count = repl.count().eval(const_);
			ast_invariant(expr, count.isInteger());
			int reps = count.integer().as<int>().value(); // TODO: checking int cast
			RTLIL::SigSpec concat = (*this)(repl.concat());
			for (int i = 0; i < reps; i++)
				ret.append(concat);
		}
		break;
	case ast::ExpressionKind::MemberAccess:
		{
			const auto &acc = expr.as<ast::MemberAccessExpression>();
			require(expr, acc.member.kind == ast::SymbolKind::Field);
			const auto &member = acc.member.as<ast::FieldSymbol>();
			require(acc, member.randMode == ast::RandMode::None);
			return (*this)(acc.value()).extract(member.bitOffset,
								expr.type->getBitstreamWidth());
		}
		break;
	case ast::ExpressionKind::Call:
		{
			const auto &call = expr.as<ast::CallExpression>();
			if (call.isSystemCall() && (call.getSubroutineName() == "$display"
					|| call.getSubroutineName() == "$write")) {
				require(expr, procedural != nullptr);
				StatementVisitor(*procedural).handle_display(call);
			} else if (call.isSystemCall()) {
				require(expr, call.getSubroutineName() == "$signed" || call.getSubroutineName() == "$unsigned");
				require(expr, call.arguments().size() == 1);
				ret = (*this)(*call.arguments()[0]);
			} else {
				const auto &subr = *std::get<0>(call.subroutine);
				if (procedural) {
					ret = StatementVisitor(*procedural).handle_call(call);
				} else {
					require(subr, subr.subroutineKind == ast::SubroutineKind::Function);
					ProcessTiming implicit;
					ProceduralContext context(netlist, implicit);
					StatementVisitor visitor(context);
					visitor.eval.ignore_ast_constants = ignore_ast_constants;
					ret = visitor.handle_call(call);

					RTLIL::Process *proc = netlist.canvas->addProcess(netlist.new_id());
					transfer_attrs(call, proc);
					context.root_case->copy_into(&proc->root_case);
				}
			}
		}
		break;
	case ast::ExpressionKind::LValueReference:
		ast_invariant(expr, lvalue != nullptr);
		ret = (*this)(*lvalue);
		break;
	default:
		netlist.add_diag(diag::LangFeatureUnsupported, expr.sourceRange);
		goto error;
	}

	if (0) {
error:
	ret = RTLIL::SigSpec(RTLIL::Sx, (int) expr.type->getBitstreamWidth());
	}

done:
	ast_invariant(expr, ret.size() == (int) expr.type->getBitstreamWidth());
	return ret;
}

RTLIL::SigSpec EvalContext::eval_signed(ast::Expression const &expr)
{
	log_assert(expr.type);

	if (expr.type->isNumeric() && !expr.type->isSigned())
		return {RTLIL::S0, (*this)(expr)};
	else
		return (*this)(expr);
}

EvalContext::EvalContext(NetlistContext &netlist)
	: netlist(netlist), procedural(nullptr),
	  const_(ast::ASTContext(netlist.compilation.getRoot(), ast::LookupLocation::max))
{
}

EvalContext::EvalContext(NetlistContext &netlist, ProceduralContext &procedural)
	: netlist(netlist), procedural(&procedural),
	  const_(ast::ASTContext(netlist.compilation.getRoot(), ast::LookupLocation::max))
{
}

struct HierarchyQueue {
	template<class... Args>
	std::pair<NetlistContext&, bool> get_or_emplace(const ast::InstanceBodySymbol *symbol, Args&&... args)
	{
		if (netlists.count(symbol)) {
			return {*netlists.at(symbol), false};
		} else {
			NetlistContext *ref = new NetlistContext(args...);
			netlists[symbol] = ref;
			queue.push_back(ref);
			return {*ref, true};
		}
	}

	~HierarchyQueue()
	{
		for (auto netlist : queue)
			delete netlist;
	}

	std::map<const ast::InstanceBodySymbol *, NetlistContext *> netlists;
	std::vector<NetlistContext *> queue;
};

struct PopulateNetlist : public TimingPatternInterpretor, public ast::ASTVisitor<PopulateNetlist, true, false> {
public:
	HierarchyQueue &queue;
	NetlistContext &netlist;
	SynthesisSettings &settings;
	InferredMemoryDetector mem_detect;
	std::vector<NetlistContext> deferred_modules;

	struct InitialEvalVisitor : SlangInitial::EvalVisitor {
		NetlistContext &netlist;
		RTLIL::Module *mod;
		int print_priority;

		InitialEvalVisitor(NetlistContext &netlist, ast::Compilation *compilation,
						   RTLIL::Module *mod, bool ignore_timing=false)
			: SlangInitial::EvalVisitor(compilation, ignore_timing), netlist(netlist), mod(mod), print_priority(0) {}

		void handleDisplay(const slang::ast::CallExpression &call, const std::vector<slang::ConstantValue> &args) {
			auto cell = mod->addCell(netlist.new_id(), ID($print));
			cell->parameters[ID::TRG_ENABLE] = true;
			cell->parameters[ID::TRG_WIDTH] = 0;
			cell->parameters[ID::TRG_POLARITY] = {};
			cell->parameters[ID::PRIORITY] = print_priority--;
			cell->setPort(ID::EN, RTLIL::S1);
			cell->setPort(ID::TRG, {});
			std::vector<Yosys::VerilogFmtArg> fmt_args;
			for (int i = 0; i < (int) call.arguments().size(); i++) {
				const ast::Expression *arg_expr = call.arguments()[i];
				const auto &arg = args[i];
				Yosys::VerilogFmtArg fmt_arg = {};
				// TODO: location info in fmt_arg
				if (arg_expr->kind == ast::ExpressionKind::StringLiteral) {
					fmt_arg.type = Yosys::VerilogFmtArg::STRING;
					fmt_arg.str = std::string{arg_expr->as<ast::StringLiteral>().getValue()};
					fmt_arg.sig = RTLIL::Const(fmt_arg.str);
				} else if (arg.isString()) {
					fmt_arg.type = Yosys::VerilogFmtArg::STRING;
					fmt_arg.str = arg.str();
					fmt_arg.sig = RTLIL::Const(fmt_arg.str);
				} else if (arg.isInteger()) {
					fmt_arg.type = Yosys::VerilogFmtArg::INTEGER;
					fmt_arg.sig = convert_svint(arg.integer());
					fmt_arg.signed_ = arg.integer().isSigned();
				} else {
					auto &diag = netlist.add_diag(diag::ArgumentTypeUnsupported, call.sourceRange);
					diag << arg_expr->type->toString();
					mod->remove(cell);
					return;
				}
				fmt_args.push_back(fmt_arg);
			}
			Yosys::Fmt fmt = {};
			// TODO: default_base is subroutine dependent, final newline is $display-only
			// TODO: calls aborts
			fmt.parse_verilog(fmt_args, /* sformat_like */ false, /* default_base */ 10,
							  std::string{call.getSubroutineName()}, mod->name);
			fmt.append_literal("\n");
			fmt.emit_rtlil(cell);
			transfer_attrs(call, cell);
		}
	} initial_eval;

	PopulateNetlist(HierarchyQueue &queue, NetlistContext &netlist)
		: TimingPatternInterpretor(netlist.settings, (DiagnosticIssuer&) netlist),
		  queue(queue), netlist(netlist), settings(netlist.settings),
		  mem_detect(settings, std::bind(&PopulateNetlist::should_dissolve, this, std::placeholders::_1)),
		  initial_eval(netlist, &netlist.compilation, netlist.canvas,
					   netlist.settings.ignore_timing.value_or(false)) {}

	void handle_comb_like_process(const ast::ProceduralBlockSymbol &symbol, const ast::Statement &body)
	{
		RTLIL::Process *proc = netlist.canvas->addProcess(netlist.new_id());
		transfer_attrs(body, proc);

		ProcessTiming implicit_timing;

		ProceduralContext procedure(netlist, implicit_timing);
		body.visit(StatementVisitor(procedure));

		VariableBits all_driven = procedure.all_driven();
		Yosys::pool<VariableBit> dangling;
		if (symbol.procedureKind != ast::ProceduralBlockKind::AlwaysComb) {
			Yosys::pool<VariableBit> driven_pool = {all_driven.begin(), all_driven.end()};
			dangling =
				detect_possibly_unassigned_subset(driven_pool, procedure.root_case);
		}

		// left-hand side and right-hand side of the connections to be made
		RTLIL::SigSpec cl, cr;
		VariableBits latch_driven;

		for (auto driven_bit : all_driven) {
			if (!dangling.count(driven_bit)) {
				// No latch inferred
				cl.append(netlist.convert_static(driven_bit));
				cr.append(procedure.vstate.visible_assignments.at(driven_bit));
			} else {
				latch_driven.append(driven_bit);
			}
		}

		if (symbol.procedureKind == ast::ProceduralBlockKind::AlwaysLatch && !cl.empty()) {
			for (auto chunk : cl.chunks()) {
				auto &diag = netlist.add_diag(diag::LatchNotInferred, symbol.location);
				diag << std::string(log_signal(chunk));
			}
		}

		if (!latch_driven.empty()) {
			// map from a driven signal to the corresponding enable/staging signal
			// TODO: SigSig needlessly costly here
			Yosys::dict<VariableBit, RTLIL::SigSig> signaling;
			RTLIL::SigSpec enables;

			for (auto bit : latch_driven) {
				// TODO: create latches in groups
				RTLIL::SigBit en = netlist.canvas->addWire(netlist.new_id(), 1);
				RTLIL::SigBit staging = netlist.canvas->addWire(netlist.new_id(), 1);
				RTLIL::Cell *cell = netlist.canvas->addDlatch(netlist.new_id(), en,
														staging, netlist.convert_static(bit), true);
				signaling[bit] = {en, staging};
				enables.append(en);
				transfer_attrs(symbol, cell);
			}

			procedure.root_case->aux_actions.push_back(
						{enables, RTLIL::SigSpec(RTLIL::S0, enables.size())});
			procedure.root_case->insert_latch_signaling(netlist, signaling);
		}

		procedure.root_case->copy_into(&proc->root_case);
		netlist.GroupConnect(cl, cr);
	}

	void handle_ff_process(const ast::ProceduralBlockSymbol &symbol,
						   const ast::SignalEventControl &clock,
						   const ast::StatementBlockSymbol *prologue_block,
						   std::vector<const ast::Statement *> prologue_statements,
						   const ast::Statement &sync_body,
						   std::span<AsyncBranch> async)
	{
		log_assert(symbol.getBody().kind == ast::StatementKind::Timed);
		const auto &timed = symbol.getBody().as<ast::TimedStatement>();

		RTLIL::Process *proc = netlist.canvas->addProcess(netlist.new_id());
		transfer_attrs(timed.stmt, proc);

		ProcessTiming prologue_timing;
		{
			prologue_timing.triggers.push_back({netlist.eval(clock.expr), clock.edge == ast::EdgeKind::PosEdge, &clock});
			for (auto &abranch : async)	{
				RTLIL::SigSpec sig = netlist.eval(abranch.trigger);
				log_assert(sig.size() == 1);
				prologue_timing.triggers.push_back({sig, abranch.polarity, nullptr});
			}
		}
		ProceduralContext prologue(netlist, prologue_timing);
		EnterAutomaticScopeGuard prologue_guard(prologue.eval, prologue_block);
		{
			StatementVisitor visitor(prologue);
			for (auto stmt : prologue_statements)
				stmt->visit(visitor);
		}
		prologue.copy_case_tree_into(proc->root_case);

		struct Aload {
			RTLIL::SigBit trigger;
			bool trigger_polarity;
			VariableState values;
			const ast::Statement *ast_node;
		};
		std::vector<Aload> aloads;
		RTLIL::SigSpec prior_branch_taken;

		for (auto &async_branch : async) {
			RTLIL::SigSpec sig = netlist.eval(async_branch.trigger);
			log_assert(sig.size() == 1);

			ProcessTiming branch_timing;
			RTLIL::SigSpec sig_depol = async_branch.polarity ? sig : netlist.LogicNot(sig);
			branch_timing.background_enable = netlist.LogicAnd(netlist.LogicNot(prior_branch_taken), sig_depol);
			prior_branch_taken.append(sig_depol);

			ProceduralContext branch(netlist, branch_timing);
			EnterAutomaticScopeGuard branch_guard(branch.eval, prologue_block);

			branch.inherit_state(prologue);
			async_branch.body.visit(StatementVisitor(branch));
			branch.copy_case_tree_into(proc->root_case);
			aloads.push_back({
				sig, async_branch.polarity, branch.vstate, &async_branch.body
			});
			// TODO: check for non-constant load values and warn about sim/synth mismatch
		}

		if (aloads.size() > 1) {
			netlist.add_diag(diag::AloadOne, timed.timing.sourceRange);
			return;
		}

		{
			ProcessTiming timing;
			timing.background_enable = netlist.LogicNot(prior_branch_taken);
			timing.triggers.push_back({netlist.eval(clock.expr), clock.edge == ast::EdgeKind::PosEdge, &clock});

			ProceduralContext sync_procedure(netlist, timing);
			EnterAutomaticScopeGuard guard(sync_procedure.eval, prologue_block);
			sync_procedure.inherit_state(prologue);
			sync_body.visit(StatementVisitor(sync_procedure));
			sync_procedure.copy_case_tree_into(proc->root_case);

			// FIXME: ignores variables not driven from the sync procedure
			VariableBits driven = sync_procedure.all_driven();
			for (VariableChunk driven_chunk : driven.chunks()) {
				const ast::Type *type = &driven_chunk.variable.get_symbol()->getType();
				RTLIL::SigSpec assigned = sync_procedure.vstate.evaluate(netlist, driven_chunk);

				RTLIL::Cell *cell;
				if (aloads.empty()) {
					for (auto [named_chunk, name] : generate_subfield_names(driven_chunk, type)) {
						cell = netlist.canvas->addDff(netlist.canvas->uniquify("$driver$" + RTLIL::unescape_id(netlist.id(*named_chunk.variable.get_symbol())) + name),
												timing.triggers[0].signal,
												assigned.extract(named_chunk.base - driven_chunk.base, named_chunk.bitwidth()),
												netlist.convert_static(named_chunk),
												timing.triggers[0].edge_polarity);
						transfer_attrs(symbol, cell);
					}
				} else if (aloads.size() == 1) {
					VariableBits aldff_q;
					VariableBits dffe_q; // fallback

					for (int i = 0; i < driven_chunk.bitwidth(); i++) {
						// Is this variable bit assigned to from the async branch?
						// Depending on this we either use $aldff or $dffe to drive it
						if (aloads[0].values.visible_assignments.count(driven_chunk[i]))
							aldff_q.append(driven_chunk[i]);
						else
							dffe_q.append(driven_chunk[i]);
					}

					if (!aldff_q.empty()) {
						for (auto driven_chunk2 : aldff_q.chunks())
						for (auto [named_chunk, name] : generate_subfield_names(driven_chunk2, type)) {
							cell = netlist.canvas->addAldff(netlist.canvas->uniquify("$driver$" + RTLIL::unescape_id(netlist.id(*named_chunk.variable.get_symbol())) + name),
													timing.triggers[0].signal,
													aloads[0].trigger,
													assigned.extract(named_chunk.base - driven_chunk.base, named_chunk.bitwidth()),
													netlist.convert_static(named_chunk),
													aloads[0].values.evaluate(netlist, named_chunk),
													timing.triggers[0].edge_polarity,
													aloads[0].trigger_polarity);
							transfer_attrs(symbol, cell);
						}
					}

					if (!dffe_q.empty()) {
						for (auto driven_chunk2 : dffe_q.chunks()) {
							auto &diag = netlist.add_diag(diag::MissingAload, aloads[0].ast_node->sourceRange);
							diag << netlist.id(*driven_chunk2.variable.get_symbol()).str() + driven_chunk2.slice_text();
							diag.addNote(diag::NoteDuplicateEdgeSense, timed.timing.sourceRange);
						}

						for (auto driven_chunk2 : dffe_q.chunks())
						for (auto [named_chunk, name] : generate_subfield_names(driven_chunk2, type)) {
							cell = netlist.canvas->addDffe(netlist.canvas->uniquify("$driver$" + RTLIL::unescape_id(netlist.id(*named_chunk.variable.get_symbol())) + name),
													timing.triggers[0].signal,
													aloads[0].trigger,
													assigned.extract(named_chunk.base - driven_chunk.base, named_chunk.bitwidth()),
													netlist.convert_static(named_chunk),
													timing.triggers[0].edge_polarity,
													!aloads[0].trigger_polarity);
							transfer_attrs(symbol, cell);
						}
					}
				} else {
					log_abort();
				}
			}
		}
	}

	void handle_initial_process(const ast::ProceduralBlockSymbol &, const ast::Statement &body) {
		if (settings.ignore_initial.value_or(false))
			return;

		auto result = body.visit(initial_eval);
		if (result != ast::Statement::EvalResult::Success)
			initial_eval.context.addDiag(diag::NoteIgnoreInitial,
										 slang::SourceLocation::NoLocation);
	}

	void handle(const ast::ProceduralBlockSymbol &symbol)
	{
		interpret(symbol);
	}

	void handle(const ast::NetSymbol &sym)
	{
		if (sym.getInitializer())
			netlist.canvas->connect(netlist.wire(sym), netlist.eval(*sym.getInitializer()));
	}

	void handle(const ast::PortSymbol &sym)
	{
		if (sym.getParentScope()->getContainingInstance() != &netlist.realm)
			return;

		if (!sym.internalSymbol || sym.internalSymbol->name.compare(sym.name)) {
			netlist.add_diag(diag::PortCorrespondence, sym.location);
			return;
		}

		RTLIL::Wire *wire = netlist.wire(*sym.internalSymbol);
		log_assert(wire);
		switch (sym.direction) {
		case ast::ArgumentDirection::In:
			wire->port_input = true;
			break;
		case ast::ArgumentDirection::Out:
			wire->port_output = true;
			break;
		case ast::ArgumentDirection::InOut:
			wire->port_input = true;
			wire->port_output = true;
			break;
		case ast::ArgumentDirection::Ref: // TODO: look up what those are
			break;
		}
	}

	void handle(const ast::MultiPortSymbol &sym)
	{
		if (sym.getParentScope()->getContainingInstance() != &netlist.realm)
			return;

		netlist.add_diag(diag::MultiportUnsupported, sym.location);
	}

	void inline_port_connection(const ast::PortSymbol &port, RTLIL::SigSpec signal)
	{
		if (port.isNullPort)
			return;

		VariableBits internal_signal;

		if (auto expr = port.getInternalExpr()) {
			internal_signal = netlist.eval.lhs(*expr);
		} else {
			ast_invariant(port, ast::ValueSymbol::isKind(port.internalSymbol->kind));
			internal_signal = Variable::from_symbol(&port.internalSymbol->as<ast::ValueSymbol>());
		}

		log_assert(internal_signal.bitwidth() == signal.size());

		if (port.direction == ast::ArgumentDirection::Out) {
			netlist.canvas->connect(signal, netlist.convert_static(internal_signal));
		} else if (port.direction == ast::ArgumentDirection::In) {
			netlist.canvas->connect(netlist.convert_static(internal_signal), signal);
		} else {
			// TODO: better location
			auto &diag = netlist.add_diag(diag::BadInlinedPortConnection, port.location);
			diag << ast::toString(port.direction);
		}
	}

	bool is_blackbox(const ast::DefinitionSymbol &sym)
	{
		for (auto attr : sym.getParentScope()->getCompilation().getAttributes(sym)) {
			if (attr->name == "blackbox"sv && !attr->getValue().isFalse())
				return true;
		}

		if (settings.empty_blackboxes.value_or(false))
			return is_decl_empty_module(*sym.getSyntax());

		return false;
	}

	bool should_dissolve(const ast::InstanceSymbol &sym)
	{
		// blackboxes are never dissolved
		if (sym.isModule() && is_blackbox(sym.body.getDefinition()))
			return false;

		// interfaces are always dissolved
		if (sym.isInterface())
			return true;

		// the rest depends on the hierarchy mode
		switch (settings.hierarchy_mode()) {
		case SynthesisSettings::NONE:
			return true;
		case SynthesisSettings::BEST_EFFORT: {
			for (auto *conn : sym.getPortConnections()) {
				switch (conn->port.kind) {
				case ast::SymbolKind::Port:
				case ast::SymbolKind::MultiPort:
					break;
				case ast::SymbolKind::InterfacePort:
					if (!conn->getIfaceConn().second)
						return true;
					break;
				default:
					return true;
					break;
				}
			}

			if (!sym.isModule())
				return true;

			return false;
			}
		case SynthesisSettings::ALL:
		default:
			return false;
		}
	}

	void handle(const ast::InstanceSymbol &sym)
	{
		// blackboxes get special handling no matter the hierarchy mode
		if (sym.isModule() && is_blackbox(sym.body.getDefinition())) {
			RTLIL::Cell *cell = netlist.canvas->addCell(netlist.id(sym), RTLIL::escape_id(std::string(sym.body.name)));

			for (auto *conn : sym.getPortConnections()) {
				switch (conn->port.kind) {
				case ast::SymbolKind::Port: {
					if (!conn->getExpression())
						continue;
					auto &expr = *conn->getExpression();
					RTLIL::SigSpec signal;
					if (expr.kind == ast::ExpressionKind::Assignment) {
							auto &assign = expr.as<ast::AssignmentExpression>();
						signal = netlist.eval.connection_lhs(assign);
					} else {
						signal = netlist.eval(expr);
					}
					cell->setPort(id(conn->port.name), signal);
					break;
				}
				case ast::SymbolKind::MultiPort:
				case ast::SymbolKind::InterfacePort: {
					slang::SourceLocation loc;
					if (auto expr = conn->getExpression())
						loc = expr->sourceRange.start();
					else
						loc = sym.location;
					auto &diag = netlist.add_diag(diag::UnsupportedBlackboxConnection, loc);
					diag << (conn->port.kind == ast::SymbolKind::MultiPort ? "multi"s : "interface"s);
					break;
				}
				default:
					ast_unreachable(sym);
				}
			}

			sym.body.visit(ast::makeVisitor([&](auto&, const ast::ParameterSymbol &symbol) {
				RTLIL::Const val = convert_const(symbol.getValue());
				if (symbol.isImplicitString(slang::SourceRange(sym.location, sym.location))
						&& val.size() % 8 == 0) {
					val.flags |= RTLIL::CONST_FLAG_STRING;
				}
				cell->setParam(RTLIL::escape_id(std::string(symbol.name)), val);
			}, [&](auto&, const ast::TypeParameterSymbol &symbol) {
				netlist.add_diag(diag::BboxTypeParameter, symbol.location);
			}, [&](auto&, const ast::InstanceSymbol&) {
				// no-op
			}));
			transfer_attrs(sym, cell);
			export_blackbox_to_rtlil(netlist.compilation, sym, netlist.canvas->design);
			return;
		}

		if (should_dissolve(sym)) {
			sym.body.visit(*this);

			for (auto *conn : sym.getPortConnections()) {
				if (!conn->getExpression())
					continue;
				auto &expr = *conn->getExpression();

				// Interface port connections are handled by transparent named value
				// lookup through the port
				if (conn->port.kind == ast::SymbolKind::InterfacePort ||
						conn->port.kind == ast::SymbolKind::ModportPort)
					continue;

				RTLIL::SigSpec signal;
				if (expr.kind == ast::ExpressionKind::Assignment) {
					auto &assign = expr.as<ast::AssignmentExpression>();
					ast::Expression const *right = &assign.right();

					signal = netlist.convert_static(netlist.eval.lhs(assign.left()));
					assert_nonstatic_free(signal);

					while (right->kind == ast::ExpressionKind::Conversion) {
						auto &conv = right->as<ast::ConversionExpression>();

						// assign converted value to the target
						RTLIL::Wire *temporary = netlist.canvas->addWire(netlist.new_id(),
												conv.operand().type->getBitstreamWidth());
						netlist.canvas->connect(signal, netlist.eval.apply_conversion(conv, temporary));

						// set pre-converted value for new target
						signal = temporary;
						right = &conv.operand();
					};

					log_assert(right->kind == ast::ExpressionKind::EmptyArgument);
				} else {
					signal = netlist.eval(expr);
				}

				if (conn->port.kind == ast::SymbolKind::MultiPort) {
					int offset = 0;
					auto &multiport = conn->port.as<ast::MultiPortSymbol>();
					for (auto component : multiport.ports) {
						int width = component->getType().getBitstreamWidth();
						inline_port_connection(*component, signal.extract(offset, width));
						offset += width;
					}
					log_assert(offset == (int) multiport.getType().getBitstreamWidth());
				} else if (conn->port.kind == ast::SymbolKind::Port) {
					inline_port_connection(conn->port.as<ast::PortSymbol>(), signal);
				} else {
					ast_unreachable(conn->port);
				}
			}
		} else {
			log_assert(sym.isModule());
			auto ref_body = &get_instance_body(settings, sym);
			ast_invariant(sym, ref_body->parentInstance != nullptr);
			auto [submodule, inserted] = queue.get_or_emplace(ref_body, netlist, *ref_body->parentInstance);

			RTLIL::Cell *cell = netlist.canvas->addCell(netlist.id(sym), module_type_id(*ref_body));
			for (auto *conn : sym.getPortConnections()) {
				slang::SourceLocation loc;
				if (auto expr = conn->getExpression())
					loc = expr->sourceRange.start();
				else
					loc = sym.location;

				switch (conn->port.kind) {
				case ast::SymbolKind::Port: {
					if (!conn->getExpression())
						continue;
					auto &expr = *conn->getExpression();
					RTLIL::SigSpec signal;
					if (expr.kind == ast::ExpressionKind::Assignment) {
						auto &assign = expr.as<ast::AssignmentExpression>();
						signal = netlist.eval.connection_lhs(assign);
					} else {
						signal = netlist.eval(expr);
					}
					cell->setPort(id(conn->port.name), signal);
					break;
				}
				case ast::SymbolKind::InterfacePort: {
					if (!conn->getIfaceConn().second) {
						netlist.add_diag(diag::ModportRequired, loc);
						if (inserted) {
							submodule.disabled = true;
						}
						continue;
					}

					const ast::Symbol &iface_instance = *conn->getIfaceConn().first;
					const ast::ModportSymbol &ref_modport = *conn->getIfaceConn().second;
					std::span<const slang::ConstantRange> array_range;

					const ast::Scope *iface_scope;
					switch (iface_instance.kind) {
					case ast::SymbolKind::InstanceArray: {
						iface_scope = static_cast<const ast::Scope *>(
										&iface_instance.as<ast::InstanceArraySymbol>());
						auto range1 = conn->port.as<ast::InterfacePortSymbol>().getDeclaredRange();
						ast_invariant(conn->port, range1.has_value());
						array_range = range1.value();
						break;
					}
					case ast::SymbolKind::Instance:
						iface_scope = static_cast<const ast::Scope *>(
										&iface_instance.as<ast::InstanceSymbol>().body);
						break;
					default:
						log_abort();
						break;
					}

					std::string hierpath_suffix = "";
					int array_level = 0;

					iface_instance.visit(ast::makeVisitor(
						[&](auto &visitor, const ast::InstanceArraySymbol &symbol) {
							// Mock instance array symbols made up by slang don't contain
							// the instances as members, but they do contain them as elements
							std::string save = hierpath_suffix;
							int i = 0;
							for (auto &elem : symbol.elements) {
								auto dim = array_range[array_level];
								int hdl_index = dim.lower() + i;
								i++;
								hierpath_suffix += "[" + std::to_string(hdl_index) + "]";
								array_level++;
								elem->visit(visitor);
								array_level--;
								hierpath_suffix = save;
							}
						},
						[&](auto &visitor, const ast::ModportSymbol &modport) {
							// To support interface arrays, we need to match all modports
							// with the same name as ref_modport
							if (!modport.name.compare(ref_modport.name)) {
								if (inserted) {
									submodule.scopes_remap[&static_cast<const ast::Scope&>(modport)] =
															submodule.id(conn->port).str() + hierpath_suffix;
								}
								visitor.visitDefault(modport);
							}
						},
						[&](auto&, const ast::ModportPortSymbol &port) {
							RTLIL::Wire *wire;
							if (inserted) {
								wire = submodule.add_wire(port);
								log_assert(wire);
								switch (port.direction) {
								case ast::ArgumentDirection::In:
									wire->port_input = true;
									break;
								case ast::ArgumentDirection::Out:
									wire->port_output = true;
									break;
								case ast::ArgumentDirection::InOut:
									wire->port_input = true;
									wire->port_output = true;
									break;
								default: {
									auto &diag = netlist.add_diag(diag::UnsupportedPortDirection, port.location);
									diag << ast::toString(port.direction);
									break;
								}
								}
							} else {
								wire = submodule.wire(port);
							}

							ast_invariant(port, port.internalSymbol);
							const ast::Scope *parent = port.getParentScope();
							ast_invariant(port, parent->asSymbol().kind == ast::SymbolKind::Modport);
							const ast::ModportSymbol &modport = parent->asSymbol().as<ast::ModportSymbol>();

							if (netlist.scopes_remap.count(&modport))
								cell->setPort(wire->name, netlist.wire(port));
							else
								cell->setPort(wire->name, netlist.wire(*port.internalSymbol));
						}
					));
					break;
				}
				case ast::SymbolKind::MultiPort: {
					netlist.add_diag(diag::MultiportUnsupported, loc);
					break;
				}
				default:
					ast_unreachable(conn->port);
				}
			}
			transfer_attrs(sym, cell);
		}
	}

	void handle(const ast::ContinuousAssignSymbol &sym)
	{
		if (sym.getDelay() && !settings.ignore_timing.value_or(false))
			netlist.add_diag(diag::GenericTimingUnsyn, sym.getDelay()->sourceRange);

		const ast::AssignmentExpression &expr = sym.getAssignment().as<ast::AssignmentExpression>();
		ast_invariant(expr, !expr.timingControl);

		RTLIL::SigSpec rvalue = netlist.eval(expr.right());

		if (expr.left().kind == ast::ExpressionKind::Streaming) {
			auto& stream_lexpr = expr.left().as<ast::StreamingConcatenationExpression>();
			VariableBits lvalue = netlist.eval.streaming_lhs(stream_lexpr);
			ast_invariant(expr, rvalue.size() >= lvalue.size());
			netlist.canvas->connect(netlist.convert_static(lvalue), rvalue.extract(0, lvalue.size()));
			return;
		}

		VariableBits lhs = netlist.eval.lhs(expr.left());
		netlist.canvas->connect(netlist.convert_static(lhs), rvalue);
	}

	void handle(const ast::GenerateBlockSymbol &sym)
	{
		if (sym.isUninstantiated)
			return;
		visitDefault(sym);
	}

	void handle(const ast::GenerateBlockArraySymbol &sym)
	{
		visitDefault(sym);
	}

	void detect_memories(const ast::InstanceBodySymbol &body)
	{
		mem_detect.process(body);
		netlist.detected_memories = mem_detect.memory_candidates;
	}

	void add_internal_wires(const ast::InstanceBodySymbol &body)
	{
		std::unordered_set<const slang::ast::SubroutineSymbol *> visited_subroutines;
		body.visit(ast::makeVisitor([&](auto&, const ast::ValueSymbol &sym) {
			if (!sym.getType().isFixedSize())
				return;

			if (sym.kind != ast::SymbolKind::Variable
					&& sym.kind != ast::SymbolKind::Net
					&& sym.kind != ast::SymbolKind::FormalArgument)
				return;

			if (sym.kind == ast::SymbolKind::Variable
					&& sym.as<ast::VariableSymbol>().lifetime == ast::VariableLifetime::Automatic)
				return;

			std::string kind{ast::toString(sym.kind)};
			log_debug("Adding %s (%s)\n", log_id(netlist.id(sym)), kind.c_str());

			if (netlist.is_inferred_memory(sym)) {
				RTLIL::Memory *m = new RTLIL::Memory;
				transfer_attrs(sym, m);
				m->name = netlist.id(sym);
				m->width = sym.getType().getArrayElementType()->getBitstreamWidth();
				auto range = sym.getType().getFixedRange();
				m->start_offset = range.lower();
				m->size = range.width();
				netlist.canvas->memories[m->name] = m;
				netlist.emitted_mems[m->name] = {};

				log_debug("Memory inferred for variable %s (size: %d, width: %d)\n",
						  log_id(m->name), m->size, m->width);
			} else {
				netlist.add_wire(sym);
			}
		}, [&](auto& visitor, const ast::InstanceSymbol& sym) {
			if (should_dissolve(sym))
				visitor.visitDefault(sym);
		}, [&](auto& visitor, const ast::CallExpression &call) {
			if (call.isSystemCall())
				return;
			auto* subroutine = std::get<0>(call.subroutine);
			subroutine->visit(visitor);
		}, [&](auto& visitor, const ast::SubroutineSymbol& subroutine) {
			if (visited_subroutines.contains(&subroutine))
				return;

			visited_subroutines.emplace(&subroutine);
			for (auto &member : subroutine.members())
				member.visit(visitor);
		}, [&](auto& visitor, const ast::GenerateBlockSymbol& sym) {
			/* stop at uninstantiated generate blocks */
			if (sym.isUninstantiated)
				return;
			visitor.visitDefault(sym);
		}));
	}

	void initialize_var_init(const ast::InstanceBodySymbol &body)
	{
		body.visit(ast::makeVisitor([&](auto&, const ast::VariableSymbol &sym) {
			slang::ConstantValue initval = nullptr;
			if (sym.getInitializer() && sym.lifetime == ast::VariableLifetime::Static)
				initval = sym.getInitializer()->eval(initial_eval.context);
			initial_eval.context.createLocal(&sym, initval);
		}, [&](auto& visitor, const ast::InstanceSymbol& sym) {
			if (should_dissolve(sym))
				visitor.visitDefault(sym);
		}, [&](auto& visitor, const ast::GenerateBlockSymbol& sym) {
			/* stop at uninstantiated generate blocks */
			if (sym.isUninstantiated)
				return;
			visitor.visitDefault(sym);
		}));
	}

	void transfer_var_init(const ast::InstanceBodySymbol &body)
	{
		body.visit(ast::makeVisitor([&](auto&, const ast::VariableSymbol &sym) {
			if (sym.getType().isFixedSize() && sym.lifetime == ast::VariableLifetime::Static) {
				auto storage = initial_eval.context.findLocal(&sym);
				log_assert(storage);
				auto const_ = convert_const(*storage);
				if (!const_.is_fully_undef()) {
					if (netlist.is_inferred_memory(sym)) {
						RTLIL::IdString id = netlist.id(sym);
						RTLIL::Memory *m = netlist.canvas->memories.at(id);
						RTLIL::Cell *meminit = netlist.canvas->addCell(netlist.new_id(), ID($meminit_v2));
						int abits = 32;
						ast_invariant(sym, m->width * m->size == const_.size());
						meminit->setParam(ID::MEMID, id.str());
						meminit->setParam(ID::PRIORITY, 0);
						meminit->setParam(ID::ABITS, abits);
						meminit->setParam(ID::WORDS, m->size);
						meminit->setParam(ID::WIDTH, m->width);
						meminit->setPort(ID::ADDR, m->start_offset);
						bool little_endian = sym.getType().getFixedRange().isLittleEndian();
						meminit->setPort(ID::DATA, little_endian ? const_ : reverse_data(const_, m->width));
						meminit->setPort(ID::EN, RTLIL::Const(RTLIL::S1, m->width));
					} else {
						auto wire = netlist.wire(sym);
						log_assert(wire);
						wire->attributes[RTLIL::ID::init] = const_;
					}
				}
			}
		}, [&](auto& visitor, const ast::InstanceSymbol& symbol) {
			if (should_dissolve(symbol))
				visitor.visitDefault(symbol);
		}, [&](auto&, const ast::ProceduralBlockSymbol&) {
			/* do not descend into procedural blocks */
		}, [&](auto& visitor, const ast::GenerateBlockSymbol& sym) {
			/* stop at uninstantiated generate blocks */
			if (sym.isUninstantiated)
				return;
			visitor.visitDefault(sym);
		}));
	}

	void handle(const ast::InstanceBodySymbol &body)
	{
		if (&body == &netlist.realm) {
			// This is the containing instance body for this netlist;
			// find inferred memories
			detect_memories(body);
			// add all internal wires before we enter the body
			add_internal_wires(body);
			// Evaluate inline initializers on variables
			initialize_var_init(body);
			// Visit the body for the bulk of processing
			visitDefault(body);
			// Now transfer initializers (possibly updated from initial statements)
			// onto RTLIL wires
			transfer_var_init(body);
			netlist.add_diagnostics(initial_eval.context.getAllDiagnostics());
		} else {
			visitDefault(body);
		}
	}

	void handle(const ast::UninstantiatedDefSymbol &sym)
	{
		if (sym.isChecker()) {
			netlist.add_diag(diag::LangFeatureUnsupported, sym.location);
			return;
		}

		if (!sym.paramExpressions.empty()) {
			netlist.add_diag(diag::NoParamsOnUnkBboxes, sym.location);
			return;
		}

		RTLIL::Cell *cell = netlist.canvas->addCell(netlist.id(sym),
												id(sym.definitionName));
		transfer_attrs(sym, cell);

		auto port_names = sym.getPortNames();
		auto port_conns = sym.getPortConnections();
		ast_invariant(sym, port_names.size() == port_conns.size());
		for (int i = 0; i < (int) port_names.size(); i++) {
			if (port_names[i].empty()) {
				netlist.add_diag(diag::ConnNameRequiredOnUnkBboxes, sym.location);
				continue;
			}

			auto &expr = port_conns[i]->as<ast::SimpleAssertionExpr>().expr;
			cell->setPort(RTLIL::escape_id(std::string{port_names[i]}), netlist.eval(expr));
		}
	}

	void handle(const ast::ClockingBlockSymbol& symbol) {
		if (!netlist.settings.ignore_timing.value_or(false))
			netlist.add_diag(diag::GenericTimingUnsyn, symbol.location);
	}

	void handle(const ast::Type&) {}
	void handle(const ast::NetType&) {}
	void handle(const ast::ForwardingTypedefSymbol&) {}
	void handle(const ast::TransparentMemberSymbol&) {}
	void handle(const ast::SubroutineSymbol&) {}
	void handle(const ast::ParameterSymbol&) {}
	void handle(const ast::TypeParameterSymbol&) {}
	void handle(const ast::WildcardImportSymbol&) {}
	void handle(const ast::ExplicitImportSymbol&) {}
	void handle(const ast::GenvarSymbol&) {}
	void handle(const ast::VariableSymbol&) {}
	void handle(const ast::EmptyMemberSymbol&) {}
	void handle(const ast::ModportSymbol&) {}
	void handle(const ast::InterfacePortSymbol&) {}
	void handle(const ast::GenericClassDefSymbol&) {}
	void handle(const ast::LetDeclSymbol&) {}
	void handle(const ast::SpecparamSymbol&) {}
	void handle(const ast::DefParamSymbol&) {}

	void handle(const ast::StatementBlockSymbol &sym)
	{
		visitDefault(sym);
	}

	void handle(const ast::InstanceArraySymbol &sym)
	{
		visitDefault(sym);
	}

	void handle(const ast::PrimitiveInstanceSymbol &sym)
	{
		auto ports = sym.getPortConnections();
		auto type = sym.primitiveType.name;
		auto id = (!sym.name.compare("")) ? netlist.new_id() : netlist.id(sym);
		RTLIL::IdString op;
		bool inv_y = false;
		RTLIL::Cell *cell;
		ast_invariant(sym, ports.front()->kind == ast::ExpressionKind::Assignment);
		auto &assign = ports.front()->as<ast::AssignmentExpression>();
		auto y = netlist.eval.connection_lhs(assign);
		switch (sym.primitiveType.primitiveKind) {
		case ast::PrimitiveSymbol::PrimitiveKind::NInput:
			{
				// and, or, xor, xnor, nand, nor
				if (!type.compare("and")) {
					op = (ports.size() == 3) ? ID($and) : ID($reduce_and);
				} else if (!type.compare("or")) {
					op = (ports.size() == 3) ? ID($or) : ID($reduce_or);
				} else if (!type.compare("nand")) {
					op = (ports.size() == 3) ? ID($and) : ID($reduce_and);
					inv_y = 1;
				} else if (!type.compare("nor")) {
					op = (ports.size() == 3) ? ID($or) : ID($reduce_or);
					inv_y = 1;
				} else if (!type.compare("xor")) {
					op = (ports.size() == 3) ? ID($xor) : ID($reduce_xor);
				} else if (!type.compare("xnor")) {
					op = (ports.size() == 3) ? ID($xnor) : ID($reduce_xnor);
				} else {
					ast_unreachable(sym);
				}
				cell = netlist.canvas->addCell(id, op);
				if (ports.size() == 3) {
					// word-level primitive cell for 2 input ports
					cell->setPort(ID::A, netlist.eval(*ports[1]));
					cell->setPort(ID::B, netlist.eval(*ports[2]));
				} else {
					// reduce_* cell for 3 or more input ports
					RTLIL::SigSpec a;
					for (auto port : ports)
						if (port != ports.front())
							a.append(netlist.eval(*port));
					cell->setPort(ID::A, a);
				}
				cell->setPort(ID::Y, y);
				break;
			}
		case ast::PrimitiveSymbol::PrimitiveKind::NOutput:
			{
				// buf, not
				// Last port is input, all others are outputs
				if (!type.compare("buf")) {
					op = ID($buf);
				} else if (!type.compare("not")) {
					op = ID($not);
				} else {
					ast_unreachable(sym);
				}
				cell = netlist.canvas->addCell(id, op);
				cell->setPort(ID::A, netlist.eval(*(ports.back())));
				cell->setPort(ID::Y, y);
				for (auto port : ports) {
					if (port != ports.front() && port != ports.back()) {
						auto &assign = port->as<ast::AssignmentExpression>();
						netlist.canvas->connect(cell->getPort(ID::Y), netlist.eval.connection_lhs(assign));
					}
				}
				break;
			}
		case ast::PrimitiveSymbol::PrimitiveKind::UserDefined:
			{
				// User-defined primitives (UDPs) are unsupported
				netlist.add_diag(diag::UdpUnsupported, sym.location);
				break;
			}
		default:
			{
				if (!type.compare("pulldown")) {
					// pulldown is equivalent to: buffer with constant 0 input
					cell = netlist.canvas->addCell(id, ID($buf));
					cell->setPort(ID::A, RTLIL::S0);
					cell->setPort(ID::Y, y);
				} else if (!type.compare("pullup")) {
					// pullup is equivalent to: buffer with constant 1 input
					cell = netlist.canvas->addCell(id, ID($buf));
					cell->setPort(ID::A, RTLIL::S1);
					cell->setPort(ID::Y, y);
				} else if (!type.compare("bufif0") || !type.compare("bufif1") ||
				           !type.compare("notif0") || !type.compare("notif1") ||
					         !type.compare("pmos")   || !type.compare("rpmos")  ||
					         !type.compare("nmos")   || !type.compare("rnmos")) {
					// These are all tri-state buffers, some having inverted enable/output
					// Use $mux instead of $tribuf to avoid Yosys issues...
					bool inv_a = false;
					bool inv_en = false;
					if (!type.compare("notif0")) {
						inv_a = inv_en = true;
					} else if (!type.compare("notif1")) {
						inv_a = true;
					} else if (!type.compare("bufif0")) {
						inv_en = true;
					} else if (!type.compare("pmos")) {
						inv_en = true;
					} else if (!type.compare("rpmos")) {
						inv_en = true;
					}
					auto in = netlist.eval(*ports[1]);
					if (inv_a) {
						auto mid_wire = netlist.canvas->addWire(id.str() + "_mid", in.size());
						auto inv_cell = netlist.canvas->addNot(id.str() + "_ainv", in, mid_wire);
						in = mid_wire;
						transfer_attrs(sym, inv_cell);
					}
					auto a = inv_en ? in : RTLIL::Sz;
					auto b = inv_en ? RTLIL::Sz : in;
					auto en = netlist.eval(*ports[2]);
					cell = netlist.canvas->addMux(id, a, b, en, y);
				} else if (!type.compare("cmos") || !type.compare("rcmos")) {
					// cmos (w, datain, ncontrol, pcontrol);
					// is equivalent to:
					// nmos (w, datain, ncontrol); pmos (w, datain, pcontrol);
					// Use $mux instead of $tribuf to avoid Yosys issues...
					auto a = netlist.eval(*ports[1]);
					auto n_en = netlist.eval(*ports[2]);
					auto p_en = netlist.eval(*ports[3]);
					auto nmos = netlist.canvas->addMux(id.str() + "_n", RTLIL::Sz, a, n_en, y);
					auto pmos = netlist.canvas->addMux(id.str() + "_p", a, RTLIL::Sz, p_en, y);
					transfer_attrs(sym, nmos);
					cell = pmos; // transfer_attrs to pmos after switch block
				} else {
					// bidir (tran/rtran/tranif0/rtranif0/tranif1/rtranif1) are unsupported
					netlist.add_diag(diag::PrimTypeUnsupported, sym.location);
				}
			}
		}
		if (cell->type == ID($buf) && !Yosys::yosys_celltypes.cell_known(cell->type))
			cell->type = ID($pos); // backwards compatibility for yosys < 0.46 (no $buf cells)
		cell->fixup_parameters();
		transfer_attrs(sym, cell);
		if (inv_y) {
			// Invert output signal where needed
			netlist.canvas->rename(cell->name, id.str() + "_yinv");
			auto mid_wire = netlist.canvas->addWire(id.str() + "_mid", y.size());
			auto inv_cell = netlist.canvas->addNot(id, mid_wire, y);
			cell->setPort(ID::Y, mid_wire);
			transfer_attrs(sym, inv_cell);
		}
	}

	void handle(const ast::Symbol &sym)
	{
		unimplemented(sym);
	}
};

static void build_hierpath2(NetlistContext &netlist,
							std::ostringstream &s, const ast::Scope *scope)
{
	if (!scope ||
		static_cast<const ast::Scope *>(&netlist.realm) == scope)
		return;

	if (netlist.scopes_remap.count(scope)) {
		s << netlist.scopes_remap.at(scope) << ".";
		return;
	}

	const ast::Symbol *symbol = &scope->asSymbol();

	if (symbol->kind == ast::SymbolKind::InstanceBody)
		symbol = symbol->as<ast::InstanceBodySymbol>().parentInstance;
	if (symbol->kind == ast::SymbolKind::CheckerInstanceBody)
		symbol = symbol->as<ast::CheckerInstanceBodySymbol>().parentInstance;

	if (auto parent = symbol->getParentScope())
		build_hierpath2(netlist, s, parent);

	if (symbol->kind == ast::SymbolKind::GenerateBlockArray) {
		auto &array = symbol->as<ast::GenerateBlockArraySymbol>();
		s << array.getExternalName();
	} else if (symbol->kind == ast::SymbolKind::GenerateBlock) {
		auto &block = symbol->as<ast::GenerateBlockSymbol>();
		if (auto index = block.arrayIndex) {
			s << "[" << index->toString(slang::LiteralBase::Decimal, false) << "].";
		} else {
			s << block.getExternalName() << ".";
		}
	} else if (symbol->kind == ast::SymbolKind::Instance ||
			   symbol->kind == ast::SymbolKind::CheckerInstance) {
		s << symbol->name;

		auto &inst = symbol->as<ast::InstanceSymbolBase>();
		if (!inst.arrayPath.empty()) {
			slang::SmallVector<slang::ConstantRange, 8> dimensions;
			inst.getArrayDimensions(dimensions);

			for (size_t i = 0; i < inst.arrayPath.size(); i++)
				s << "[" << ((int) inst.arrayPath[i]) + dimensions[i].lower() << "]";
		}

		s << ".";
	} else if (symbol->kind == ast::SymbolKind::InstanceArray) {
		s << symbol->name;
	} else if (!symbol->name.empty()) {
		s << symbol->name << ".";
	} else if (symbol->kind == ast::SymbolKind::StatementBlock) {
		s << "$" << (int) symbol->getIndex() << ".";
	}
}

static bool build_hierpath3(const ast::Scope *relative_to,
							std::ostringstream &s, const ast::Scope *scope)
{
	log_assert(scope);

	if (relative_to == scope)
		return false;

	const ast::Symbol *symbol = &scope->asSymbol();

	if (symbol->kind == ast::SymbolKind::InstanceBody)
		symbol = symbol->as<ast::InstanceBodySymbol>().parentInstance;
	if (symbol->kind == ast::SymbolKind::CheckerInstanceBody)
		symbol = symbol->as<ast::CheckerInstanceBodySymbol>().parentInstance;

	bool pending;
	if (auto parent = symbol->getParentScope()) {
		pending = build_hierpath3(relative_to, s, parent);
	} else {
		log_abort();
	}

	if ((symbol->kind == ast::SymbolKind::GenerateBlockArray ||
			symbol->kind == ast::SymbolKind::GenerateBlock ||
			symbol->kind == ast::SymbolKind::Instance ||
			symbol->kind == ast::SymbolKind::CheckerInstance ||
			!symbol->name.empty() ||
			symbol->kind == ast::SymbolKind::StatementBlock) &&
			pending) {
		s << ".";
		pending = false;
	}

	if (symbol->kind == ast::SymbolKind::GenerateBlockArray) {
		auto &array = symbol->as<ast::GenerateBlockArraySymbol>();
		s << array.getExternalName();
	} else if (symbol->kind == ast::SymbolKind::GenerateBlock) {
		auto &block = symbol->as<ast::GenerateBlockSymbol>();
		if (auto index = block.arrayIndex) {
			s << "[" << index->toString(slang::LiteralBase::Decimal, false) << "]";
		} else {
			s << block.getExternalName();
		}

		pending = true;
	} else if (symbol->kind == ast::SymbolKind::Instance ||
			   symbol->kind == ast::SymbolKind::CheckerInstance) {
		s << symbol->name;

		auto &inst = symbol->as<ast::InstanceSymbolBase>();
		if (!inst.arrayPath.empty()) {
			slang::SmallVector<slang::ConstantRange, 8> dimensions;
			inst.getArrayDimensions(dimensions);

			for (size_t i = 0; i < inst.arrayPath.size(); i++)
				s << "[" << ((int) inst.arrayPath[i]) + dimensions[i].lower() << "]";
		}

		pending = true;
	} else if (symbol->kind == ast::SymbolKind::InstanceArray) {
		s << symbol->name;
	} else if (!symbol->name.empty()) {
		s << symbol->name;

		pending = true;
	} else if (symbol->kind == ast::SymbolKind::StatementBlock) {
		s << "$" << (int) symbol->getIndex();

		pending = true;
	}

	return pending;
}

std::string hierpath_relative_to(const ast::Scope *relative_to, const ast::Scope *scope)
{
	std::ostringstream path;
	build_hierpath3(relative_to, path, scope);
	return path.str();
}

RTLIL::IdString NetlistContext::id(const ast::Symbol &symbol)
{
	std::ostringstream path;
	build_hierpath2(*this, path, symbol.getParentScope());
	path << symbol.name;

	if (symbol.kind == ast::SymbolKind::Instance ||
			symbol.kind == ast::SymbolKind::PrimitiveInstance) {
		auto &inst = symbol.as<ast::InstanceSymbolBase>();
		if (!inst.arrayPath.empty()) {
			slang::SmallVector<slang::ConstantRange, 8> dimensions;
			inst.getArrayDimensions(dimensions);
			for (size_t i = 0; i < inst.arrayPath.size(); i++)
				path << "[" << ((int) inst.arrayPath[i]) + dimensions[i].lower() << "]";
		}
	}

	return RTLIL::escape_id(path.str());
}

RTLIL::Wire *NetlistContext::add_wire(const ast::ValueSymbol &symbol)
{
	auto w = canvas->addWire(id(symbol), symbol.getType().getBitstreamWidth());
	wire_cache[&symbol] = w;
	transfer_attrs(symbol, w);
	return w;
}

RTLIL::Wire *NetlistContext::wire(const ast::Symbol &symbol)
{
	auto it = wire_cache.find(&symbol);
	if (it == wire_cache.end())
		wire_missing(*this, symbol);
	return it->second;
}

RTLIL::SigSpec NetlistContext::convert_static(VariableBits bits)
{
	RTLIL::SigSpec ret;

	for (auto vchunk : bits.chunks()) {
		switch (vchunk.variable.kind) {
		case Variable::Static: {
			RTLIL::SigChunk chunk{wire(*vchunk.variable.get_symbol()),
					vchunk.base, vchunk.length};
			ret.append(chunk);
		} break;
		case Variable::Dummy:
			ret.append(canvas->addWire(new_id("dummy"), vchunk.length));
			break;
		default:
			log_abort();
		}
	}

	return ret;
}

NetlistContext::NetlistContext(
		RTLIL::Design *design,
		SynthesisSettings &settings,
		ast::Compilation &compilation,
		const ast::InstanceSymbol &instance)
	: settings(settings), compilation(compilation), realm(instance.body), eval(*this)
{
	canvas = design->addModule(module_type_id(instance.body));
	transfer_attrs(instance.body.getDefinition(), canvas);
}

NetlistContext::NetlistContext(
		NetlistContext &other,
		const ast::InstanceSymbol &instance)
	: NetlistContext(other.canvas->design, other.settings, other.compilation, instance)
{
}

NetlistContext::~NetlistContext()
{
	// move constructor could have cleared our canvas pointer
	if (canvas) {
		canvas->fixup_ports();
		canvas->check();
	}
}

USING_YOSYS_NAMESPACE

struct SlangVersionPass : Pass {
	SlangVersionPass() : Pass("slang_version", "display revision of slang frontend") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("	slang_version\n");
		log("\n");
		log("Display git revisions of the slang frontend.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, [[maybe_unused]] RTLIL::Design *d) override
	{
		if (args.size() != 1)
			cmd_error(args, 1, "Extra argument");

		log("yosys-slang revision %s\n", YOSYS_SLANG_REVISION);
		log("slang revision %s\n", SLANG_REVISION);
	}
} SlangVersionPass;

static std::vector<std::string> default_options;
static std::vector<std::vector<std::string>> defaults_stack;

void fixup_options(SynthesisSettings &settings, slang::driver::Driver &driver)
{
	if (!settings.no_default_translate_off.value_or(false)) {
		auto &format_list = driver.options.translateOffOptions;
		format_list.insert(format_list.end(), {
			"pragma,synthesis_off,synthesis_on",
			"pragma,translate_off,translate_on",
			"synopsys,synthesis_off,synthesis_on",
			"synopsys,translate_off,translate_on",
			"synthesis,translate_off,translate_on",
			"xilinx,translate_off,translate_on",
		});
	}

	auto &disable_inst_caching = driver.options.compilationFlags[ast::CompilationFlags::DisableInstanceCaching];
	if (!disable_inst_caching.has_value()) {
		disable_inst_caching = true;
	}
	settings.disable_instance_caching = disable_inst_caching.value();

	// revisit slang#1326 in case of issues with this override
	auto &time_scale = driver.options.timeScale;
	if (!time_scale.has_value()) {
		time_scale = "1ns/1ns";
	}
}

static std::string expected_diagnostic;

std::vector<slang::DiagCode> forbidden_diag_demotions = {
	slang::diag::UnknownSystemName
};

void catch_forbidden_diag_demotions(slang::DiagnosticEngine &engine) {
	// FIXME: this doesn't catch demotions which are location specific via pragmas
	for (auto code : forbidden_diag_demotions) {
		if (engine.getSeverity(code, slang::SourceLocation::NoLocation) !=
				slang::DiagnosticSeverity::Error) {
			slang::Diagnostic demotion_diag(diag::ForbiddenDemotion, slang::SourceLocation::NoLocation);
			demotion_diag << engine.getOptionName(code);
			engine.issue(demotion_diag);
			engine.setSeverity(slang::diag::UnknownSystemName, slang::DiagnosticSeverity::Error);
		}
	}
}

struct SlangFrontend : Frontend {
	SlangFrontend() : Frontend("slang", "read SystemVerilog (slang)") {}

	void help() override
	{
		slang::driver::Driver driver;
		driver.addStandardArgs();
		SynthesisSettings settings;
		settings.addOptions(driver.cmdLine);
		log("%s\n", driver.cmdLine.getHelpText("Slang-based SystemVerilog frontend").c_str());
	}

	std::optional<std::string> read_heredoc(std::vector<std::string> &args)
	{
		std::string eot;

		if (!args.empty() && args.back().compare(0, 2, "<<") == 0) {
			eot = args.back().substr(2);
			args.pop_back();
		} else if (args.size() >= 2 && args[args.size() - 2] == "<<") {
			eot = args.back();
			args.pop_back();
			args.pop_back();
		} else {
			return {};
		}

		if (eot.empty())
			log_error("Missing EOT marker for reading a here-document\n");

		std::string buffer;
		bool in_script = current_script_file != nullptr;

		while (true) {
			char line[4096];
			if (!fgets(line, sizeof(line), in_script ? current_script_file : stdin))
				log_error("Unexpected EOF reading a here-document\n");

			const char *p = line;
			while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n')
				p++;

			if (!strncmp(p, eot.data(), eot.size()) &&
				(*(p + eot.size()) == '\r' || *(p + eot.size()) == '\n'))
				break;
			else
				buffer += line;
		}

		return buffer;
	}

	// There are three cases handled by this function:
	// 1. Normal mode; no expected diagnostics. Return `false` to continue executing.
	// 2. Test mode; expected diagnostic found. Return `true` to exit early with success.
	// 3a. Test mode; expected diagnostic not found but more could appear later. Return `false`.
	// 3b. Test mode; expected diagnostic not found. Use `log_error()` to exit early with failure.
	bool check_diagnostics(slang::DiagnosticEngine &diagEngine, const slang::SmallVector<slang::Diagnostic> &diags, bool last)
	{
		if (expected_diagnostic.empty())
			return false;

		for (auto &diag : diags) {
			auto message = diagEngine.formatMessage(diag);
			if (message == expected_diagnostic) {
				log("Expected diagnostic `%s' found\n", expected_diagnostic.c_str());
				expected_diagnostic.clear();
				return true;
			}
		}
		if (last)
			log_error("Expected diagnostic `%s' but none emitted\n", expected_diagnostic.c_str());
		else
			return false;
	}

	void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		(void) f;
		(void) filename;
		log_header(design, "Executing SLANG frontend.\n");

		slang::driver::Driver driver;
		driver.addStandardArgs();
		SynthesisSettings settings;
		settings.addOptions(driver.cmdLine);
		diag::setup_messages(driver.diagEngine);

		{
			if (auto heredoc = read_heredoc(args)) {
				auto buffer = driver.sourceManager.assignText("<inlined>", std::string_view{heredoc.value()});
				driver.sourceLoader.addBuffer(buffer);
			}

			args.insert(args.begin() + 1, default_options.begin(), default_options.end());

			std::vector<std::unique_ptr<char[]>> c_args_guard;
			std::vector<char *> c_args;

			for (auto arg : args) {
				char *c = new char[arg.size() + 1];
				strcpy(c, arg.c_str());
				c_args_guard.emplace_back(c);
				c_args.push_back(c);
			}

			if (!driver.parseCommandLine(c_args.size(), &c_args[0]))
				log_cmd_error("Bad command\n");
		}

		fixup_options(settings, driver);
		if (!driver.processOptions())
			log_cmd_error("Bad command\n");
		catch_forbidden_diag_demotions(driver.diagEngine);

		try {
			if (!driver.parseAllSources())
				log_error("Parsing failed\n");

			auto compilation = driver.createCompilation();

			if (settings.extern_modules.value_or(true))
				import_blackboxes_from_rtlil(driver.sourceManager, *compilation, design);

			if (settings.dump_ast.value_or(false)) {
				slang::JsonWriter writer;
				writer.setPrettyPrint(true);
				ast::ASTSerializer serializer(*compilation, writer);
				serializer.serialize(compilation->getRoot());
				std::cout << writer.view() << std::endl;
			}

			bool in_succesful_failtest = false;

			driver.reportCompilation(*compilation,/* quiet */ false);
			if (check_diagnostics(driver.diagEngine, compilation->getAllDiagnostics(), /*last=*/false))
				in_succesful_failtest = true;

			if (driver.diagEngine.getNumErrors()) {
				// Stop here should there have been any errors from AST compilation,
				// PopulateNetlist requires a well-formed AST without error nodes
				(void) driver.reportDiagnostics(/* quiet */ false);
				if (!in_succesful_failtest)
					log_error("Compilation failed\n");
				return;
			}

			if (settings.ast_compilation_only.value_or(false)) {
				(void) driver.reportDiagnostics(/* quiet */ false);
				return;
			}

			global_compilation = &(*compilation);
			global_sourcemgr = compilation->getSourceManager();

			HierarchyQueue hqueue;
			for (auto instance : compilation->getRoot().topInstances) {
				auto ref_body = &get_instance_body(settings, *instance);
				log_assert(ref_body->parentInstance);
				auto [netlist, new_] = hqueue.get_or_emplace(ref_body, design, settings,
															 *compilation, *ref_body->parentInstance);
				log_assert(new_);
				netlist.canvas->attributes[ID::top] = 1;
			}

			for (int i = 0; i < (int) hqueue.queue.size(); i++) {
				NetlistContext &netlist = *hqueue.queue[i];

				if (netlist.disabled)
					continue;

				PopulateNetlist populate(hqueue, netlist);
				netlist.realm.visit(populate);

				slang::Diagnostics diags;
				diags.append_range(populate.mem_detect.issued_diagnostics);
				diags.append_range(netlist.issued_diagnostics);
				diags.sort(driver.sourceManager);

				if (check_diagnostics(driver.diagEngine, diags, /*last=*/false))
					in_succesful_failtest = true;

				for (int i = 0; i < (int) diags.size(); i++) {
					if (i > 0 && diags[i] == diags[i - 1])
						continue;
					driver.diagEngine.issue(diags[i]);
				}
			}

			if (check_diagnostics(driver.diagEngine, {}, /*last=*/true))
				in_succesful_failtest = true;

			if (!driver.reportDiagnostics(/* quiet */ false)) {
				if (!in_succesful_failtest)
					log_error("Compilation failed\n");
				return;
			}
		} catch (const std::exception& e) {
			log_error("Exception: %s\n", e.what());
		}

		if (!settings.no_proc.value_or(false)) {
			log_push();
			call(design, "undriven");
			call(design, "proc_clean");
			call(design, "tribuf");
			call(design, "proc_rmdead");
			call(design, "proc_prune");
			call(design, "proc_init");
			call(design, "proc_rom");
			call(design, "proc_mux");
			call(design, "proc_clean");
			call(design, "opt_expr -keepdc");
			log_pop();
		}
	}
} SlangFrontend;

struct SlangDefaultsPass : Pass {
	SlangDefaultsPass() : Pass("slang_defaults", "set default options for read_slang") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("	slang_defaults -add [options]\n");
		log("\n");
		log("Add default options for subsequent calls to read_slang.\n");
		log("\n");
		log("\n");
		log("	slang_defaults -clear\n");
		log("\n");
		log("Clear the list of default options to read_slang.\n");
		log("\n");
		log("\n");
		log("	slang_defaults -push\n");
		log("	slang_defaults -pop\n");
		log("\n");
		log("Push or pop the default option list to a stack. On -push the list isn't cleared.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, [[maybe_unused]] RTLIL::Design *d) override
	{
		if (args.size() < 2)
			cmd_error(args, 1, "Missing argument");

		if (args[1] == "-add") {
			default_options.insert(default_options.end(), args.begin() + 2, args.end());
		} else {
			if (args.size() != 2)
				cmd_error(args, 2, "Extra argument");

			if (args[1] == "-clear") {
				default_options.clear();
			} else if (args[1] == "-push") {
				defaults_stack.push_back(default_options);
			} else if (args[1] == "-pop") {
				if (!defaults_stack.empty()) {
					default_options.swap(defaults_stack.back());
					defaults_stack.pop_back();
				} else {
					default_options.clear();
				}
			} else {
				cmd_error(args, 1, "Unknown option");
			}
		}
	}
} SlangDefaultsPass;

struct UndrivenPass : Pass {
	UndrivenPass() : Pass("undriven", "assign initializers to undriven signals") {}
	void execute(std::vector<std::string> args, RTLIL::Design *d) override
	{
		log_header(d, "Executing UNDRIVEN pass. (resolve undriven signals)\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			break;
		}
		extra_args(args, argidx, d);

		for (auto module : d->selected_whole_modules_warn()) {
			SigPool driven;

			std::function<void(RTLIL::CaseRule *rule)> visit_case = [&](RTLIL::CaseRule *rule) {
				for (auto &action : rule->actions)
					driven.add(action.first);

				for (auto switch_ : rule->switches) {
					for (auto case_ : switch_->cases)
						visit_case(case_);
				}
			};

			for (auto proc : module->processes) {
				visit_case(&proc.second->root_case);

				if (!proc.second->syncs.empty())
					log_error("Process %s in module %s contains sync rules, that's unsupported by the 'undriven' command.\n",
							  log_id(proc.second), log_id(module));
			}

			for (auto conn : module->connections())
				driven.add(conn.first);

			for (auto cell : module->cells())
			for (auto &conn : cell->connections())
			if (cell->output(conn.first))
			for (auto bit : conn.second)
				driven.add(bit);

			for (auto wire : module->wires()) {
				if (!wire->attributes.count(ID::init) || wire->port_input)
					continue;

				Const &init = wire->attributes[ID::init];
				for (int i = 0; i < wire->width; i++)
				if (!driven.check(SigBit(wire, i)) && i < init.size() && (init[i] == RTLIL::S1 || init[i] == RTLIL::S0))
					module->connect(SigBit(wire, i), init[i]);
			}
		}
	}
} UndrivenPass;

struct TestSlangDiagPass : Pass {
	TestSlangDiagPass() : Pass("test_slangdiag", "test diagnostics emission by the slang frontend") {}

	void help() override
	{
		log("Perform internal test of the slang frontend.\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing TEST_SLANGDIAG pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-expect" && argidx+1 < args.size()) {
				std::string message = args[++argidx];
				if (message.front() == '\"' && message.back() == '\"')
					message = message.substr(1, message.size() - 2);
				expected_diagnostic = message;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design, false);
	}
} TestSlangDiagPass;

class TFunc : public ast::SystemSubroutine {
public:
	TFunc() : ast::SystemSubroutine("$t", ast::SubroutineKind::Function) {}

	const ast::Type& checkArguments(const ast::ASTContext& context, const Args& args,
									slang::SourceRange range, const ast::Expression*) const final {
		auto& comp = context.getCompilation();
		if (!checkArgCount(context, false, args, range, 1, 1))
			return comp.getErrorType();
		return comp.getVoidType();
	}

	slang::ConstantValue eval(ast::EvalContext& context, const Args&,
							  slang::SourceRange range,
							  const ast::CallExpression::SystemCallInfo&) const final {
		notConst(context, range);
		return nullptr;
	}
};

struct TestSlangExprPass : Pass {
	TestSlangExprPass() : Pass("test_slangexpr", "test expression evaluation within slang frontend") {}

	void help() override
	{
		log("Perform internal test of the slang frontend.\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *d) override
	{
		log_header(d, "Executing TEST_SLANGEXPR pass.\n");

		slang::driver::Driver driver;
		driver.addStandardArgs();
		SynthesisSettings settings;
		settings.addOptions(driver.cmdLine);

		{
			std::vector<char *> c_args;
			for (auto arg : args) {
				char *c = new char[arg.size() + 1];
				strcpy(c, arg.c_str());
				c_args.push_back(c);
			}
			if (!driver.parseCommandLine(c_args.size(), &c_args[0]))
				log_cmd_error("Bad command\n");
		}

		fixup_options(settings, driver);
		if (!driver.processOptions())
			log_cmd_error("Bad command\n");

		if (!driver.parseAllSources())
			log_error("Parsing failed\n");

		auto compilation = driver.createCompilation();
		auto tfunc = std::make_shared<TFunc>();
		compilation->addSystemSubroutine(tfunc);

		if (settings.dump_ast.value_or(false)) {
			slang::JsonWriter writer;
			writer.setPrettyPrint(true);
			ast::ASTSerializer serializer(*compilation, writer);
			serializer.serialize(compilation->getRoot());
			std::cout << writer.view() << std::endl;
		}

		log_assert(compilation->getRoot().topInstances.size() == 1);
		auto *top = compilation->getRoot().topInstances[0];
		compilation->forceElaborate(top->body);

		driver.reportCompilation(*compilation,/* quiet */ false);
		if (driver.diagEngine.getNumErrors()) {
			(void) driver.reportDiagnostics(/* quiet */ false);
			log_error("Compilation failed\n");
			return;
		}

		global_compilation = &(*compilation);
		global_sourcemgr = compilation->getSourceManager();

		HierarchyQueue dummy_queue;
		NetlistContext netlist(d, settings, *compilation, *top);
		PopulateNetlist populate(dummy_queue, netlist);
		populate.add_internal_wires(top->body);

		EvalContext amended_eval(netlist);
		amended_eval.ignore_ast_constants = true;

		int ntests = 0;
		int nfailures = 0;

		top->visit(ast::makeVisitor([&](auto&, const ast::SubroutineSymbol&) {
			// ignore
		}, [&](auto&, const ast::ExpressionStatement &stmt) {
			assert(stmt.expr.kind == ast::ExpressionKind::Call);
			auto &call = stmt.expr.as<ast::CallExpression>();
			assert(call.getSubroutineName() == "$t");
			auto expr = call.arguments()[0];

			SigSpec ref = netlist.eval(*expr);
			SigSpec test = amended_eval(*expr);

			slang::SourceRange sr = expr->sourceRange;
			std::string_view text = global_sourcemgr->getSourceText(sr.start().buffer()) \
										.substr(sr.start().offset(), sr.end().offset() - sr.start().offset());

			if (ref == test) {
				log_debug("%s: %s (ref) == %s (test) # %s\n", format_src(*expr).c_str(),
					log_signal(ref), log_signal(test),
					std::string(text).c_str());
				ntests++;
			} else {
				log("%s: %s (ref) == %s (test) # %s\n", format_src(*expr).c_str(),
					log_signal(ref), log_signal(test),
					std::string(text).c_str());
				ntests++;
				nfailures++;
			}
		}));

		if (!nfailures)
			log("%d tests passed.\n", ntests);
		else
			log_error("%d out of %d tests failed.\n", nfailures, ntests);
	}
} TestSlangExprPass;

};
