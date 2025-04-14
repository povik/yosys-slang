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
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/CompilationDiags.h"
#include "slang/driver/Driver.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/text/Json.h"
#include "slang/util/Util.h"

#include "kernel/bitpattern.h"
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

namespace slang_frontend {

struct SynthesisSettings {
	std::optional<bool> dump_ast;
	std::optional<bool> no_proc;
	std::optional<bool> compat_mode;
	std::optional<bool> keep_hierarchy;
	std::optional<bool> best_effort_hierarchy;
	std::optional<bool> ignore_timing;
	std::optional<bool> ignore_initial;
	std::optional<bool> ignore_assertions;
	std::optional<int> unroll_limit_;
	std::optional<bool> extern_modules;
	std::optional<bool> no_implicit_memories;
	std::optional<bool> empty_blackboxes;
	std::optional<bool> ast_compilation_only;
	std::optional<bool> no_default_translate_off;
	bool disable_instance_caching = false;

	enum HierMode {
		NONE,
		BEST_EFFORT,
		ALL
	};

	HierMode hierarchy_mode()
	{
		if (keep_hierarchy.value_or(false))
			return ALL;
		if (best_effort_hierarchy.value_or(false))
			return BEST_EFFORT;
		return NONE;
	}

	int unroll_limit() {
		return unroll_limit_.value_or(4000);
	}

	void addOptions(slang::CommandLine &cmdLine) {
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
};

namespace RTLIL = Yosys::RTLIL;
namespace ID = Yosys::RTLIL::ID;
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

void crop_zero_mask(const RTLIL::SigSpec &mask, RTLIL::SigSpec &target)
{
	for (int i = mask.size() - 1; i >= 0; i--) {
		if (mask[i] == RTLIL::S0)
			target.remove(i, 1);
	}
}

};

#include "cases.h"
#include "memory.h"

namespace slang_frontend {

static Yosys::pool<RTLIL::SigBit> detect_possibly_unassigned_subset(Yosys::pool<RTLIL::SigBit> &signals, Case *rule, int level=0)
{
	Yosys::pool<RTLIL::SigBit> remaining = signals;
	bool debug = false;

	for (auto &action : rule->actions) {
		if (debug) {
			log_debug("%saction %s<=%s (mask %s)\n", std::string(level, ' ').c_str(),
					  log_signal(action.lvalue), log_signal(action.unmasked_rvalue), log_signal(action.mask));
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

		Yosys::pool<RTLIL::SigBit> new_remaining;
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

struct UpdateTiming {
	RTLIL::SigBit background_enable = RTLIL::S1;

	struct Sensitivity {
		RTLIL::SigBit signal;
		bool edge_polarity;
		const ast::TimingControl *ast_node;
	};
	std::vector<Sensitivity> triggers;

	bool implicit() const
	{
		return triggers.empty();
	}

	// extract trigger for side-effect cells like $print, $check
	void extract_trigger(NetlistContext &netlist, Yosys::Cell *cell, RTLIL::SigBit enable)
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
};

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

class UnrollLimitTracking {
	NetlistContext &netlist;
	int limit;
	int unrolling = 0;
	int unroll_counter = 0;
	Yosys::pool<const ast::Statement * YS_HASH_PTR_OPS> loops;
	bool error_issued = false;

public:
	UnrollLimitTracking(NetlistContext &netlist, int limit)
		: netlist(netlist), limit(limit) {}

	~UnrollLimitTracking() {
		log_assert(!unrolling);
	}

	void enter_unrolling() {
		if (!unrolling++) {
			unroll_counter = 0;
			error_issued = false;
			loops.clear();
		}
	}

	void exit_unrolling() {
		unrolling--;
		log_assert(unrolling >= 0);
	}

	bool unroll_tick(const ast::Statement *symbol) {
		if (error_issued)
			return false;

		loops.insert(symbol);

		if (++unroll_counter > limit) {
			auto &diag = netlist.add_diag(diag::UnrollLimitExhausted, symbol->sourceRange);
			diag << limit;
			for (auto other_loop : loops) {
				if (other_loop == symbol)
					continue;
				diag.addNote(diag::NoteLoopContributes, other_loop->sourceRange);
			}
			error_issued = true;
			return false;
		}

		return true;
	}
};

struct ProceduralVisitor : public ast::ASTVisitor<ProceduralVisitor, true, false>, public UnrollLimitTracking {
public:
	NetlistContext &netlist;
	EvalContext eval;
	UpdateTiming &timing;

	Yosys::pool<RTLIL::Wire *> seen_blocking_assignment;
	Yosys::pool<RTLIL::Wire *> seen_nonblocking_assignment;

	Case *root_case;
	Case *current_case;

	enum Mode {
		AlwaysProcedure,
		ContinuousAssign
	} mode;

	std::vector<RTLIL::Cell *> preceding_memwr;
	int effects_priority = 0;

	ProceduralVisitor(NetlistContext &netlist, UpdateTiming &timing, Mode mode)
			: UnrollLimitTracking(netlist, netlist.settings.unroll_limit()),
			  netlist(netlist), eval(netlist, *this), timing(timing), mode(mode) {
		eval.push_frame();

		root_case = new Case;
		current_case = root_case->add_switch({})->add_case({});
	}

	~ProceduralVisitor()
	{
		delete root_case;
	}

	void inherit_state(ProceduralVisitor &other)
	{
		log_assert(other.eval.frames.size() == 1);
		eval.frames[0].locals = other.eval.frames[0].locals;
		seen_blocking_assignment = other.seen_blocking_assignment;
		seen_nonblocking_assignment = other.seen_nonblocking_assignment;
		preceding_memwr = other.preceding_memwr;
		vstate = other.vstate;
	}

	void copy_case_tree_into(RTLIL::CaseRule &rule)
	{
		root_case->copy_into(&rule);
	}

	RTLIL::SigSpec all_driven()
	{
		RTLIL::SigSpec all_driven;
		for (auto pair : vstate.visible_assignments)
			all_driven.append(pair.first);
		all_driven.sort_and_unify();

		RTLIL::SigSpec all_driven_filtered;

		for (auto chunk : all_driven.chunks()) {
			log_assert(chunk.wire);
			if (!chunk.wire->get_bool_attribute(ID($nonstatic)))
				all_driven_filtered.append(chunk);
		}

		return all_driven_filtered;
	}

	// Return an enable signal for the current case node
	RTLIL::SigBit case_enable()
	{
		RTLIL::SigBit ret = netlist.canvas->addWire(netlist.new_id(), 1);
		root_case->aux_actions.emplace_back(ret, RTLIL::State::S0);
		current_case->aux_actions.emplace_back(ret, RTLIL::State::S1);
		return ret;
	}

	// For $check, $print cells
	void set_effects_trigger(RTLIL::Cell *cell)
	{
		timing.extract_trigger(netlist, cell, case_enable());
	}

	struct SwitchHelper {
		struct VariableState {
			using Map = Yosys::dict<RTLIL::SigBit, RTLIL::SigBit>;

			Map visible_assignments;
			Map revert;

			void set(RTLIL::SigSpec lhs, RTLIL::SigSpec value)
			{
				log_debug("VariableState.set: lhs=%s value=%s\n",
						  log_signal(lhs), log_signal(value));
				log_assert(lhs.size() == value.size());

				for (int i = 0; i < lhs.size(); i++) {
					RTLIL::SigBit bit = lhs[i];

					if (!revert.count(bit)) {
						if (visible_assignments.count(bit))
							revert[bit] = visible_assignments.at(bit);
						else
							revert[bit] = RTLIL::Sm;
					}

					visible_assignments[bit] = value[i];
				}
			}

			void save(Map &save)
			{
				revert.swap(save);
			}

			RTLIL::SigSig restore(Map &save)
			{
				RTLIL::SigSpec lreverted, rreverted;

				for (auto pair : revert)
					lreverted.append(pair.first);
				lreverted.sort();
				rreverted = lreverted;
				rreverted.replace(visible_assignments);

				for (auto pair : revert) {
					if (pair.second == RTLIL::Sm)
						visible_assignments.erase(pair.first);
					else
						visible_assignments[pair.first] = pair.second;
				}

				save.swap(revert);
				return {lreverted, rreverted};
			}
		};

		Case *parent;
		Case *&current_case;
		Switch *sw;
		VariableState &vstate;
		VariableState::Map save_map;
		std::vector<std::pair<Case *, RTLIL::SigSig>> branch_updates;
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
			branch_updates.push_back(std::make_pair(this_case, updates));
		}

		void branch(std::vector<RTLIL::SigSpec> compare,
					std::function<void()> f)
		{
			enter_branch(compare);
			f();
			exit_branch();
		}

		void finish(NetlistContext &netlist)
		{
			RTLIL::SigSpec updated_anybranch;
			for (auto &branch : branch_updates)
				updated_anybranch.append(branch.second.first);
			updated_anybranch.sort_and_unify();

			for (auto chunk : updated_anybranch.chunks()) {
				log_assert(chunk.wire);

				if (chunk.wire->has_attribute(ID($nonstatic)) \
						&& chunk.wire->attributes[ID($nonstatic)].as_int() > parent->level)
					continue;

				RTLIL::Wire *w = netlist.canvas->addWire(netlist.new_id(format_wchunk(chunk)), chunk.size());
				if (sw->statement)
					transfer_attrs(*sw->statement, w);
				RTLIL::SigSpec w_default = chunk;
				w_default.replace(vstate.visible_assignments);
				parent->aux_actions.push_back(RTLIL::SigSig(w, w_default));
				vstate.set(chunk, w);
			}

			for (auto &branch : branch_updates) {
				Case *rule = branch.first;
				RTLIL::SigSpec target = branch.second.first;
				RTLIL::SigSpec source = branch.second.second;
				int done = 0;
				for (auto chunk : target.chunks()) {
					if (chunk.wire->has_attribute(ID($nonstatic)) \
							&& chunk.wire->attributes[ID($nonstatic)].as_int() > parent->level) {
						done += chunk.size();
						continue;
					}

					RTLIL::SigSpec target_w = chunk;
					// get the wire (or some part of it) which we created up above
					target_w.replace(vstate.visible_assignments);
					rule->aux_actions.push_back(RTLIL::SigSig(target_w,
						source.extract(done, chunk.size())));
					done += chunk.size();
				}
			}

			finished = true;
		}
	};

	SwitchHelper::VariableState vstate;

	void do_assign(slang::SourceLocation loc, RTLIL::SigSpec lvalue, RTLIL::SigSpec unmasked_rvalue, RTLIL::SigSpec mask, bool blocking)
	{
		log_assert(lvalue.size() == unmasked_rvalue.size());
		log_assert(lvalue.size() == mask.size());

		crop_zero_mask(mask, lvalue);
		crop_zero_mask(mask, unmasked_rvalue);
		crop_zero_mask(mask, mask);

		// TODO: proper message on blocking/nonblocking mixing
		if (blocking) {
			for (auto bit : lvalue)
			if (bit.wire) {
				log_assert(!seen_nonblocking_assignment.count(bit.wire));
				seen_blocking_assignment.insert(bit.wire);
			}
		} else {
			for (auto bit : lvalue)
			if (bit.wire) {
				log_assert(!seen_blocking_assignment.count(bit.wire));
				seen_nonblocking_assignment.insert(bit.wire);
			}
		}

		current_case->actions.push_back(Case::Action{
			loc,
			lvalue,
			mask,
			unmasked_rvalue
		});

		RTLIL::SigSpec rvalue_background = lvalue;
		rvalue_background.replace(vstate.visible_assignments);

		RTLIL::SigSpec rvalue = netlist.Bwmux(rvalue_background, unmasked_rvalue, mask);
		vstate.set(lvalue, rvalue);
	}

	void do_simple_assign(slang::SourceLocation loc, RTLIL::SigSpec lvalue, RTLIL::SigSpec rvalue, bool blocking)
	{
		do_assign(loc, lvalue, rvalue, RTLIL::SigSpec(RTLIL::S1, rvalue.size()), blocking);
	}

	RTLIL::SigSpec substitute_rvalue(RTLIL::Wire *wire)
	{
		log_assert(wire);

		// We disallow mixing of blocking and non-blocking assignments to the same
		// variable from the same process. That simplifies the handling here.
		if (!seen_blocking_assignment.count(wire))
			return wire;

		RTLIL::SigSpec subed = wire;
		subed.replace(vstate.visible_assignments);
		return subed;
	}

	void assign_rvalue(const ast::AssignmentExpression &assign, RTLIL::SigSpec rvalue)
	{
		if (assign.timingControl && !netlist.settings.ignore_timing.value_or(false))
				netlist.add_diag(diag::GenericTimingUnsyn, assign.timingControl->sourceRange);

		bool blocking = !assign.isNonBlocking();
		const ast::Expression *raw_lexpr = &assign.left();
		RTLIL::SigSpec raw_mask = RTLIL::SigSpec(RTLIL::S1, rvalue.size()), raw_rvalue = rvalue;

		if (raw_lexpr->kind == ast::ExpressionKind::Streaming) {
			auto& stream_lexpr = raw_lexpr->as<ast::StreamingConcatenationExpression>();
			RTLIL::SigSpec lvalue = eval.streaming(stream_lexpr, true);
			ast_invariant(assign, rvalue.size() >= lvalue.size());
			do_simple_assign(assign.sourceRange.start(), lvalue,
							 rvalue.extract_end(rvalue.size() - lvalue.size()), blocking);
			return;
		} else if (raw_lexpr->kind == ast::ExpressionKind::SimpleAssignmentPattern) {
			// break down into individual assignments
			auto& pattern_lexpr = raw_lexpr->as<ast::SimpleAssignmentPatternExpression>();

			int nbits_remaining = rvalue.size();
			for (auto el : pattern_lexpr.elements()) {
				log_assert(el->kind == ast::ExpressionKind::Assignment);
				auto &inner_assign = el->as<ast::AssignmentExpression>();

				const ast::Expression *rsymbol = &inner_assign.right();
				while (rsymbol->kind == ast::ExpressionKind::Conversion)
					rsymbol = &rsymbol->as<ast::ConversionExpression>().operand();
				log_assert(rsymbol->kind == ast::ExpressionKind::EmptyArgument);
				log_assert(rsymbol->type->isBitstreamType());
				int relem_width = rsymbol->type->getBitstreamWidth();

				log_assert(nbits_remaining >= relem_width);
				RTLIL::SigSpec relem = rvalue.extract(nbits_remaining - relem_width, relem_width);
				nbits_remaining -= relem_width;

				assign_rvalue(inner_assign, eval.apply_nested_conversion(inner_assign.right(), relem));
			}

			log_assert(nbits_remaining == 0);
			return;
		}
		assign_rvalue_inner(assign, raw_lexpr, raw_rvalue, raw_mask, blocking);
	}

	void assign_rvalue_inner(const ast::AssignmentExpression &assign, const ast::Expression *raw_lexpr,
							 RTLIL::SigSpec raw_rvalue, RTLIL::SigSpec raw_mask, bool blocking)
	{
		ast_invariant(assign, raw_mask.size() == (int) raw_lexpr->type->getBitstreamWidth());
		ast_invariant(assign, raw_rvalue.size() == (int) raw_lexpr->type->getBitstreamWidth());

		bool finished_etching = false;
		bool memory_write = false;
		while (!finished_etching) {
			switch (raw_lexpr->kind) {
			case ast::ExpressionKind::RangeSelect:
				{
					auto &sel = raw_lexpr->as<ast::RangeSelectExpression>();
					Addressing addr(eval, sel);
					int wider_size = sel.value().type->getBitstreamWidth();
					raw_mask = addr.shift_up(raw_mask, false, wider_size);
					raw_rvalue = addr.shift_up(raw_rvalue, true, wider_size);
					raw_lexpr = &sel.value();
				}
				break;
			case ast::ExpressionKind::ElementSelect:
				{
					auto &sel = raw_lexpr->as<ast::ElementSelectExpression>();

					if (netlist.is_inferred_memory(sel.value())) {
						finished_etching = true;
						memory_write = true;
						break;
					}

					Addressing addr(eval, sel);
					raw_mask = addr.demux(raw_mask, sel.value().type->getBitstreamWidth());
					raw_rvalue = raw_rvalue.repeat(addr.range.width());
					raw_lexpr = &sel.value();
				}
				break;
			case ast::ExpressionKind::MemberAccess:
				{
					const auto &acc = raw_lexpr->as<ast::MemberAccessExpression>();
					if (acc.member.kind != ast::SymbolKind::Field) {
						finished_etching = true;
						break;
					}
					const auto &member = acc.member.as<ast::FieldSymbol>();
					if (member.randMode != ast::RandMode::None) {
						finished_etching = true;
						break;
					}

					int pad = acc.value().type->getBitstreamWidth() - acc.type->getBitstreamWidth() - member.bitOffset;
					raw_mask = {RTLIL::SigSpec(RTLIL::S0, pad), raw_mask, RTLIL::SigSpec(RTLIL::S0, member.bitOffset)};
					raw_rvalue = {RTLIL::SigSpec(RTLIL::Sx, pad), raw_rvalue, RTLIL::SigSpec(RTLIL::Sx, member.bitOffset)};
					raw_lexpr = &acc.value();
				}
				break;
			case ast::ExpressionKind::Concatenation:
				{
					const auto &concat = raw_lexpr->as<ast::ConcatenationExpression>();
					int base = raw_mask.size(), len;
					for (auto op : concat.operands()) {
						require(concat, op->type->isBitstreamType());
						base -= (len = op->type->getBitstreamWidth());
						log_assert(base >= 0);
						assign_rvalue_inner(assign, op, raw_rvalue.extract(base, len), raw_mask.extract(base, len), blocking);
					}
					log_assert(base == 0);
					return;
				}
				break;
			default:
				finished_etching = true;
				break;
			}
			log_assert(raw_mask.size() == (int) raw_lexpr->type->getBitstreamWidth());
			log_assert(raw_rvalue.size() == (int) raw_lexpr->type->getBitstreamWidth());
		}

		if (memory_write) {
			log_assert(raw_lexpr->kind == ast::ExpressionKind::ElementSelect);
			auto &sel = raw_lexpr->as<ast::ElementSelectExpression>();
			log_assert(netlist.is_inferred_memory(sel.value()));
			require(assign, !blocking);

			RTLIL::IdString id = netlist.id(sel.value().as<ast::NamedValueExpression>().symbol);
			RTLIL::Cell *memwr = netlist.canvas->addCell(netlist.new_id(), ID($memwr_v2));
			memwr->setParam(ID::MEMID, id.str());
			if (timing.implicit()) {
				memwr->setParam(ID::CLK_ENABLE, false);
				memwr->setParam(ID::CLK_POLARITY, false);
				memwr->setPort(ID::CLK, RTLIL::Sx);
			} else {
				require(assign, timing.triggers.size() == 1);
				auto& trigger = timing.triggers[0];
				memwr->setParam(ID::CLK_ENABLE, true);
				memwr->setParam(ID::CLK_POLARITY, trigger.edge_polarity);
				memwr->setPort(ID::CLK, trigger.signal);
			}
			int portid = netlist.emitted_mems[id].num_wr_ports++;
			memwr->setParam(ID::PORTID, portid);
			std::vector<RTLIL::State> mask(portid, RTLIL::S0);
			for (auto prev : preceding_memwr) {
				log_assert(prev->type == ID($memwr_v2));
				if (prev->getParam(ID::MEMID) == memwr->getParam(ID::MEMID)) {
					mask[prev->getParam(ID::PORTID).as_int()] = RTLIL::S1;
				}
			}
			memwr->setParam(ID::PRIORITY_MASK, mask);
			memwr->setPort(ID::EN, netlist.Mux(
				RTLIL::SigSpec(RTLIL::S0, raw_mask.size()), raw_mask,
				netlist.LogicAnd(case_enable(), timing.background_enable)));

			RTLIL::SigSpec addr = eval(sel.selector());

			memwr->setParam(ID::ABITS, addr.size());
			memwr->setPort(ID::ADDR, addr);
			memwr->setParam(ID::WIDTH, raw_rvalue.size());
			memwr->setPort(ID::DATA, raw_rvalue);
			preceding_memwr.push_back(memwr);
		} else {
			RTLIL::SigSpec lvalue = eval.lhs(*raw_lexpr);
			do_assign(assign.sourceRange.start(), lvalue, raw_rvalue, raw_mask, blocking);
		}
	}

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
		set_effects_trigger(cell);
		cell->setParam(ID::FLAVOR, flavor);
		cell->setParam(ID::FORMAT, std::string(""));
		cell->setParam(ID::ARGS_WIDTH, 0);
		cell->setParam(ID::PRIORITY, --effects_priority);
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

		eval.push_frame(subroutine);
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
				do_simple_assign(loc, eval.wire(*arg_symbols[i]), arg_in[i], true);
		}

		subroutine->getBody().visit(*this);

		for (int i = 0; i < (int) arg_symbols.size(); i++) {
			auto dir = arg_symbols[i]->direction;
			if (dir == ast::ArgumentDirection::Out || dir == ast::ArgumentDirection::InOut)
				arg_out.push_back(eval(*arg_symbols[i]));
			else
				arg_out.push_back({});
		}

		if (subroutine->returnValVar)
			ret = eval(*subroutine->returnValVar);

		eval.pop_frame();

		for (int i = 0; i < (int) arg_symbols.size(); i++) {
			const ast::Expression *arg = call.arguments()[i];
			auto dir = arg_symbols[i]->direction;

			if (dir == ast::ArgumentDirection::Out || dir == ast::ArgumentDirection::InOut)
				assign_rvalue(arg->as<ast::AssignmentExpression>(), arg_out[i]);
		}

		return ret;
	}

	void handle_display(const ast::CallExpression &call)
	{
		auto cell = netlist.canvas->addCell(netlist.new_id(), ID($print));
		transfer_attrs(call, cell);
		set_effects_trigger(cell);
		cell->parameters[ID::PRIORITY] = --effects_priority;
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
		blk.body.visit(*this);
	}

	void handle(const ast::StatementList &list)
	{
		RTLIL::Wire *disable = eval.frames.back().disable;
		std::vector<SwitchHelper> sw_stack;

		for (auto &stmt : list.list) {
			RTLIL::SigSpec disable_rv = disable != nullptr ? substitute_rvalue(disable) : RTLIL::S0;
			if (!disable_rv.is_fully_const()) {
				auto &b = sw_stack.emplace_back(current_case, vstate, disable_rv);
				b.sw->statement = stmt;
				b.enter_branch({RTLIL::S0});
				current_case->statement = stmt;

				// From a semantical POV the following is a no-op, but it allows us to
				// do more constant folding.
				do_simple_assign(slang::SourceLocation::NoLocation, disable, RTLIL::S0, true);
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
		SwitchHelper b(current_case, vstate, condition);
		b.sw->statement = &cond;

		b.branch({RTLIL::S1}, [&](){
			current_case->statement = &cond.ifTrue;
			cond.ifTrue.visit(*this);
		});

		if (cond.ifFalse) {
			b.branch({}, [&](){
				current_case->statement = &cond.ifTrue;
				cond.ifFalse->visit(*this);
			});
		}
		b.finish(netlist);

		// descend into an empty switch so we force action priority for follow-up statements
		current_case = current_case->add_switch({})->add_case({});
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
		SwitchHelper b(current_case, vstate,
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
				current_case->statement = item.stmt;
				item.stmt->visit(*this);
			});
		}

		if (stmt.defaultCase) {
			b.branch(std::vector<RTLIL::SigSpec>{}, [&]() {
				current_case->statement = stmt.defaultCase;
				stmt.defaultCase->visit(*this);
			});
		}
		b.finish(netlist);

		// descend into an empty switch so we force action priority for follow-up statements
		current_case = current_case->add_switch({})->add_case({});
	}

	RTLIL::Wire *add_nonstatic(RTLIL::IdString id, int width)
	{
		RTLIL::Wire *wire = netlist.canvas->addWire(id, width);
		wire->attributes[ID($nonstatic)] = current_case->level;
		return wire;
	}

	void handle(const ast::WhileLoopStatement &stmt) {
		RTLIL::Wire *break_ = add_nonstatic(netlist.new_id("break"), 1);
		do_simple_assign(stmt.sourceRange.start(), break_, RTLIL::S0, true);

		std::vector<SwitchHelper> sw_stack;
		enter_unrolling();
		while (true) {
			RTLIL::SigSpec cv = netlist.ReduceBool(eval(stmt.cond));
			RTLIL::SigSpec break_rv = substitute_rvalue(break_);
			RTLIL::SigSpec joint_break = netlist.LogicOr(netlist.LogicNot(cv), break_rv);

			if (!joint_break.is_fully_const()) {
				auto &b = sw_stack.emplace_back(current_case, vstate, joint_break);
				b.sw->statement = &stmt;
				b.enter_branch({RTLIL::S0});
				current_case->statement = &stmt.body;

				// From a semantical POV the following is a no-op, but it allows us to
				// do more constant folding.
				do_simple_assign(slang::SourceLocation::NoLocation, break_, RTLIL::S0, true);
			} else if (joint_break.as_bool()) {
				break;
			} else {
				log_assert(!joint_break.as_bool());
			}

			eval.push_frame(nullptr).break_ = break_;
			stmt.body.visit(*this);
			eval.pop_frame();

			if (!unroll_tick(&stmt))
				break;
		}
		exit_unrolling();

		for (auto it = sw_stack.rbegin(); it != sw_stack.rend(); it++) {
			it->exit_branch();
			it->finish(netlist);
		}

		current_case = current_case->add_switch({})->add_case({});
	}

	void handle(const ast::ForLoopStatement &stmt) {
		for (auto init : stmt.initializers)
			eval(*init);

		if (!stmt.stopExpr) {
			netlist.add_diag(diag::MissingStopCondition, stmt.sourceRange.start());
			return;
		}

		RTLIL::Wire *break_ = add_nonstatic(netlist.new_id("break"), 1);
		do_simple_assign(stmt.sourceRange.start(), break_, RTLIL::S0, true);

		std::vector<SwitchHelper> sw_stack;
		enter_unrolling();
		while (true) {
			RTLIL::SigSpec cv = netlist.ReduceBool(eval(*stmt.stopExpr));

			if (!cv.is_fully_const()) {
				auto &b = sw_stack.emplace_back(current_case, vstate, cv);
				b.sw->statement = &stmt;
				b.enter_branch({RTLIL::S1});
				current_case->statement = &stmt.body;
			} else if (!cv.as_bool()) {
				break;
			} else {
				log_assert(cv.as_bool());
			}

			eval.push_frame(nullptr).break_ = break_;
			stmt.body.visit(*this);
			eval.pop_frame();

			RTLIL::SigSpec break_rv = substitute_rvalue(break_);

			if (!break_rv.is_fully_const()) {
				auto &b = sw_stack.emplace_back(current_case, vstate, break_rv);
				b.sw->statement = &stmt;
				b.enter_branch({RTLIL::S0});
				current_case->statement = &stmt.body;
			} else if (break_rv.as_bool()) {
				break;
			} else {
				log_assert(!break_rv.as_bool());
			}

			for (auto step : stmt.steps)
				eval(*step);

			if (!unroll_tick(&stmt))
				break;
		}
		exit_unrolling();

		for (auto it = sw_stack.rbegin(); it != sw_stack.rend(); it++) {
			it->exit_branch();
			it->finish(netlist);
		}

		current_case = current_case->add_switch({})->add_case({});
	}

	void handle(const ast::EmptyStatement&) {}

	void init_nonstatic_variable(const ast::ValueSymbol &symbol) {
		RTLIL::Wire *target = eval.wire(symbol);
		log_assert(target);

		if (!target->width)
			return;

		RTLIL::SigSpec initval;
		if (symbol.getInitializer())
			initval = eval(*symbol.getInitializer());
		else
			initval = convert_const(symbol.getType().getDefaultValue());

		do_simple_assign(
			symbol.location,
			target,
			initval,
			true
		);
	}

	void handle(const ast::VariableSymbol &symbol) {
		if (symbol.lifetime != ast::VariableLifetime::Static) {
			eval.create_local(&symbol);
			init_nonstatic_variable(symbol);
		}
	}
	void handle(const ast::VariableDeclStatement &stmt) {
		stmt.symbol.visit(*this);
	}

	using Frame = EvalContext::Frame;

	void handle(const ast::BreakStatement &brk)
	{
		log_assert(!eval.frames.empty());
		auto &frame = eval.frames.back();
		log_assert(frame.kind == Frame::LoopBody);
		log_assert(frame.disable != nullptr && frame.break_ != nullptr);

		do_simple_assign(brk.sourceRange.start(), frame.disable, RTLIL::S1, true);
		do_simple_assign(brk.sourceRange.start(), frame.break_, RTLIL::S1, true);
	}

	void handle(const ast::ContinueStatement &brk)
	{
		log_assert(!eval.frames.empty());
		auto &frame = eval.frames.back();
		log_assert(frame.kind == Frame::LoopBody);
		log_assert(frame.disable != nullptr && frame.break_ != nullptr);

		do_simple_assign(brk.sourceRange.start(), frame.disable, RTLIL::S1, true);
	}

	void handle(const ast::ReturnStatement &stmt)
	{
		log_assert(!eval.frames.empty());
		auto it = eval.frames.end() - 1;
		for (; it != eval.frames.begin(); it--) {
			if (it->kind == Frame::FunctionBody)
				break;
		}
		log_assert(it != eval.frames.begin());
		int level = it - eval.frames.begin();

		auto subroutine = it->subroutine;
		log_assert(subroutine && subroutine->subroutineKind == ast::SubroutineKind::Function);
		log_assert(subroutine->returnValVar);

		if (stmt.expr) {
			do_simple_assign(stmt.sourceRange.start(), eval.wire(*subroutine->returnValVar),
							 eval(*stmt.expr), true);
		}

		// refetch the iterator (stack may have changed in the meantime)
		log_assert(level < (int) eval.frames.size());
		it = eval.frames.begin() + level;
		for (; it != eval.frames.end(); it++) {
			log_assert(it->disable != nullptr);
			do_simple_assign(stmt.sourceRange.start(), it->disable, RTLIL::S1, true);
		}
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

EvalContext::Frame &EvalContext::push_frame(const ast::SubroutineSymbol *subroutine)
{
	if (subroutine) {
		std::string hier = subroutine->getHierarchicalPath();
		log_debug("%s-> push (%s)\n", std::string(frames.size(), ' ').c_str(),
				  hier.c_str());
	} else {
		log_debug("%s-> push\n", std::string(frames.size(), ' ').c_str());
	}

	auto &frame = frames.emplace_back();
	frame.subroutine = subroutine;
	if (frames.size() == 1) {
		log_assert(!subroutine);
		frame.kind = Frame::Implicit;
	} else {
		frame.disable = procedural->add_nonstatic(netlist.new_id("disable"), 1);
		procedural->do_simple_assign(slang::SourceLocation::NoLocation,
									 frame.disable, RTLIL::S0, true);
		frame.kind = (subroutine != nullptr) ? Frame::FunctionBody : Frame::LoopBody;
	}
	return frame;
}

void EvalContext::create_local(const ast::Symbol *symbol)
{
	log_assert(procedural);
	log_assert(!frames.empty());

	{
		std::string hier = symbol->getHierarchicalPath();
		log_debug("%s- local (%s)\n", std::string(frames.size(), ' ').c_str(), hier.c_str());
	}

	log_assert(!frames.back().locals.count(symbol));
	auto &variable = symbol->as<ast::VariableSymbol>();
	log_assert(variable.lifetime == ast::VariableLifetime::Automatic);

	frames.back().locals[symbol] = procedural->add_nonstatic(netlist.new_id("local"),
												variable.getType().getBitstreamWidth());
}

void EvalContext::pop_frame()
{
	log_assert(!frames.empty());
	frames.pop_back();

	log_debug("%s<- pop\n", std::string(frames.size(), ' ').c_str());
}

RTLIL::Wire *EvalContext::wire(const ast::Symbol &symbol)
{
	if (ast::VariableSymbol::isKind(symbol.kind) &&
			symbol.as<ast::VariableSymbol>().lifetime == ast::VariableLifetime::Automatic) {
		for (auto it = frames.rbegin(); it != frames.rend(); it++) {
			if (it->locals.count(&symbol))
				return it->locals.at(&symbol);
		}
		ast_unreachable(symbol);
	} else {
		return netlist.wire(symbol);
	}
}

RTLIL::SigSpec EvalContext::lhs(const ast::Expression &expr)
{
	ast_invariant(expr, expr.kind != ast::ExpressionKind::Streaming);
	RTLIL::SigSpec ret;

	if (!expr.type->isFixedSize()) {
		auto &diag = netlist.add_diag(diag::FixedSizeRequired, expr.sourceRange);
		diag << expr.type->toString();
		goto error;
	}

	switch (expr.kind) {
	case ast::ExpressionKind::NamedValue:
	case ast::ExpressionKind::HierarchicalValue: // TODO: raise error if there's a boundary
		{
			const ast::Symbol &symbol = expr.as<ast::ValueExpressionBase>().symbol;
			if (netlist.is_inferred_memory(symbol)) {
				netlist.add_diag(diag::BadMemoryExpr, expr.sourceRange);
				goto error;
			}

			if (symbol.kind == ast::SymbolKind::ModportPort \
					&& !netlist.scopes_remap.count(symbol.getParentScope())) {
				ret = lhs(*symbol.as<ast::ModportPortSymbol>().getConnectionExpr());
				break;
			}

			ret = wire(symbol);
		}
		break;
	case ast::ExpressionKind::RangeSelect:
		{
			const ast::RangeSelectExpression &sel = expr.as<ast::RangeSelectExpression>();
			Addressing addr(netlist.eval, sel);
			RTLIL::SigSpec inner = lhs(sel.value());
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
			Addressing addr(*this, elemsel);
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
	default:
		netlist.add_diag(diag::UnsupportedLhs, expr.sourceRange);
		goto error;
	}

	if (0) {
	error:
		ret = netlist.canvas->addWire(netlist.new_id(), expr.type->getBitstreamWidth());
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
		RTLIL::SigSpec ret = lhs(assign.left());
		assert_nonstatic_free(ret);
		return ret;
	}

	while (rsymbol->kind == ast::ExpressionKind::Conversion)
		rsymbol = &rsymbol->as<ast::ConversionExpression>().operand();
	ast_invariant(assign, rsymbol->kind == ast::ExpressionKind::EmptyArgument);
	ast_invariant(assign, rsymbol->type->isBitstreamType());

	RTLIL::SigSpec ret = netlist.canvas->addWire(netlist.new_id(), rsymbol->type->getBitstreamWidth());
	netlist.GroupConnect(
		lhs(assign.left()),
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
			RTLIL::Wire *wire = this->wire(symbol);
			log_assert(wire);
			RTLIL::SigSpec value;
			if (procedural)
				value = procedural->substitute_rvalue(wire);
			else
				value = wire;
			assert_nonstatic_free(value);
			return value;
		}
		break;
	case ast::SymbolKind::Parameter:
		{
			auto &valsym = symbol.as<ast::ValueSymbol>();
			require(valsym, valsym.getInitializer());
			auto exprconst = valsym.getInitializer()->constant;
			require(valsym, exprconst && exprconst->isInteger());
			return convert_svint(exprconst->integer());
		}
		break;
	default:
		ast_unreachable(symbol);
	}
}

RTLIL::SigSpec EvalContext::streaming(ast::StreamingConcatenationExpression const &expr, bool in_lhs)
{
	require(expr, expr.isFixedSize());
	RTLIL::SigSpec cat;

	for (auto stream : expr.streams()) {
		require(*stream.operand, !stream.withExpr);
		auto& op = *stream.operand;
		RTLIL::SigSpec item;

		if (op.kind == ast::ExpressionKind::Streaming)
			item = streaming(op.as<ast::StreamingConcatenationExpression>(), in_lhs);
		else
			item = in_lhs ? lhs(*stream.operand) : (*this)(*stream.operand);

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

			if (unop.op == ast::UnaryOperator::Postincrement
					|| unop.op == ast::UnaryOperator::Preincrement) {
				require(expr, procedural != nullptr);
				procedural->do_simple_assign(expr.sourceRange.start(), lhs(unop.operand()),
					ret = netlist.Biop(ID($add), left, {RTLIL::S0, RTLIL::S1},
							 unop.operand().type->isSigned(), unop.operand().type->isSigned(),
							 left.size()), true);
				break;
			}

			if (unop.op == ast::UnaryOperator::Postdecrement
					|| unop.op == ast::UnaryOperator::Predecrement) {
				require(expr, procedural != nullptr);
				procedural->do_simple_assign(expr.sourceRange.start(), lhs(unop.operand()),
					ret = netlist.Biop(ID($sub), left, {RTLIL::S0, RTLIL::S1},
							 unop.operand().type->isSigned(), unop.operand().type->isSigned(),
							 left.size()), true);
				break;
			}

			bool invert = false;

			RTLIL::IdString type;
			switch (unop.op) {
			case ast::UnaryOperator::Minus: type = ID($neg); break;
			case ast::UnaryOperator::Plus: type = ID($pos); break;
			case ast::UnaryOperator::LogicalNot: type = ID($logic_not); break;
			case ast::UnaryOperator::BitwiseNot: type = ID($not); break;
			case ast::UnaryOperator::BitwiseOr: type = ID($reduce_or); break;
			case ast::UnaryOperator::BitwiseAnd: type = ID($reduce_and); break;
			case ast::UnaryOperator::BitwiseNand: type = ID($reduce_and); invert = true; break;
			case ast::UnaryOperator::BitwiseNor: type = ID($reduce_or); invert = true; break;
			case ast::UnaryOperator::BitwiseXor: type = ID($reduce_xor); break;
			case ast::UnaryOperator::BitwiseXnor: type = ID($reduce_xnor); break;
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
				RTLIL::SigSpec stream = streaming(stream_expr, false);

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
			Addressing addr(*this, sel);
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

			Addressing addr(*this, elemsel);
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
			require(expr, repl.count().constant); // TODO: message
			int reps = repl.count().constant->integer().as<int>().value(); // TODO: checking
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
				procedural->handle_display(call);
			} else if (call.isSystemCall()) {
				require(expr, call.getSubroutineName() == "$signed" || call.getSubroutineName() == "$unsigned");
				require(expr, call.arguments().size() == 1);
				ret = (*this)(*call.arguments()[0]);
			} else {
				const auto &subr = *std::get<0>(call.subroutine);
				if (procedural) {
					ret = procedural->handle_call(call);
				} else {
					require(subr, subr.subroutineKind == ast::SubroutineKind::Function);
					UpdateTiming implicit;
					ProceduralVisitor visitor(netlist, implicit, ProceduralVisitor::ContinuousAssign);
					visitor.eval.ignore_ast_constants = ignore_ast_constants;
					ret = visitor.handle_call(call);

					RTLIL::Process *proc = netlist.canvas->addProcess(netlist.new_id());
					transfer_attrs(call, proc);
					visitor.root_case->copy_into(&proc->root_case);
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

EvalContext::EvalContext(NetlistContext &netlist, ProceduralVisitor &procedural)
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
		: TimingPatternInterpretor((DiagnosticIssuer&) netlist),
		  queue(queue), netlist(netlist), settings(netlist.settings),
		  mem_detect(settings.no_implicit_memories.value_or(false), std::bind(&PopulateNetlist::should_dissolve, this, std::placeholders::_1)),
		  initial_eval(netlist, &netlist.compilation, netlist.canvas,
					   netlist.settings.ignore_timing.value_or(false)) {}

	void handle_comb_like_process(const ast::ProceduralBlockSymbol &symbol, const ast::Statement &body)
	{
		RTLIL::Process *proc = netlist.canvas->addProcess(netlist.new_id());
		transfer_attrs(body, proc);

		UpdateTiming implicit_timing;
		ProceduralVisitor visitor(netlist, implicit_timing, ProceduralVisitor::AlwaysProcedure);
		body.visit(visitor);

		RTLIL::SigSpec all_driven = visitor.all_driven();

		Yosys::pool<RTLIL::SigBit> dangling;
		if (symbol.procedureKind != ast::ProceduralBlockKind::AlwaysComb) {
			Yosys::pool<RTLIL::SigBit> driven_pool = {all_driven.begin(), all_driven.end()};
			dangling =
				detect_possibly_unassigned_subset(driven_pool, visitor.root_case);
		}

		RTLIL::SigSpec dangling_;
		for (auto bit : dangling)
			dangling_.append(bit);
		dangling_.sort_and_unify();

		// left-hand side and right-hand side of the connections to be made
		RTLIL::SigSpec cl, cr;
		RTLIL::SigSpec latch_driven;

		for (auto driven_bit : visitor.all_driven()) {
			if (!dangling.count(driven_bit)) {
				// No latch inferred
				cl.append(driven_bit);
				cr.append(visitor.vstate.visible_assignments.at(driven_bit));
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
			Yosys::dict<RTLIL::SigBit, RTLIL::SigSig> signaling;
			RTLIL::SigSpec enables;

			for (auto bit : latch_driven) {
				// TODO: create latches in groups
				RTLIL::SigBit en = netlist.canvas->addWire(netlist.new_id(), 1);
				RTLIL::SigBit staging = netlist.canvas->addWire(netlist.new_id(), 1);
				RTLIL::Cell *cell = netlist.canvas->addDlatch(netlist.new_id(), en,
														staging, bit, true);
				signaling[bit] = {en, staging};
				enables.append(en);
				transfer_attrs(symbol, cell);
			}

			visitor.root_case->aux_actions.push_back(
						{enables, RTLIL::SigSpec(RTLIL::S0, enables.size())});
			visitor.root_case->insert_latch_signaling(netlist, signaling);
		}

		visitor.root_case->copy_into(&proc->root_case);
		netlist.GroupConnect(cl, cr);
	}

	void handle_ff_process(const ast::ProceduralBlockSymbol &symbol,
						   const ast::SignalEventControl &clock,
						   std::vector<const ast::Statement *> prologue,
						   const ast::Statement &sync_body,
						   std::span<AsyncBranch> async)
	{
		log_assert(symbol.getBody().kind == ast::StatementKind::Timed);
		const auto &timed = symbol.getBody().as<ast::TimedStatement>();

		RTLIL::Process *proc = netlist.canvas->addProcess(netlist.new_id());
		transfer_attrs(timed.stmt, proc);

		UpdateTiming prologue_timing;
		{
			prologue_timing.triggers.push_back({netlist.eval(clock.expr), clock.edge == ast::EdgeKind::PosEdge, &clock});
			for (auto &abranch : async)	{
				RTLIL::SigSpec sig = netlist.eval(abranch.trigger);
				log_assert(sig.size() == 1);
				prologue_timing.triggers.push_back({sig, abranch.polarity, nullptr});
			}
		}
		ProceduralVisitor prologue_visitor(netlist, prologue_timing,
										   ProceduralVisitor::AlwaysProcedure);
		for (auto stmt : prologue)
			stmt->visit(prologue_visitor);
		prologue_visitor.copy_case_tree_into(proc->root_case);

		struct Aload {
			RTLIL::SigBit trigger;
			bool trigger_polarity;
			Yosys::dict<RTLIL::SigBit, RTLIL::SigBit> values;
			const ast::Statement *ast_node;
		};
		std::vector<Aload> aloads;
		RTLIL::SigSpec prior_branch_taken;

		for (auto &abranch : async) {
			RTLIL::SigSpec sig = netlist.eval(abranch.trigger);
			log_assert(sig.size() == 1);

			UpdateTiming branch_timing;
			RTLIL::SigSpec sig_depol = abranch.polarity ? sig : netlist.LogicNot(sig);
			branch_timing.background_enable = netlist.LogicAnd(netlist.LogicNot(prior_branch_taken), sig_depol);
			prior_branch_taken.append(sig_depol);

			ProceduralVisitor visitor(netlist, branch_timing, ProceduralVisitor::AlwaysProcedure);
			visitor.inherit_state(prologue_visitor);
			abranch.body.visit(visitor);
			visitor.copy_case_tree_into(proc->root_case);
			aloads.push_back({
				sig, abranch.polarity, visitor.vstate.visible_assignments, &abranch.body
			});
			// TODO: check for non-constant load values and warn about sim/synth mismatch
		}

		if (aloads.size() > 1) {
			netlist.add_diag(diag::AloadOne, timed.timing.sourceRange);
			return;
		}

		{
			UpdateTiming timing;
			timing.background_enable = netlist.LogicNot(prior_branch_taken);
			timing.triggers.push_back({netlist.eval(clock.expr), clock.edge == ast::EdgeKind::PosEdge, &clock});
			ProceduralVisitor visitor(netlist, timing, ProceduralVisitor::AlwaysProcedure);
			visitor.inherit_state(prologue_visitor);
			sync_body.visit(visitor);
			visitor.copy_case_tree_into(proc->root_case);

			RTLIL::SigSpec driven = visitor.all_driven();
			for (RTLIL::SigChunk driven_chunk : driven.chunks()) {
				log_assert(netlist.wire_hdl_types.count(driven_chunk.wire));

				RTLIL::SigSpec staging_chunk = driven_chunk;
				staging_chunk.replace(visitor.vstate.visible_assignments);

				RTLIL::Cell *cell;
				if (aloads.empty()) {
					for (auto [named_chunk, name] : generate_subfield_names(driven_chunk, netlist.wire_hdl_types.at(driven_chunk.wire))) {
						cell = netlist.canvas->addDff(netlist.canvas->uniquify("$driver$" + name),
												timing.triggers[0].signal,
												staging_chunk.extract(named_chunk.offset - driven_chunk.offset, named_chunk.width),
												named_chunk,
												timing.triggers[0].edge_polarity);
						transfer_attrs(symbol, cell);
					}
				} else if (aloads.size() == 1) {
					RTLIL::SigSpec aload_chunk = driven_chunk;
					aload_chunk.replace(aloads[0].values);

					RTLIL::SigSpec aldff_q;
					RTLIL::SigSpec dffe_q; // fallback

					for (int i = 0; i < driven_chunk.size(); i++) {
						if (aload_chunk[i] != RTLIL::SigSpec(driven_chunk)[i])
							aldff_q.append(RTLIL::SigSpec(driven_chunk)[i]);
						else
							dffe_q.append(RTLIL::SigSpec(driven_chunk)[i]);
					}

					if (!aldff_q.empty()) {
						for (auto driven_chunk2 : aldff_q.chunks())
						for (auto [named_chunk, name] : generate_subfield_names(driven_chunk2, netlist.wire_hdl_types.at(driven_chunk.wire))) {
							cell = netlist.canvas->addAldff(netlist.canvas->uniquify("$driver$" + name),
													timing.triggers[0].signal,
													aloads[0].trigger,
													staging_chunk.extract(named_chunk.offset - driven_chunk.offset, named_chunk.width),
													named_chunk,
													aload_chunk.extract(named_chunk.offset - driven_chunk.offset, named_chunk.width),
													timing.triggers[0].edge_polarity,
													aloads[0].trigger_polarity);
							transfer_attrs(symbol, cell);
						}
					}

					if (!dffe_q.empty()) {
						auto &diag = netlist.add_diag(diag::MissingAload, aloads[0].ast_node->sourceRange);
						diag << std::string(log_signal(dffe_q));
						diag.addNote(diag::NoteDuplicateEdgeSense, timed.timing.sourceRange);

						for (auto driven_chunk2 : dffe_q.chunks())
						for (auto [named_chunk, name] : generate_subfield_names(driven_chunk2, netlist.wire_hdl_types.at(driven_chunk.wire))) {
							cell = netlist.canvas->addDffe(netlist.canvas->uniquify("$driver$" + name),
													timing.triggers[0].signal,
													aloads[0].trigger,
													staging_chunk.extract(named_chunk.offset - driven_chunk.offset, named_chunk.width),
													named_chunk,
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

		RTLIL::SigSpec internal_signal;

		if (auto expr = port.getInternalExpr())
			internal_signal = netlist.eval.lhs(*expr);
		else
			internal_signal = netlist.wire(*port.internalSymbol);

		log_assert(internal_signal.size() == signal.size());
		assert_nonstatic_free(internal_signal);

		if (port.direction == ast::ArgumentDirection::Out) {
			netlist.canvas->connect(signal, internal_signal);
		} else if (port.direction == ast::ArgumentDirection::In) {
			netlist.canvas->connect(internal_signal, signal);
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
				cell->setParam(RTLIL::escape_id(std::string(symbol.name)), convert_const(symbol.getValue()));
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

					signal = netlist.eval.lhs(assign.left());
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
			RTLIL::SigSpec lvalue = netlist.eval.streaming(stream_lexpr, true);
			ast_invariant(expr, rvalue.size() >= lvalue.size());
			netlist.canvas->connect(lvalue, rvalue);
			return;
		}

		RTLIL::SigSpec lhs = netlist.eval.lhs(expr.left());
		assert_nonstatic_free(lhs);
		netlist.canvas->connect(lhs, rvalue);
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
		}, [&](auto&, const ast::InstanceSymbol&) {
			/* do not descend into other modules */
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

	void handle(const ast::StatementBlockSymbol &sym)
	{
		visitDefault(sym);
	}

	void handle(const ast::InstanceArraySymbol &sym)
	{
		visitDefault(sym);
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
	return RTLIL::escape_id(path.str());
}

RTLIL::Wire *NetlistContext::add_wire(const ast::ValueSymbol &symbol)
{
	auto w = canvas->addWire(id(symbol), symbol.getType().getBitstreamWidth());
	transfer_attrs(symbol, w);
	wire_hdl_types[w] = &symbol.getType();
	return w;
}

RTLIL::Wire *NetlistContext::wire(const ast::Symbol &symbol)
{
	RTLIL::Wire *wire = canvas->wire(id(symbol));
	if (!wire)
		wire_missing(*this, symbol);
	log_assert(wire);
	return wire;
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
}

static std::string expected_diagnostic;

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
		// TODO: move me elsewhere
		driver.diagEngine.setSeverity(slang::diag::MissingTimeScale, slang::DiagnosticSeverity::Ignored);
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
