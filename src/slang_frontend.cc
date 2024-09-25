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
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/driver/Driver.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/Json.h"
#include "slang/util/Util.h"

#include "kernel/bitpattern.h"
#include "kernel/fmt.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"

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
	std::optional<int> unroll_limit_;

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
		cmdLine.add("--unroll-limit", unroll_limit_,
		            "Set unrolling limit (default: 4000)", "<limit>");
	}
};

using Yosys::log;
using Yosys::log_error;
using Yosys::log_warning;
using Yosys::log_id;
using Yosys::log_signal;
using Yosys::ys_debug;
using Yosys::ceil_log2;

namespace RTLIL = Yosys::RTLIL;
namespace ID = Yosys::RTLIL::ID;
namespace ast = slang::ast;
namespace syntax = slang::syntax;
namespace parsing = slang::parsing;

ast::Compilation *global_compilation;
const slang::SourceManager *global_sourcemgr;
slang::DiagnosticEngine *global_diagengine;
slang::TextDiagnosticClient *global_diagclient;

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

template<typename T>
[[noreturn]] void unimplemented_(const T &obj, const char *file, int line, const char *condition)
{
	slang::JsonWriter writer;
	writer.setPrettyPrint(true);
	ast::ASTSerializer serializer(*global_compilation, writer);
	serializer.serialize(obj);
	std::cout << writer.view() << std::endl;
	auto loc = source_location(obj);
	log_assert(loc.start().buffer() == loc.end().buffer());
	std::string_view source_text = global_sourcemgr->getSourceText(loc.start().buffer());
	int col_no = global_sourcemgr->getColumnNumber(loc.start());
	const char *line_start = source_text.data() + loc.start().offset() - col_no + 1;
	const char *line_end = line_start;
	while (*line_end && *line_end != '\n' && *line_end != '\r') line_end++;
	std::cout << "Source line " << format_src(obj) << ": " << std::string_view(line_start, line_end) << std::endl;
	log_error("Feature unimplemented at %s:%d, see AST and code line dump above%s%s%s\n",
			  file, line, condition ? " (failed condition \"" : "", condition ? condition : "", condition ? "\")" : "");
}
#define require(obj, property) { if (!(property)) unimplemented_(obj, __FILE__, __LINE__, #property); }
#define unimplemented(obj) { slang_frontend::unimplemented_(obj, __FILE__, __LINE__, NULL); }
#define ast_invariant(obj, property) require(obj, property)

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

static const RTLIL::IdString module_type_id(const ast::InstanceSymbol &sym)
{
	require(sym, sym.isModule());
	std::string instance;
	sym.body.getHierarchicalPath(instance);
	if (instance == sym.body.name)
		return RTLIL::escape_id(std::string(sym.body.name));
	else
		return RTLIL::escape_id(std::string(sym.body.name) + "$" + instance);
}

static const RTLIL::Const convert_svint(const slang::SVInt &svint)
{
	RTLIL::Const ret;
	ret.bits.reserve(svint.getBitWidth());
	for (int i = 0; i < (int) svint.getBitWidth(); i++)
	switch (svint[i].value) {
	case 0: ret.bits.push_back(RTLIL::State::S0); break;
	case 1: ret.bits.push_back(RTLIL::State::S1); break;
	case slang::logic_t::X_VALUE: ret.bits.push_back(RTLIL::State::Sx); break;
	case slang::logic_t::Z_VALUE: ret.bits.push_back(RTLIL::State::Sz); break;
	}
	return ret;
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
		RTLIL::Const ret;
		// TODO: is this right?
		for (auto &el : constval.elements()) {
			auto piece = convert_const(el);
			ret.bits.insert(ret.bits.begin(), piece.bits.begin(), piece.bits.end());
		}
		log_assert(ret.size() == (int) constval.getBitstreamWidth());
		return ret;
	} else if (constval.isString()) {
		RTLIL::Const ret = convert_svint(constval.convertToInt().integer());
		ret.flags |= RTLIL::CONST_FLAG_STRING;
		return ret;
	} else if (constval.isNullHandle()) {
		return {};
	}

	log_abort();
}

template<typename T>
void transfer_attrs(T &from, RTLIL::AttrObject *to)
{
	auto src = format_src(from);
	if (!src.empty())
		to->attributes[Yosys::ID::src] = src;

	for (auto attr : global_compilation->getAttributes(from)) {
		require(*attr, attr->getValue().isInteger());
		to->attributes[id(attr->name)] = convert_svint(attr->getValue().integer());
	}
}


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
			RTLIL::Const pol;
			RTLIL::SigSpec trg_signals;
			for (auto trigger : triggers) {
				pol.bits.push_back(trigger.edge_polarity ? RTLIL::S1 : RTLIL::S0);
				trg_signals.append(trigger.signal);
			}
			params[ID::TRG_POLARITY] = pol;
			cell->setPort(ID::TRG, trg_signals);
		}
	}
};

RTLIL::SigBit inside_comparison(SignalEvalContext &eval, RTLIL::SigSpec left,
								const ast::Expression &expr)
{
	require(expr, !expr.type->isUnpackedArray());

	if (expr.kind == ast::ExpressionKind::ValueRange) {
		const auto& vexpr = expr.as<ast::ValueRangeExpression>();
		require(expr, vexpr.rangeKind == ast::ValueRangeKind::Simple);
		require(expr, vexpr.left().type == vexpr.right().type);
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

Yosys::pool<const ast::Symbol *> memory_candidates;

bool is_inferred_memory(const ast::Symbol &symbol)
{
	return memory_candidates.count(&symbol);
}

bool is_inferred_memory(const ast::Expression &expr)
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

class UnrollLimitTracking {
	const ast::Scope *diag_scope;
	int limit;
	int unrolling = 0;
	int unroll_counter = 0;
	Yosys::pool<const ast::Statement *, Yosys::hash_ptr_ops> loops;
	bool error_issued = false;

public:
	UnrollLimitTracking(const ast::Scope *diag_scope, int limit)
		: diag_scope(diag_scope), limit(limit) {}

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
			auto &diag = diag_scope->addDiag(diag::UnrollLimitExhausted, symbol->sourceRange);
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
	const ast::Scope *diag_scope;

	NetlistContext &netlist;
	SignalEvalContext eval;
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

	// TODO: revisit diag_scope
	ProceduralVisitor(NetlistContext &netlist, const ast::Scope *diag_scope, UpdateTiming &timing, Mode mode)
			: UnrollLimitTracking(diag_scope, netlist.settings.unroll_limit()),
			  diag_scope(diag_scope), netlist(netlist), eval(netlist, *this),
			  timing(timing), mode(mode) {
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
		RTLIL::SigBit ret = netlist.canvas->addWire(NEW_ID, 1);
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

				RTLIL::Wire *w = netlist.canvas->addWire(NEW_ID_SUFFIX(format_wchunk(chunk)), chunk.size());
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
		require(assign, !assign.timingControl || netlist.settings.ignore_timing.value_or(false));

		bool blocking = !assign.isNonBlocking();
		const ast::Expression *raw_lexpr = &assign.left();
		RTLIL::SigSpec raw_mask = RTLIL::SigSpec(RTLIL::S1, rvalue.size()), raw_rvalue = rvalue;

		if (raw_lexpr->kind == ast::ExpressionKind::Streaming) {
			auto& stream_lexpr = raw_lexpr->as<ast::StreamingConcatenationExpression>();
			RTLIL::SigSpec lvalue = eval.streaming(stream_lexpr, true);
			log_assert(rvalue.size() >= lvalue.size()); // should have been checked by slang
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
		log_assert(raw_mask.size() == (int) raw_lexpr->type->getBitstreamWidth());
		log_assert(raw_rvalue.size() == (int) raw_lexpr->type->getBitstreamWidth());

		bool finished_etching = false;
		bool memory_write = false;
		while (!finished_etching) {
			switch (raw_lexpr->kind) {
			case ast::ExpressionKind::RangeSelect:
				{
					auto &sel = raw_lexpr->as<ast::RangeSelectExpression>();
					Addressing addr(eval, sel);
					log_assert(addr.stride == (int) (sel.value().type->getBitstreamWidth() / addr.range.width()));
					int stride = sel.value().type->getBitstreamWidth() / addr.range.width();
					int wider_size = sel.value().type->getBitstreamWidth();
					if (stride == 1) {
						raw_mask = addr.shift_up(raw_mask, false, wider_size);
						raw_rvalue = addr.shift_up(raw_rvalue, true, wider_size);
					} else {
						raw_mask = addr.embed(raw_mask, wider_size, stride, RTLIL::S0);
						raw_rvalue = addr.embed(raw_rvalue, wider_size, stride, RTLIL::Sx);
					}
					raw_lexpr = &sel.value();
				}
				break;
			case ast::ExpressionKind::ElementSelect:
				{
					auto &sel = raw_lexpr->as<ast::ElementSelectExpression>();

					if (is_inferred_memory(sel.value())) {
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
					require(assign, acc.member.kind == ast::SymbolKind::Field);
					const auto &member = acc.member.as<ast::FieldSymbol>();
					require(acc, member.randMode == ast::RandMode::None);
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
			log_assert(is_inferred_memory(sel.value()));
			require(assign, !blocking);

			RTLIL::IdString id = netlist.id(sel.value().as<ast::NamedValueExpression>().symbol);
			RTLIL::Cell *memwr = netlist.canvas->addCell(NEW_ID, ID($memwr_v2));
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
			RTLIL::Const mask(RTLIL::S0, portid);
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
			unimplemented(stmt);
		}

		auto cell = netlist.canvas->addCell(NEW_ID, ID($check));
		set_effects_trigger(cell);
		cell->setParam(ID::FLAVOR, flavor);
		cell->setParam(ID::FORMAT, std::string(""));
		cell->setParam(ID::ARGS_WIDTH, 0);
		cell->setParam(ID::PRIORITY, --effects_priority);
		cell->setPort(ID::ARGS, {});
		cell->setPort(ID::A, netlist.ReduceBool(eval(stmt.cond)));
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
		auto cell = netlist.canvas->addCell(NEW_ID, ID($print));
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
		RTLIL::Wire *break_ = add_nonstatic(NEW_ID_SUFFIX("break"), 1);
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
			diag_scope->addDiag(diag::MissingStopCondition, stmt.sourceRange.start());
			return;
		}

		RTLIL::Wire *break_ = add_nonstatic(NEW_ID_SUFFIX("break"), 1);
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

	using Frame = SignalEvalContext::Frame;

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
		if (netlist.settings.ignore_timing.value_or(false))
			stmt.stmt.visit(*this);
		else
			unimplemented(stmt);
	}

	void handle(const ast::Statement &stmt)
	{
		unimplemented(stmt);
	}

	void handle(const ast::Expression &expr)
	{
		unimplemented(expr);
	}
};

SignalEvalContext::Frame &SignalEvalContext::push_frame(const ast::SubroutineSymbol *subroutine)
{
	if (subroutine) {
		std::string hier;
		subroutine->getHierarchicalPath(hier);
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
		frame.disable = procedural->add_nonstatic(NEW_ID_SUFFIX("disable"), 1);
		procedural->do_simple_assign(slang::SourceLocation::NoLocation,
									 frame.disable, RTLIL::S0, true);
		frame.kind = (subroutine != nullptr) ? Frame::FunctionBody : Frame::LoopBody;
	}
	return frame;
}

void SignalEvalContext::create_local(const ast::Symbol *symbol)
{
	log_assert(procedural);
	log_assert(!frames.empty());

	{
		std::string hier;
		symbol->getHierarchicalPath(hier);
		log_debug("%s- local (%s)\n", std::string(frames.size(), ' ').c_str(), hier.c_str());
	}

	log_assert(!frames.back().locals.count(symbol));
	auto &variable = symbol->as<ast::VariableSymbol>();
	log_assert(variable.lifetime == ast::VariableLifetime::Automatic);

	frames.back().locals[symbol] = procedural->add_nonstatic(NEW_ID_SUFFIX("local"),
												variable.getType().getBitstreamWidth());
}

void SignalEvalContext::pop_frame()
{
	log_assert(!frames.empty());
	frames.pop_back();

	log_debug("%s<- pop\n", std::string(frames.size(), ' ').c_str());
}

RTLIL::Wire *SignalEvalContext::wire(const ast::Symbol &symbol)
{
	if (ast::VariableSymbol::isKind(symbol.kind) &&
			symbol.as<ast::VariableSymbol>().lifetime == ast::VariableLifetime::Automatic) {
		for (auto it = frames.rbegin(); it != frames.rend(); it++) {
			if (it->locals.count(&symbol))
				return it->locals.at(&symbol);
		}
		require(symbol, false && "not found");
	} else {
		return netlist.wire(symbol);
	}
}

RTLIL::SigSpec SignalEvalContext::lhs(const ast::Expression &expr)
{
	log_assert(expr.kind != ast::ExpressionKind::Streaming);
	require(expr, expr.type->isFixedSize());
	RTLIL::SigSpec ret;

	switch (expr.kind) {
	case ast::ExpressionKind::NamedValue:
	case ast::ExpressionKind::HierarchicalValue: // TODO: raise error if there's a boundary
		{
			const ast::Symbol &symbol = expr.as<ast::ValueExpressionBase>().symbol;
			if (is_inferred_memory(symbol)) {
				// TODO: scope
				netlist.realm.addDiag(diag::BadMemoryExpr, expr.sourceRange);
				ret = netlist.canvas->addWire(NEW_ID, expr.type->getBitstreamWidth());
				break;
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
		unimplemented(expr);
		break;
	}

	log_assert(expr.type->isFixedSize());
	log_assert(ret.size() == (int) expr.type->getBitstreamWidth());
	return ret;
}

RTLIL::SigSpec SignalEvalContext::connection_lhs(ast::AssignmentExpression const &assign)
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
	log_assert(rsymbol->kind == ast::ExpressionKind::EmptyArgument);
	log_assert(rsymbol->type->isBitstreamType());

	RTLIL::SigSpec ret = netlist.canvas->addWire(NEW_ID, rsymbol->type->getBitstreamWidth());
	netlist.GroupConnect(
		lhs(assign.left()),
		apply_nested_conversion(assign.right(), ret)
	);
	return ret;
}

RTLIL::SigSpec SignalEvalContext::operator()(ast::Symbol const &symbol)
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
		unimplemented(symbol);
	}
}

RTLIL::SigSpec SignalEvalContext::streaming(ast::StreamingConcatenationExpression const &expr, bool in_lhs)
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

RTLIL::SigSpec SignalEvalContext::apply_conversion(const ast::ConversionExpression &conv, RTLIL::SigSpec op)
{
	const ast::Type &from = conv.operand().type->getCanonicalType();
	const ast::Type &to = conv.type->getCanonicalType();

	log_assert(op.size() == from.getBitstreamWidth());

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

RTLIL::SigSpec SignalEvalContext::apply_nested_conversion(const ast::Expression &expr, RTLIL::SigSpec op)
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

RTLIL::SigSpec SignalEvalContext::operator()(ast::Expression const &expr)
{
	log_assert(expr.kind != ast::ExpressionKind::Streaming);
	require(expr, expr.type->isVoid() || expr.type->isFixedSize());
	RTLIL::Module *mod = netlist.canvas;
	RTLIL::SigSpec ret;
	size_t repl_count;

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
			require(expr, procedural != nullptr);
			require(expr, !assign.timingControl || netlist.settings.ignore_timing.value_or(false));
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
			if (is_inferred_memory(symbol)) {
				// TODO: scope
				netlist.realm.addDiag(diag::BadMemoryExpr, expr.sourceRange);
				ret = netlist.canvas->addWire(NEW_ID, expr.type->getBitstreamWidth());
				break;
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
			case ast::UnaryOperator::LogicalNot: type = ID($logic_not); break;
			case ast::UnaryOperator::BitwiseNot: type = ID($not); break;
			case ast::UnaryOperator::BitwiseOr: type = ID($reduce_or); break;
			case ast::UnaryOperator::BitwiseAnd: type = ID($reduce_and); break;
			case ast::UnaryOperator::BitwiseNand: type = ID($reduce_and); invert = true; break;
			case ast::UnaryOperator::BitwiseNor: type = ID($reduce_or); invert = true; break;
			case ast::UnaryOperator::BitwiseXor: type = ID($reduce_xor); break;
			case ast::UnaryOperator::BitwiseXnor: type = ID($reduce_xnor); break;
			default:
				unimplemented(unop);
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
			//case ast::BinaryOperator::WildcardEquality;
			//case ast::BinaryOperator::WildcardInequality;
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
				unimplemented(biop);
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
				log_assert(to.isBitstreamType());

				// evaluate the bitstream
				auto &stream_expr = conv.operand().as<ast::StreamingConcatenationExpression>();
				RTLIL::SigSpec stream = streaming(stream_expr, false);

				// pad to fit target size
				log_assert(stream.size() <= expr.type->getBitstreamWidth());
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
			if (addr.stride == 1)		
				ret = addr.shift_down((*this)(sel.value()), sel.type->getBitstreamWidth());
			else
				ret = addr.extract((*this)(sel.value()), sel.type->getBitstreamWidth());
		}
		break;
	case ast::ExpressionKind::ElementSelect:
		{
			const ast::ElementSelectExpression &elemsel = expr.as<ast::ElementSelectExpression>();

			if (is_inferred_memory(elemsel.value())) {
				int width = elemsel.type->getBitstreamWidth();
				RTLIL::IdString id = netlist.id(elemsel.value()
										.as<ast::NamedValueExpression>().symbol);
				RTLIL::Cell *memrd = netlist.canvas->addCell(NEW_ID, ID($memrd_v2));
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
				ret = netlist.canvas->addWire(NEW_ID, width);
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

			ret = mod->Mux(NEW_ID,
				(*this)(ternary.right()),
				(*this)(ternary.left()),
				mod->ReduceBool(NEW_ID, (*this)(*(ternary.conditions[0].expr)))
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
					// TODO: better scope here
					ProceduralVisitor visitor(netlist, nullptr, implicit, ProceduralVisitor::ContinuousAssign);
					visitor.eval.ignore_ast_constants = ignore_ast_constants;
					ret = visitor.handle_call(call);

					RTLIL::Process *proc = netlist.canvas->addProcess(NEW_ID);
					transfer_attrs(call, proc);
					visitor.root_case->copy_into(&proc->root_case);	
				}
			}
		}
		break;
	case ast::ExpressionKind::LValueReference:
		log_assert(lvalue != nullptr);
		ret = (*this)(*lvalue);
		break;
	default:
		unimplemented(expr);
	}

done:
	log_assert(ret.size() == (int) expr.type->getBitstreamWidth());
	return ret;
}

RTLIL::SigSpec SignalEvalContext::eval_signed(ast::Expression const &expr)
{
	require(expr, expr.type);

	if (expr.type->isNumeric() && !expr.type->isSigned())
		return {RTLIL::S0, (*this)(expr)};
	else
		return (*this)(expr);
}

SignalEvalContext::SignalEvalContext(NetlistContext &netlist)
	: netlist(netlist), procedural(nullptr),
	  const_(ast::ASTContext(netlist.compilation.getRoot(), ast::LookupLocation::max))
{
}

SignalEvalContext::SignalEvalContext(NetlistContext &netlist, ProceduralVisitor &procedural)
	: netlist(netlist), procedural(&procedural),
	  const_(ast::ASTContext(netlist.compilation.getRoot(), ast::LookupLocation::max))
{
}

struct PopulateNetlist : public TimingPatternInterpretor, public ast::ASTVisitor<PopulateNetlist, true, false> {
public:
	NetlistContext &netlist;
	SynthesisSettings &settings;
	std::vector<NetlistContext> deferred_modules;

	struct InitialEvalVisitor : SlangInitial::EvalVisitor {
		RTLIL::Module *mod;
		int print_priority;

		InitialEvalVisitor(ast::Compilation *compilation, RTLIL::Module *mod, bool ignore_timing=false)
			: SlangInitial::EvalVisitor(compilation, ignore_timing), mod(mod), print_priority(0) {}

		void handleDisplay(const slang::ast::CallExpression &call, const std::vector<slang::ConstantValue> &args) {
			auto cell = mod->addCell(NEW_ID, ID($print));
			cell->parameters[Yosys::ID::TRG_ENABLE] = true;
			cell->parameters[Yosys::ID::TRG_WIDTH] = 0;
			cell->parameters[Yosys::ID::TRG_POLARITY] = {};
			cell->parameters[Yosys::ID::PRIORITY] = print_priority--;
			cell->setPort(Yosys::ID::EN, RTLIL::S1);
			cell->setPort(Yosys::ID::TRG, {});
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
					unimplemented(*arg_expr);
				}
				fmt_args.push_back(fmt_arg);	
			}
			Yosys::Fmt fmt = {};
			// TODO: default_base is subroutine dependent, final newline is $display-only
			fmt.parse_verilog(fmt_args, /* sformat_like */ false, /* default_base */ 10,
							  std::string{call.getSubroutineName()}, mod->name);
			fmt.append_literal("\n");
			fmt.emit_rtlil(cell);
			transfer_attrs(call, cell);
		}
	} initial_eval;

	PopulateNetlist(NetlistContext &netlist)
		: netlist(netlist), settings(netlist.settings), initial_eval(&netlist.compilation, netlist.canvas, netlist.settings.ignore_timing.value_or(false)) {}

	void handle_comb_like_process(const ast::ProceduralBlockSymbol &symbol, const ast::Statement &body)
	{
		const ast::Scope *scope = symbol.getParentScope();

		RTLIL::Process *proc = netlist.canvas->addProcess(NEW_ID);
		transfer_attrs(body, proc);

		UpdateTiming implicit_timing;
		ProceduralVisitor visitor(netlist, scope, implicit_timing, ProceduralVisitor::AlwaysProcedure);
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
				auto &diag = scope->addDiag(diag::LatchNotInferred, symbol.location);
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
				RTLIL::SigBit en = netlist.canvas->addWire(NEW_ID, 1);
				RTLIL::SigBit staging = netlist.canvas->addWire(NEW_ID, 1);
				RTLIL::Cell *cell = netlist.canvas->addDlatch(NEW_ID, en,
														staging, bit, true);
				signaling[bit] = {en, staging};
				enables.append(en);
				transfer_attrs(symbol, cell);
			}

			visitor.root_case->aux_actions.push_back(
						{enables, RTLIL::SigSpec(RTLIL::S0, enables.size())});
			visitor.root_case->insert_latch_signaling(scope, signaling);
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
		const ast::Scope *scope = symbol.getParentScope();

		RTLIL::Process *proc = netlist.canvas->addProcess(NEW_ID);
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
		ProceduralVisitor prologue_visitor(netlist, symbol.getParentScope(), prologue_timing,
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

			ProceduralVisitor visitor(netlist, scope, branch_timing, ProceduralVisitor::AlwaysProcedure);
			visitor.inherit_state(prologue_visitor);
			abranch.body.visit(visitor);
			visitor.copy_case_tree_into(proc->root_case);
			aloads.push_back({
				sig, abranch.polarity, visitor.vstate.visible_assignments, &abranch.body
			});
			// TODO: check for non-constant load values and warn about sim/synth mismatch
		}

		require(symbol, aloads.size() <= 1);
		{
			UpdateTiming timing;
			timing.background_enable = netlist.LogicNot(prior_branch_taken);
			timing.triggers.push_back({netlist.eval(clock.expr), clock.edge == ast::EdgeKind::PosEdge, &clock});
			ProceduralVisitor visitor(netlist, scope, timing, ProceduralVisitor::AlwaysProcedure);
			visitor.inherit_state(prologue_visitor);
			sync_body.visit(visitor);
			visitor.copy_case_tree_into(proc->root_case);

			RTLIL::SigSpec driven = visitor.all_driven();
			for (RTLIL::SigSpec driven_chunk : driven.chunks()) {
				RTLIL::SigSpec staging_chunk = driven_chunk;
				staging_chunk.replace(visitor.vstate.visible_assignments);

				RTLIL::Cell *cell;
				if (aloads.empty()) {
					cell = netlist.canvas->addDff(NEW_ID,
											timing.triggers[0].signal, staging_chunk, driven_chunk,
											timing.triggers[0].edge_polarity);
					transfer_attrs(symbol, cell);
				} else if (aloads.size() == 1) {
					RTLIL::SigSpec aload_chunk = driven_chunk;
					aload_chunk.replace(aloads[0].values);

					RTLIL::SigSpec aldff_d, aldff_q, aldff_aload;
					RTLIL::SigSpec dffe_d, dffe_q; // fallback

					for (int i = 0; i < driven_chunk.size(); i++) {
						if (aload_chunk[i] != driven_chunk[i]) {
							aldff_d.append(staging_chunk[i]);
							aldff_q.append(driven_chunk[i]);
							aldff_aload.append(aload_chunk[i]);
						} else {
							dffe_d.append(staging_chunk[i]);
							dffe_q.append(driven_chunk[i]);
						}
					}

					if (!aldff_q.empty()) {
						cell = netlist.canvas->addAldff(NEW_ID,
												timing.triggers[0].signal, aloads[0].trigger,
												aldff_d, aldff_q, aldff_aload,
												timing.triggers[0].edge_polarity, aloads[0].trigger_polarity);
						transfer_attrs(symbol, cell);
					}

					if (!dffe_q.empty()) {
						auto &diag = scope->addDiag(diag::MissingAload, aloads[0].ast_node->sourceRange);
						diag << std::string(log_signal(dffe_q));
						diag.addNote(diag::NoteDuplicateEdgeSense, timed.timing.sourceRange);

						cell = netlist.canvas->addDffe(NEW_ID,
												timing.triggers[0].signal, aloads[0].trigger,
												dffe_d, dffe_q,
												timing.triggers[0].edge_polarity, !aloads[0].trigger_polarity);
						transfer_attrs(symbol, cell);
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
		if (result != ast::Statement::EvalResult::Success) {
			for (auto& diag : initial_eval.context.getAllDiagnostics())
    			global_diagengine->issue(diag);
			auto str = global_diagclient->getString();
			log_error("Failed to execute initial block\n%s\n",
					  str.c_str());
		}
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

		if (!sym.internalSymbol) {
			// This can happen in case of a compilation error.
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

		unimplemented(sym);
	}

	void inline_port_connection(const ast::PortSymbol &port, RTLIL::SigSpec signal)
	{
		require(port, !port.isNullPort);
		RTLIL::SigSpec internal_signal;

		if (auto expr = port.getInternalExpr()) 
			internal_signal = netlist.eval.lhs(*expr);
		else
			internal_signal = netlist.wire(*port.internalSymbol);

		log_assert(internal_signal.size() == signal.size());
		assert_nonstatic_free(internal_signal);

		require(port, port.direction == ast::ArgumentDirection::Out ||
					  port.direction == ast::ArgumentDirection::In);

		if (port.direction == ast::ArgumentDirection::Out)
			netlist.canvas->connect(signal, internal_signal);
		else
			netlist.canvas->connect(internal_signal, signal);
	}

	void handle(const ast::InstanceSymbol &sym)
	{
		bool should_dissolve;

		switch (settings.hierarchy_mode()) {
		case SynthesisSettings::NONE:
			should_dissolve = true;
			break;
		case SynthesisSettings::BEST_EFFORT: {
				should_dissolve = false;
				for (auto *conn : sym.getPortConnections()) {
					switch (conn->port.kind) {
					case ast::SymbolKind::Port:
					case ast::SymbolKind::MultiPort:
						break;
					case ast::SymbolKind::InterfacePort:
						if (!conn->getIfaceConn().second)
							should_dissolve = true;
						break;
					default:
						should_dissolve = true;
						break;
					}
				}

				if (!sym.isModule())
					should_dissolve = true;

				break;
			}
		case SynthesisSettings::ALL:
			should_dissolve = false;
			break;
		}

		if (sym.isInterface())
			should_dissolve = true;

		if (should_dissolve) {
			sym.body.visit(*this);

			for (auto *conn : sym.getPortConnections()) {
				if (!conn->getExpression())
					continue;
				auto &expr = *conn->getExpression();

				RTLIL::SigSpec signal;
				if (expr.kind == ast::ExpressionKind::Assignment) {
					auto &assign = expr.as<ast::AssignmentExpression>();
					ast::Expression const *right = &assign.right();

					signal = netlist.eval.lhs(assign.left());
					assert_nonstatic_free(signal);

					while (right->kind == ast::ExpressionKind::Conversion) {
						auto &conv = right->as<ast::ConversionExpression>();

						// assign converted value to the target
						RTLIL::Wire *temporary = netlist.canvas->addWire(NEW_ID,
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
					log_abort();
				}
			}
		} else {
			if (sym.isModule()) {
				deferred_modules.emplace_back(netlist, sym);
				NetlistContext &submodule = deferred_modules.back();

				RTLIL::Cell *cell = netlist.canvas->addCell(netlist.id(sym), module_type_id(sym));
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
					case ast::SymbolKind::InterfacePort: {
						require(sym, conn->getIfaceConn().second != nullptr && "must be a modport");
						const ast::ModportSymbol &modport = *conn->getIfaceConn().second;
						submodule.scopes_remap[&static_cast<const ast::Scope&>(modport)] =
																		submodule.id(conn->port).str();

						modport.visit(ast::makeVisitor([&](auto&, const ast::ModportPortSymbol &port) {
							auto wire = submodule.add_wire(port);
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
							default:
								unimplemented(port);
							}
							ast_invariant(port, port.internalSymbol);
							if (netlist.scopes_remap.count(&modport))
								cell->setPort(wire->name, netlist.wire(port));
							else
								cell->setPort(wire->name, netlist.wire(*port.internalSymbol));
						}));
						break;
					}
					default:
						unimplemented(conn->port);
					}
					
				}
				transfer_attrs(sym, cell);
			} else {
				unimplemented(sym);
			}
		}
	}

	void handle(const ast::ContinuousAssignSymbol &sym)
	{
		require(sym, !sym.getDelay() || settings.ignore_timing.value_or(false));
		const ast::AssignmentExpression &expr = sym.getAssignment().as<ast::AssignmentExpression>();
		ast_invariant(expr, !expr.timingControl);
		RTLIL::SigSpec lhs = netlist.eval.lhs(expr.left());
		assert_nonstatic_free(lhs);
		netlist.canvas->connect(lhs, netlist.eval(expr.right()));		
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

	void collect_flattened_trivia(std::vector<parsing::Trivia> &collect, parsing::Token token)
	{
		for (auto trivia : token.trivia()) {
			if (trivia.syntax())
				collect_flattened_trivia(collect, trivia.syntax()->getFirstToken());
			else
				collect.push_back(trivia);
		}
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

			if (is_inferred_memory(sym)) {
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
		}, [&](auto&, const ast::InstanceSymbol&) {
			/* do not descend into other modules */
		}, [&](auto& visitor, const ast::GenerateBlockSymbol& sym) {
			/* stop at uninstantiated generate blocks */
			if (sym.isUninstantiated)
				return;
			visitor.visitDefault(sym);
		}));
	}

	void handle(const ast::InstanceBodySymbol &sym)
	{
		add_internal_wires(sym);

		auto varinit = ast::makeVisitor([&](auto&, const ast::VariableSymbol &sym) {
			slang::ConstantValue initval = nullptr;
			if (sym.getInitializer())
				initval = sym.getInitializer()->eval(initial_eval.context);
			initial_eval.context.createLocal(&sym, initval);
		}, [&](auto&, const ast::InstanceSymbol&) {
			/* do not descend into other modules */
		}, [&](auto&, const ast::ProceduralBlockSymbol&) {
			/* do not descend into procedural blocks */
		}, [&](auto& visitor, const ast::GenerateBlockSymbol& sym) {
			/* stop at uninstantiated generate blocks */
			if (sym.isUninstantiated)
				return;
			visitor.visitDefault(sym);
		});
		sym.visit(varinit);

		visitDefault(sym);

		// now transfer the initializers from variables onto RTLIL wires
		auto inittransfer = ast::makeVisitor([&](auto&, const ast::VariableSymbol &sym) {
			if (sym.getType().isFixedSize() && sym.lifetime == ast::VariableLifetime::Static) {
				auto storage = initial_eval.context.findLocal(&sym);
				log_assert(storage);
				auto const_ = convert_const(*storage);
				if (!const_.is_fully_undef()) {
					auto wire = netlist.wire(sym);
					log_assert(wire);
					wire->attributes[RTLIL::ID::init] = const_;
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
		});
		sym.visit(inittransfer);

		for (auto& diag : initial_eval.context.getAllDiagnostics())
        	global_diagengine->issue(diag);
		auto str = global_diagclient->getString();
		if (global_diagengine->getNumErrors())
			log_error("%s", str.c_str());
		else
			log("%s", str.c_str());
		global_diagclient->clear();
	}

	void handle(const ast::UninstantiatedDefSymbol &sym)
	{
		require(sym, !sym.isChecker());
		require(sym, sym.paramExpressions.empty());

		RTLIL::Cell *cell = netlist.canvas->addCell(netlist.id(sym),
												id(sym.definitionName));
		transfer_attrs(sym, cell);

		auto port_names = sym.getPortNames();
		auto port_conns = sym.getPortConnections();

		log_assert(port_names.size() == port_conns.size());
		for (int i = 0; i < (int) port_names.size(); i++) {
			require(sym, !port_names[i].empty());
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
            for (size_t i = 0; i < inst.arrayPath.size(); i++)
            	s << "[" << inst.arrayPath[i] << "]";
		}

		s << ".";
	} else if (!symbol->name.empty()) {
		s << symbol->name << ".";
	} else if (symbol->kind == ast::SymbolKind::StatementBlock) {
		s << "$" << (int) symbol->getIndex() << ".";
	}
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
	return w;
}

RTLIL::Wire *NetlistContext::wire(const ast::Symbol &symbol)
{
	RTLIL::Wire *wire = canvas->wire(id(symbol));
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
	canvas = design->addModule(module_type_id(instance));
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
			std::vector<char *> c_args;
			for (auto arg : args) {
				char *c = new char[arg.size() + 1];
				strcpy(c, arg.c_str());
				c_args.push_back(c);
			}
			if (!driver.parseCommandLine(c_args.size(), &c_args[0]))
				log_cmd_error("Bad command\n");
		}
		if (!driver.processOptions())
			log_cmd_error("Bad command\n");

		if (settings.compat_mode.value_or(false)) {
			driver.diagEngine.setSeverity(diag::SignalSensitivityAmbiguous,
										  slang::DiagnosticSeverity::Warning);
		}

		try {
			if (!driver.parseAllSources())
				log_error("Parsing failed\n");

			auto compilation = driver.createCompilation();

			if (settings.dump_ast.value_or(false)) {
				slang::JsonWriter writer;
				writer.setPrettyPrint(true);
				ast::ASTSerializer serializer(*compilation, writer);
				serializer.serialize(compilation->getRoot());
				std::cout << writer.view() << std::endl;
			}

			auto elab = ast::makeVisitor([&](auto& visitor, const ast::InstanceBodySymbol &body) {
				compilation->forceElaborate(body);
				visitor.visitDefault(body);
			});
			for (auto instance : compilation->getRoot().topInstances)
				instance->visit(elab);

			if (compilation->hasIssuedErrors()) {
				if (!driver.reportCompilation(*compilation, /* quiet */ false))
					log_error("Compilation failed\n");
			}

			global_compilation = &(*compilation);
			global_sourcemgr = compilation->getSourceManager();
			global_diagengine = &driver.diagEngine;
			global_diagclient = driver.diagClient.get();
			global_diagclient->clear();

			InferredMemoryDetector mem_detect;
			compilation->getRoot().visit(mem_detect);
			memory_candidates = mem_detect.memory_candidates;

			{
				std::vector<NetlistContext> queue;
				for (auto instance : compilation->getRoot().topInstances) {
					queue.emplace_back(design, settings, *compilation, *instance);
					queue.back().canvas->attributes[ID::top] = 1;
				}

				for (int i = 0; i < (int) queue.size(); i++) {
					NetlistContext &netlist = queue[i];
					PopulateNetlist populate(netlist);
					netlist.realm.visit(populate);
					std::move(populate.deferred_modules.begin(),
						populate.deferred_modules.end(), std::back_inserter(queue));
				}
			}

			if (!driver.reportCompilation(*compilation, /* quiet */ false))
				log_error("Compilation failed\n");
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

				Const init = wire->attributes[ID::init];
				while (init.size() < wire->width)
					init.bits.push_back(RTLIL::Sx);

				for (int i = 0; i < wire->width; i++)
				if (!driven.check(SigBit(wire, i)) && (init[i] == RTLIL::S1 || init[i] == RTLIL::S0))
					module->connect(SigBit(wire, i), init[i]);
			}
		}
	}
} UndrivenPass;

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

		//if (compilation->hasIssuedErrors()) {
			if (!driver.reportCompilation(*compilation, /* quiet */ false))
				log_error("Compilation failed\n");
		//}

		global_compilation = &(*compilation);
		global_sourcemgr = compilation->getSourceManager();
		global_diagengine = &driver.diagEngine;
		global_diagclient = driver.diagClient.get();
		global_diagclient->clear();

		NetlistContext netlist(d, settings, *compilation, *top);
		PopulateNetlist populate(netlist);
		populate.add_internal_wires(top->body);

		SignalEvalContext amended_eval(netlist);
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
