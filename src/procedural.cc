//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//

#include "slang/ast/Statement.h"
#include "slang/ast/expressions/AssignmentExpressions.h"
#include "slang/ast/expressions/ConversionExpression.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/symbols/SubroutineSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"

// Fix for Yosys declaring ceil_log2 as both inline and non-inline
// but not defining the non-inline one; be sure to include utils.h
// with the inline definition to prevent linkage errors on some
// platforms
#include "kernel/utils.h"

#include "cases.h"
#include "diag.h"
#include "slang_frontend.h"
#include "variables.h"

namespace slang_frontend {

EnterAutomaticScopeGuard::EnterAutomaticScopeGuard(EvalContext &context, const ast::Scope *scope)
	: context(context), scope(scope)
{
	if (scope) {
		++context.scope_nest_level[scope];
	}
}

EnterAutomaticScopeGuard::~EnterAutomaticScopeGuard()
{
	if (scope) {
		auto new_nest_level = --context.scope_nest_level.at(scope);
		log_assert(new_nest_level >= 0);
		if (new_nest_level == 0)
			context.scope_nest_level.erase(scope);
	}
}

RegisterEscapeConstructGuard::RegisterEscapeConstructGuard(ProceduralContext &context,
		EscapeConstructKind kind, const ast::SubroutineSymbol *subroutine)
	: context(context), flag(Variable::escape_flag(context.flag_counter++))
{
	assert(kind == EscapeConstructKind::FunctionBody);
	context.escape_stack.emplace_back();
	auto &construct = context.escape_stack.back();
	construct.kind = kind;
	construct.subroutine = subroutine;
	construct.flag = flag;
	context.do_simple_assign(subroutine->location, flag, ir::S0, true);
}

RegisterEscapeConstructGuard::RegisterEscapeConstructGuard(
		ProceduralContext &context, EscapeConstructKind kind, const ast::Statement *statement)
	: context(context), flag(Variable::escape_flag(context.flag_counter++))
{
	log_assert(kind == EscapeConstructKind::Loop || kind == EscapeConstructKind::LoopBody);
	context.escape_stack.emplace_back();
	auto &construct = context.escape_stack.back();
	construct.kind = kind;
	construct.flag = flag;
	context.do_simple_assign(statement->sourceRange.start(), flag, ir::S0, true);
}

ProcessTiming::ProcessTiming(Kind kind) : kind(kind)
{}

ProcessTiming ProcessTiming::implicit(ProcessTiming::Implicit);
ProcessTiming ProcessTiming::initial(ProcessTiming::Initial);

void ProceduralContext::signal_escape(slang::SourceLocation loc, EscapeConstructKind kind)
{
	auto it = escape_stack.rbegin();
	while (it != escape_stack.rend()) {
		do_simple_assign(loc, it->flag, ir::S1, true);
		if (it->kind == kind)
			break;
		it++;
	}
	log_assert(it != escape_stack.rend());
}

const ast::SubroutineSymbol *ProceduralContext::get_current_subroutine()
{
	for (auto it = escape_stack.rbegin(); it != escape_stack.rend(); it++) {
		if (it->kind == EscapeConstructKind::FunctionBody)
			return it->subroutine;
	}
	log_abort();
}

RegisterEscapeConstructGuard::~RegisterEscapeConstructGuard()
{
	context.escape_stack.pop_back();
}

ProceduralContext::ProceduralContext(NetlistContext &netlist, ProcessTiming &timing)
	: unroll_limit(netlist, netlist.settings.unroll_limit()), netlist(netlist), timing(timing),
	  eval(netlist, *this)
{
#ifndef SLANG_MUX_LOWERING
	root_case = std::make_unique<Case>();
	current_case = root_case->add_switch({})->add_case({});
#endif
}

ProceduralContext::~ProceduralContext()
{}

void ProceduralContext::inherit_state(ProceduralContext &other)
{
	assert(&netlist == &other.netlist);
	assert(eval.scope_nest_level == other.eval.scope_nest_level);
	assert(seen_blocking_assignment.empty());
	assert(seen_nonblocking_assignment.empty());
	seen_blocking_assignment = other.seen_blocking_assignment;
	seen_nonblocking_assignment = other.seen_nonblocking_assignment;
	preceding_memwr = other.preceding_memwr;
	vstate = other.vstate;
	flag_counter = other.flag_counter;
}

#ifndef SLANG_MUX_LOWERING
void ProceduralContext::copy_case_tree_into(RTLIL::CaseRule &rule)
{
	root_case->copy_into(netlist, &rule);
}
#endif

void ProceduralContext::descend_into_empty_case()
{
#ifndef SLANG_MUX_LOWERING
	current_case = current_case->add_switch({})->add_case({});
#endif
}

VariableBits ProceduralContext::all_driven()
{
	VariableBits all_driven;
	for (auto pair : vstate.visible_assignments) {
		all_driven.append(pair.first);
	}

	all_driven.sort_and_unify();

	VariableBits all_driven_filtered;
	for (auto chunk : all_driven.chunks())
		if (chunk.variable.kind == Variable::Static)
			all_driven_filtered.append(VariableBits(chunk));

	return all_driven_filtered;
}

ir::Net ProceduralContext::case_enable()
{
	if (timing.kind == ProcessTiming::Initial) {
		return ir::S1;
	}
#ifdef SLANG_MUX_LOWERING
	return enabled;
#else
	ir::Value ret = netlist.add_placeholder_signal(1);
	root_case->aux_actions.emplace_back(ret, RTLIL::State::S0);
	current_case->aux_actions.emplace_back(ret, RTLIL::State::S1);
	return ret.as_net();
#endif
}

void crop_zero_mask(const ir::Value &mask, ir::Value &target)
{
	for (int i = mask.size() - 1; i >= 0; i--) {
		if (mask[i] == ir::S0)
			target.remove(i, 1);
	}
}

void crop_zero_mask(const ir::Value &mask, VariableBits &target)
{
	for (int i = mask.size() - 1; i >= 0; i--) {
		if (mask[i] == ir::S0)
			target.remove(i);
	}
}

void crop_undef_mask(const ir::Value &mask, ir::Value &target)
{
	for (int i = mask.size() - 1; i >= 0; i--) {
		if (mask[i] == ir::Sx)
			target.remove(i, 1);
	}
}

void crop_undef_mask(const ir::Value &mask, VariableBits &target)
{
	for (int i = mask.size() - 1; i >= 0; i--) {
		if (mask[i] == ir::Sx)
			target.remove(i);
	}
}

void ProceduralContext::update_variable_state(slang::SourceLocation loc, VariableBits lvalue,
		ir::Value unmasked_rvalue, ir::Value mask, bool blocking)
{
	log_assert(lvalue.bitwidth() == (uint64_t)unmasked_rvalue.size());
	log_assert(lvalue.bitwidth() == (uint64_t)mask.size());

	crop_zero_mask(mask, lvalue);
	crop_zero_mask(mask, unmasked_rvalue);
	crop_zero_mask(mask, mask);

	for (auto chunk : lvalue.chunks()) {
		if (chunk.variable.kind == Variable::Static) {
			if (blocking) {
				if (seen_nonblocking_assignment.count(chunk.variable)) {
					auto &diag = netlist.add_diag(diag::BlockingAssignmentAfterNonblocking, loc);
					diag << chunk.variable.get_symbol()->name;
					diag.addNote(diag::NotePreviousAssignment,
							seen_nonblocking_assignment.at(chunk.variable));
				} else {
					seen_blocking_assignment[chunk.variable] = loc;
				}
			} else {
				if (timing.kind == ProcessTiming::Initial) {
					auto &diag = netlist.add_diag(diag::NonblockingAssignInInitialUnsupported, loc);
					diag.addNote(diag::NoteIgnoreInitial, loc);
					// We have issued the diagnostic, handle as blocking from
					// this point onward.
					blocking = true;
				} else if (seen_blocking_assignment.count(chunk.variable)) {
					auto &diag = netlist.add_diag(diag::NonblockingAssignmentAfterBlocking, loc);
					diag << chunk.variable.get_symbol()->name;
					diag.addNote(diag::NotePreviousAssignment,
							seen_blocking_assignment.at(chunk.variable));
				} else {
					seen_nonblocking_assignment[chunk.variable] = loc;
				}
			}
		} else if (chunk.variable.kind == Variable::Dummy) {
			// Dummies are for graceful error handling and require
			// no checking of blocking or nonblocking case
		} else {
			// This is expected to be an AST invariant -- we don't have a symbol
			// to use here for the ast_invariant() helper, so it's a plain
			// assert
			log_assert(blocking);
		}
	}

	if (timing.kind == ProcessTiming::Initial) {
		crop_undef_mask(mask, lvalue);
		crop_undef_mask(mask, unmasked_rvalue);
		crop_undef_mask(mask, mask);

		ir::Value &rvalue = unmasked_rvalue;

		if (!rvalue.is_fully_const()) {
			netlist.add_diag(diag::ErrorNonconstantInitialEval, loc);
			return;
		}

		for (auto [base, size, chunk] : lvalue.chunk_spans()) {
			switch (chunk.variable.kind) {
			case Variable::Dummy:
			case Variable::Invalid: continue;

			case Variable::Local:
			case Variable::EscapeFlag:
				for (uint64_t i = 0; i < size; i++) {
					initial_locals_state[chunk[i]] = rvalue[base + i].trit();
				}
				break;
			case Variable::Static: {
				for (uint64_t i = 0; i < size; i++) {
					netlist.initial_state[chunk[i]] = rvalue[base + i].trit();
				}
				const ast::Symbol &symbol = *chunk.variable.get_symbol();
				if (netlist.is_inferred_memory(symbol)) {
					bool big_endian = !symbol.as<ast::ValueSymbol>()
											   .getType()
											   .getFixedRange()
											   .isLittleEndian();
					netlist.add_memory_init(netlist.id(symbol), chunk.base, big_endian,
							rvalue.extract((int)base, (int)size).as_const());
				}
			} break;
			default: log_abort();
			}
		}
		return;
	}

#ifndef SLANG_MUX_LOWERING
	current_case->actions.push_back(Case::Action{loc, lvalue, mask, unmasked_rvalue});
#endif

	if (mask.is_fully_ones()) {
		// shortcut path to support initialization of automatic variables
		// (evaluating the background value is unavailable on the first
		// assignment)
		vstate.set(lvalue, unmasked_rvalue);
	} else {
		ir::Value rvalue_background = vstate.evaluate(netlist, lvalue);
		ir::Value rvalue = netlist.Bwmux(rvalue_background, unmasked_rvalue, mask);
		vstate.set(lvalue, rvalue);
	}
}

void ProceduralContext::do_simple_assign(
		slang::SourceLocation loc, VariableBits lvalue, ir::Value rvalue, bool blocking)
{
	update_variable_state(loc, lvalue, rvalue, ir::Value(ir::S1, rvalue.size()), blocking);
}

ir::Value ProceduralContext::substitute_rvalue(VariableBits bits)
{
	ir::Value subed;

	if (timing.kind == ProcessTiming::Initial) {
		// No non-blocking assignments allowed in initial procedures.
		for (auto [base, size, chunk] : bits.chunk_spans()) {
			switch (chunk.variable.kind) {
			case Variable::Dummy:
			case Variable::Invalid: log_abort();

			case Variable::Local:
			case Variable::EscapeFlag:
				for (uint64_t i = 0; i < size; i++) {
					subed.append(initial_locals_state.at(chunk[i], ir::Sx));
				}
				break;
			case Variable::Static:
				for (uint64_t i = 0; i < size; i++) {
					subed.append(netlist.initial_state.at(chunk[i], ir::Sx));
				}
				break;
			default: log_abort();
			}
		}
	} else {
		for (auto chunk : bits.chunks()) {
			// We disallow mixing of blocking and non-blocking assignments to the
			// same variable from the same process. That simplifies the handling
			// here.
			if (chunk.variable.kind != Variable::Static ||
					seen_blocking_assignment.count(chunk.variable))
				subed.append(vstate.evaluate(netlist, chunk));
			else
				subed.append(netlist.convert_static(chunk));
		}
	}

	return subed;
}

void assign_to_lvalue_with_masking(const ast::AssignmentExpression &assign,
		ProceduralContext &context, LValue &lvalue, ir::Value rvalue, ir::Value mask, bool blocking)
{
	if (lvalue.is_static()) {
		context.update_variable_state(
				assign.sourceRange.start(), lvalue.evaluate_vbits(), rvalue, mask, blocking);
		return;
	}

	if (auto concat = std::get_if<LValue::Concatenation>(&lvalue.descriptor)) {
		uint64_t base = lvalue.bitsize;
		for (auto &el : concat->elements) {
			base -= el.bitsize;
			assign_to_lvalue_with_masking(assign, context, el, rvalue.extract(base, el.bitsize),
					mask.extract(base, el.bitsize), blocking);
		}
		log_assert(base == 0);
	} else if (auto range_sel = std::get_if<LValue::RangeSelect>(&lvalue.descriptor)) {
		if (range_sel->resolver->stride == lvalue.bitsize) {
			// Effectively an element select
			assign_to_lvalue_with_masking(assign, context, *range_sel->inner,
					rvalue.repeat(range_sel->resolver->range.width()),
					range_sel->resolver->demux(mask, range_sel->inner->bitsize), blocking);
		} else {
			assign_to_lvalue_with_masking(assign, context, *range_sel->inner,
					range_sel->resolver->shift_up(rvalue, true, range_sel->inner->bitsize),
					range_sel->resolver->shift_up(mask, false, range_sel->inner->bitsize),
					blocking);
		}
	} else if (auto member_acc = std::get_if<LValue::MemberAccess>(&lvalue.descriptor)) {
		uint64_t parent_width = member_acc->inner->bitsize;
		uint64_t pad = parent_width - lvalue.bitsize - member_acc->base_offset;
		assign_to_lvalue_with_masking(assign, context, *member_acc->inner,
				{ir::Value(ir::Sx, pad), rvalue, ir::Value(ir::Sx, member_acc->base_offset)},
				{ir::Value(ir::S0, pad), mask, ir::Value(ir::S0, member_acc->base_offset)},
				blocking);
	} else if (auto mem_write = std::get_if<LValue::MemoryWrite>(&lvalue.descriptor)) {
		auto &netlist = context.netlist;
		RTLIL::Cell *cell = netlist.canvas->addCell(netlist.new_id(), ID($memwr_v2));
		std::string id = netlist.id(*mem_write->target.get_symbol());
		cell->setParam(ID::MEMID, id);
		auto &timing = context.timing;
		if (timing.kind == ProcessTiming::Implicit) {
			cell->setParam(ID::CLK_ENABLE, false);
			cell->setParam(ID::CLK_POLARITY, false);
			cell->setPort(ID::CLK, RTLIL::Sx);
		} else if (timing.kind == ProcessTiming::EdgeTriggered) {
			require(assign, timing.triggers.size() == 1);
			auto &trigger = timing.triggers[0];
			cell->setParam(ID::CLK_ENABLE, true);
			cell->setParam(ID::CLK_POLARITY, trigger.edge_polarity);
			cell->setPort(ID::CLK, ir::Value(trigger.signal));
		} else {
			ast_unreachable(assign);
		}

		int portid = context.netlist.emitted_mems[id].num_wr_ports++;
		cell->setParam(ID::PORTID, portid);
		std::vector<RTLIL::State> prio_mask(portid, RTLIL::S0);
		auto &preceding_memwr = context.preceding_memwr;
		for (auto prev : preceding_memwr) {
			log_assert(prev->type == ID($memwr_v2));
			if (prev->getParam(ID::MEMID) == cell->getParam(ID::MEMID)) {
				prio_mask[prev->getParam(ID::PORTID).as_int()] = RTLIL::S1;
			}
		}
		preceding_memwr.push_back(cell);

		cell->setParam(ID::PRIORITY_MASK, prio_mask);
		cell->setPort(
				ID::EN, netlist.Mux(RTLIL::SigSpec(RTLIL::S0, mask.size()), mask,
								netlist.LogicAnd(context.case_enable(), timing.background_enable)));
		cell->setParam(ID::ABITS, mem_write->address.size());
		cell->setPort(ID::ADDR, mem_write->address);
		cell->setParam(ID::WIDTH, rvalue.size());
		cell->setPort(ID::DATA, rvalue);
	} else {
		// unreachable
		log_abort();
	}
}

void ProceduralContext::assign_rvalue(const ast::AssignmentExpression &assign, ir::Value rvalue)
{
	if (assign.timingControl && !netlist.settings.ignore_timing.value_or(false))
		netlist.add_diag(diag::GenericTimingUnsyn, assign.timingControl->sourceRange);

	bool blocking = !assign.isNonBlocking();
	const ast::Expression *raw_lexpr = &assign.left();

	if (raw_lexpr->kind == ast::ExpressionKind::Streaming) {
		auto &stream_lexpr = raw_lexpr->as<ast::StreamingConcatenationExpression>();
		VariableBits lvalue = eval.streaming_lhs(stream_lexpr);
		ast_invariant(assign, (uint64_t)rvalue.size() >= lvalue.bitwidth());
		do_simple_assign(assign.sourceRange.start(), lvalue,
				rvalue.extract_end(rvalue.size() - lvalue.bitwidth()), blocking);
		return;
	} else if (raw_lexpr->kind == ast::ExpressionKind::SimpleAssignmentPattern) {
		// break down into individual assignments
		auto &pattern_lexpr = raw_lexpr->as<ast::SimpleAssignmentPatternExpression>();

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
			ir::Value relem = rvalue.extract(nbits_remaining - relem_width, relem_width);
			nbits_remaining -= relem_width;

			assign_rvalue(inner_assign, eval.apply_nested_conversion(inner_assign.right(), relem));
		}

		log_assert(nbits_remaining == 0);
		return;
	}
	auto analyzed_lvalue = LValue::analyze(this->eval, *raw_lexpr, false);
	if (analyzed_lvalue) {
		assign_to_lvalue_with_masking(assign, *this, *analyzed_lvalue, rvalue,
				ir::Value(ir::S1, rvalue.size()), blocking);
	}
}

Variable ProceduralContext::get_disable_flag()
{
	if (escape_stack.empty())
		return Variable();
	else
		return escape_stack.back().flag;
}

UnrollLimitTracking::UnrollLimitTracking(NetlistContext &netlist, int limit)
	: netlist(netlist), limit(limit)
{}

UnrollLimitTracking::~UnrollLimitTracking()
{
	log_assert(!unrolling);
}

void UnrollLimitTracking::enter_unrolling()
{
	if (!unrolling++) {
		unroll_counter = 0;
		error_issued = false;
		loops.clear();
	}
}

void UnrollLimitTracking::exit_unrolling()
{
	unrolling--;
	log_assert(unrolling >= 0);
}

bool UnrollLimitTracking::unroll_tick(const ast::Statement *symbol)
{
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

}; // namespace slang_frontend
