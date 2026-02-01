//
// Yosys slang frontend
//
// Copyright 2025 Martin Povišer <povik@cutebit.org>
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

#include "addressing.h"
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
	context.do_simple_assign(subroutine->location, flag, RTLIL::S0, true);
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
	context.do_simple_assign(statement->sourceRange.start(), flag, RTLIL::S0, true);
}

void ProceduralContext::signal_escape(slang::SourceLocation loc, EscapeConstructKind kind)
{
	auto it = escape_stack.rbegin();
	while (it != escape_stack.rend()) {
		do_simple_assign(loc, it->flag, RTLIL::S1, true);
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
	root_case = std::make_unique<Case>();
	current_case = root_case->add_switch({})->add_case({});
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

void ProceduralContext::copy_case_tree_into(RTLIL::CaseRule &rule)
{
	root_case->copy_into(netlist, &rule);
}

VariableBits ProceduralContext::all_driven()
{
	VariableBits all_driven;
	for (auto pair : vstate.visible_assignments) {
		all_driven.push_back(pair.first);
	}

	all_driven.sort_and_unify();

	VariableBits all_driven_filtered;
	for (auto bit : all_driven)
		if (bit.variable.kind == Variable::Static)
			all_driven_filtered.push_back(bit);

	return all_driven_filtered;
}

RTLIL::SigBit ProceduralContext::case_enable()
{
	RTLIL::SigBit ret = netlist.canvas->addWire(netlist.new_id(), 1);
	root_case->aux_actions.emplace_back(ret, RTLIL::State::S0);
	current_case->aux_actions.emplace_back(ret, RTLIL::State::S1);
	return ret;
}

void crop_zero_mask(const RTLIL::SigSpec &mask, RTLIL::SigSpec &target)
{
	for (int i = mask.size() - 1; i >= 0; i--) {
		if (mask[i] == RTLIL::S0)
			target.remove(i, 1);
	}
}

void crop_zero_mask(const RTLIL::SigSpec &mask, VariableBits &target)
{
	for (int i = mask.size() - 1; i >= 0; i--) {
		if (mask[i] == RTLIL::S0)
			target.erase(target.begin() + i);
	}
}

void ProceduralContext::update_variable_state(slang::SourceLocation loc, VariableBits lvalue,
		RTLIL::SigSpec unmasked_rvalue, RTLIL::SigSpec mask, bool blocking)
{
	log_assert((int)lvalue.size() == unmasked_rvalue.size());
	log_assert((int)lvalue.size() == mask.size());

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
				if (seen_blocking_assignment.count(chunk.variable)) {
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

	current_case->actions.push_back(Case::Action{loc, lvalue, mask, unmasked_rvalue});

	if (mask.is_fully_ones()) {
		// shortcut path to support initialization of automatic variables
		// (evaluating the background value is unavailable on the first
		// assignment)
		vstate.set(lvalue, unmasked_rvalue);
	} else {
		RTLIL::SigSpec rvalue_background = vstate.evaluate(netlist, lvalue);
		RTLIL::SigSpec rvalue = netlist.Bwmux(rvalue_background, unmasked_rvalue, mask);
		vstate.set(lvalue, rvalue);
	}
}

void ProceduralContext::do_simple_assign(
		slang::SourceLocation loc, VariableBits lvalue, RTLIL::SigSpec rvalue, bool blocking)
{
	update_variable_state(loc, lvalue, rvalue, RTLIL::SigSpec(RTLIL::S1, rvalue.size()), blocking);
}

RTLIL::SigSpec ProceduralContext::substitute_rvalue(VariableBits bits)
{
	RTLIL::SigSpec subed;
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
	return subed;
}

void ProceduralContext::assign_rvalue(
		const ast::AssignmentExpression &assign, RTLIL::SigSpec rvalue)
{
	if (assign.timingControl && !netlist.settings.ignore_timing.value_or(false))
		netlist.add_diag(diag::GenericTimingUnsyn, assign.timingControl->sourceRange);

	bool blocking = !assign.isNonBlocking();
	const ast::Expression *raw_lexpr = &assign.left();
	RTLIL::SigSpec raw_mask = RTLIL::SigSpec(RTLIL::S1, rvalue.size()), raw_rvalue = rvalue;

	if (raw_lexpr->kind == ast::ExpressionKind::Streaming) {
		auto &stream_lexpr = raw_lexpr->as<ast::StreamingConcatenationExpression>();
		VariableBits lvalue = eval.streaming_lhs(stream_lexpr);
		ast_invariant(assign, rvalue.size() >= lvalue.size());
		do_simple_assign(assign.sourceRange.start(), lvalue,
				rvalue.extract_end(rvalue.size() - lvalue.size()), blocking);
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
			RTLIL::SigSpec relem = rvalue.extract(nbits_remaining - relem_width, relem_width);
			nbits_remaining -= relem_width;

			assign_rvalue(inner_assign, eval.apply_nested_conversion(inner_assign.right(), relem));
		}

		log_assert(nbits_remaining == 0);
		return;
	}
	assign_rvalue_inner(assign, raw_lexpr, raw_rvalue, raw_mask, blocking);
}

void ProceduralContext::assign_rvalue_inner(const ast::AssignmentExpression &assign,
		const ast::Expression *raw_lexpr, RTLIL::SigSpec raw_rvalue, RTLIL::SigSpec raw_mask,
		bool blocking)
{
	ast_invariant(assign, raw_mask.size() == (int)raw_lexpr->type->getBitstreamWidth());
	ast_invariant(assign, raw_rvalue.size() == (int)raw_lexpr->type->getBitstreamWidth());

	bool finished_etching = false;
	bool memory_write = false;
	while (!finished_etching) {
		switch (raw_lexpr->kind) {
		case ast::ExpressionKind::RangeSelect: {
			auto &sel = raw_lexpr->as<ast::RangeSelectExpression>();
			Addressing<RTLIL::SigSpec> addr(eval, sel);
			int wider_size = sel.value().type->getBitstreamWidth();
			raw_mask = addr.shift_up(raw_mask, false, wider_size);
			raw_rvalue = addr.shift_up(raw_rvalue, true, wider_size);
			raw_lexpr = &sel.value();
		} break;
		case ast::ExpressionKind::ElementSelect: {
			auto &sel = raw_lexpr->as<ast::ElementSelectExpression>();

			if (netlist.is_inferred_memory(sel.value())) {
				finished_etching = true;
				memory_write = true;
				break;
			}

			Addressing<RTLIL::SigSpec> addr(eval, sel);
			raw_mask = addr.demux(raw_mask, sel.value().type->getBitstreamWidth());
			raw_rvalue = raw_rvalue.repeat(addr.range.width());
			raw_lexpr = &sel.value();
		} break;
		case ast::ExpressionKind::MemberAccess: {
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

			int bit_offset = bitstream_member_offset(member);
			int parent_width = acc.value().type->getBitstreamWidth();
			int pad = parent_width - acc.type->getBitstreamWidth() - bit_offset;
			raw_mask = {RTLIL::SigSpec(RTLIL::S0, pad), raw_mask,
					RTLIL::SigSpec(RTLIL::S0, bit_offset)};
			raw_rvalue = {RTLIL::SigSpec(RTLIL::Sx, pad), raw_rvalue,
					RTLIL::SigSpec(RTLIL::Sx, bit_offset)};
			raw_lexpr = &acc.value();
		} break;
		case ast::ExpressionKind::Concatenation: {
			const auto &concat = raw_lexpr->as<ast::ConcatenationExpression>();
			int base = raw_mask.size(), len;
			for (auto op : concat.operands()) {
				require(concat, op->type->isBitstreamType());
				base -= (len = op->type->getBitstreamWidth());
				log_assert(base >= 0);
				assign_rvalue_inner(assign, op, raw_rvalue.extract(base, len),
						raw_mask.extract(base, len), blocking);
			}
			log_assert(base == 0);
			return;
		} break;
		default: finished_etching = true; break;
		}
		log_assert(raw_mask.size() == (int)raw_lexpr->type->getBitstreamWidth());
		log_assert(raw_rvalue.size() == (int)raw_lexpr->type->getBitstreamWidth());
	}

	if (memory_write) {
		log_assert(raw_lexpr->kind == ast::ExpressionKind::ElementSelect);
		auto &sel = raw_lexpr->as<ast::ElementSelectExpression>();
		log_assert(netlist.is_inferred_memory(sel.value()));
		require(assign, !blocking);

		RTLIL::IdString id = netlist.id(sel.value().as<ast::ValueExpressionBase>().symbol);
		RTLIL::Cell *memwr = netlist.canvas->addCell(netlist.new_id(), ID($memwr_v2));
		memwr->setParam(ID::MEMID, id.str());
		if (timing.implicit()) {
			memwr->setParam(ID::CLK_ENABLE, false);
			memwr->setParam(ID::CLK_POLARITY, false);
			memwr->setPort(ID::CLK, RTLIL::Sx);
		} else {
			require(assign, timing.triggers.size() == 1);
			auto &trigger = timing.triggers[0];
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
		memwr->setPort(ID::EN, netlist.Mux(RTLIL::SigSpec(RTLIL::S0, raw_mask.size()), raw_mask,
									   netlist.LogicAnd(case_enable(), timing.background_enable)));

		RTLIL::SigSpec addr = eval(sel.selector());

		memwr->setParam(ID::ABITS, addr.size());
		memwr->setPort(ID::ADDR, addr);
		memwr->setParam(ID::WIDTH, raw_rvalue.size());
		memwr->setPort(ID::DATA, raw_rvalue);
		preceding_memwr.push_back(memwr);
	} else {
		VariableBits lvalue = eval.lhs(*raw_lexpr);
		update_variable_state(assign.sourceRange.start(), lvalue, raw_rvalue, raw_mask, blocking);
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
