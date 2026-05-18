//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
// clang-format off
#include "slang/ast/statements/MiscStatements.h"
#include "slang/ast/expressions/AssertionExpr.h"
#include "slang/ast/symbols/BlockSymbols.h"
#include "slang/util/ScopeGuard.h"

#include "slang_frontend.h"
#include "statements.h"
#include "diag.h"

namespace slang_frontend {

static const ast::Expression *get_simple_assertion_expr(
		NetlistContext &netlist, const ast::AssertionExpr &assertion_expr,
		slang::SourceRange fallback_source_range)
{
	slang::SourceRange source_range = assertion_expr.syntax ?
		assertion_expr.syntax->sourceRange() : fallback_source_range;

	if (!ast::SimpleAssertionExpr::isKind(assertion_expr.kind)) {
		netlist.add_diag(diag::UnsupportedSVAFeature, source_range);
		return nullptr;
	}

	auto &simple_expr = assertion_expr.as<ast::SimpleAssertionExpr>();
	if (simple_expr.repetition.has_value()) {
		netlist.add_diag(diag::RepetitionsUnsupported, source_range);
		return nullptr;
	}

	return &simple_expr.expr;
}

// Process a 'concurrent assertion'
//
// Any top level clocking expressions have been stripped. Clocking is part
// of the created procedural context.
void process_sva_property(const ast::ConcurrentAssertionStatement &statement,
						  const ast::StatementBlockSymbol *block,
						  ProceduralContext &procedural, const ast::AssertionExpr &top_expr)
{
	auto &netlist = procedural.netlist;

	const ast::AssertionExpr *expr = &top_expr;
	slang::SourceRange source_range = expr->syntax ? expr->syntax->sourceRange() : statement.sourceRange;

	// Extract disable iff condition if present; the extracted switch
	// needs to live until the end of the function to be picked up
	// by set_effects_trigger
	std::optional<SwitchHelper> switch_;
	auto guard = slang::ScopeGuard([&] {
		if (switch_.has_value()) {
			switch_->exit_branch();
			switch_->finish(netlist);
		}
	});
	if (ast::DisableIffAssertionExpr::isKind(expr->kind)) {
		auto &disable = expr->as<ast::DisableIffAssertionExpr>();
		switch_.emplace(procedural, netlist.ReduceBool(procedural.eval.sva(disable.condition)));
		switch_->enter_branch({RTLIL::S0});
		expr = &disable.expr;
		source_range = expr->syntax ? expr->syntax->sourceRange() : statement.sourceRange;
	}

	std::string flavor;
	switch (statement.assertionKind) {
	case ast::AssertionKind::Assert:        flavor = "assert"; break;
	case ast::AssertionKind::Assume:        flavor = "assume"; break;
	case ast::AssertionKind::CoverProperty: flavor = "cover"; break;
	default:                                netlist.add_diag(diag::AssertionUnsupported, statement.sourceRange); return;
	}

	RTLIL::SigSpec a;
	if (ast::SimpleAssertionExpr::isKind(expr->kind)) {
		auto simple_expr = get_simple_assertion_expr(netlist, *expr, source_range);
		if (!simple_expr)
			return;
		a = netlist.ReduceBool(procedural.eval.sva(*simple_expr));
	} else if (ast::BinaryAssertionExpr::isKind(expr->kind)) {
		auto &binary_expr = expr->as<ast::BinaryAssertionExpr>();
		if (binary_expr.op != ast::BinaryAssertionOperator::OverlappedImplication) {
			netlist.add_diag(diag::UnsupportedSVAFeature, source_range);
			return;
		}

		auto lhs_expr = get_simple_assertion_expr(netlist, binary_expr.left, source_range);
		auto rhs_expr = get_simple_assertion_expr(netlist, binary_expr.right, source_range);
		if (!lhs_expr || !rhs_expr)
			return;

		RTLIL::SigSpec antecedent = netlist.ReduceBool(procedural.eval.sva(*lhs_expr));
		RTLIL::SigSpec consequent = netlist.ReduceBool(procedural.eval.sva(*rhs_expr));
		if (statement.assertionKind == ast::AssertionKind::CoverProperty) {
			// Cover only non-vacuous successes of the implication.
			a = netlist.LogicAnd(antecedent, consequent);
		} else {
			a = netlist.LogicOr(netlist.LogicNot(antecedent), consequent);
		}
	} else {
		netlist.add_diag(diag::UnsupportedSVAFeature, source_range);
		return;
	}

	RTLIL::IdString cell_name;

	if (block && unwrap_statement(block->tryGetStatement()) == &statement && !block->name.empty()) {
		// If we are the sole statement in a block, use the block's label
		cell_name = netlist.id(*block);
	} else {
		cell_name = netlist.new_id();
	}

	auto cell = netlist.canvas->addCell(cell_name, ID($check));
	procedural.set_effects_trigger(cell);
	cell->setParam(ID::FLAVOR, flavor);
	cell->setParam(ID::FORMAT, std::string(""));
	cell->setParam(ID::ARGS_WIDTH, 0);
	cell->setParam(ID::PRIORITY, --procedural.effects_priority);
	cell->setPort(ID::ARGS, {});
	cell->setPort(ID::A, a);
	transfer_attrs<const ast::Statement>(netlist, statement, cell);
}

void process_freestanding_sva_property(NetlistContext &netlist,
									   const ast::ConcurrentAssertionStatement &statement,
						  			   const ast::StatementBlockSymbol *block)
{
	const ast::AssertionExpr &spec = statement.propertySpec;

	if (ast::ClockingAssertionExpr::isKind(spec.kind)) {
		// Need to strip clocking
		const auto &clocking_expr = spec.as<ast::ClockingAssertionExpr>();
		const auto &clocking = clocking_expr.clocking;

		if (!ast::SignalEventControl::isKind(clocking.kind)) {
			netlist.add_diag(diag::UnsupportedSVAFeature, clocking.sourceRange);
			return;
		}

		const auto &signal_event = clocking.as<ast::SignalEventControl>();

		ProcessTiming timing(ProcessTiming::EdgeTriggered);
		switch (signal_event.edge) {
		case ast::EdgeKind::None:
			netlist.add_diag(diag::SVAClockingRequiresEdge, signal_event.sourceRange);
			return;

		case ast::EdgeKind::PosEdge:
		case ast::EdgeKind::NegEdge:
			timing.triggers.push_back(ProcessTiming::Sensitivity {
				.signal = netlist.eval(signal_event.expr),
				.edge_polarity = (signal_event.edge == ast::EdgeKind::PosEdge),
				.ast_node = &clocking
			});
			break;

		case ast::EdgeKind::BothEdges:
			netlist.add_diag(diag::BothEdgesUnsupported, signal_event.sourceRange);
			return;
		}

		if (signal_event.iffCondition) {
			// TODO
			netlist.add_diag(diag::IffUnsupported, signal_event.iffCondition->sourceRange);
		}

		ProceduralContext procedure(netlist, timing);
		process_sva_property(statement, block, procedure, clocking_expr.expr);

		RTLIL::Process *rtlil_proc = netlist.canvas->addProcess(netlist.new_id());
		transfer_attrs<const ast::Statement>(netlist, statement, rtlil_proc);
		procedure.copy_case_tree_into(rtlil_proc->root_case);
	} else {
		// No clocking
		ProceduralContext procedure(netlist, ProcessTiming::implicit);
		process_sva_property(statement, block, procedure, spec);

		RTLIL::Process *rtlil_proc = netlist.canvas->addProcess(netlist.new_id());
		transfer_attrs<const ast::Statement>(netlist, statement, rtlil_proc);
		procedure.copy_case_tree_into(rtlil_proc->root_case);
	}
}

};
