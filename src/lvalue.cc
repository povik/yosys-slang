//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/ast/expressions/ConversionExpression.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/expressions/SelectExpressions.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/VariableSymbols.h"
#include "slang/ast/types/Type.h"

#include "diag.h"
#include "slang_frontend.h"
#include "variables.h"

namespace slang_frontend {

std::optional<LValue> LValue::analyze(
		EvalContext &context, const ast::Expression &expr, bool silent)
{
	ast_invariant(expr, expr.kind != ast::ExpressionKind::Streaming);

	if (!expr.type->isFixedSize()) {
		if (!silent) {
			auto &d = context.netlist.add_diag(diag::FixedSizeRequired, expr.sourceRange);
			d << expr.type->toString();
		}
		return std::nullopt;
	}

	switch (expr.kind) {
	case ast::ExpressionKind::HierarchicalValue: {
		const ast::ValueSymbol &symbol = expr.as<ast::ValueExpressionBase>().symbol;
		if (!context.netlist.scopes_remap.count(symbol.getParentScope()) &&
				!context.netlist.check_hier_ref(symbol, expr.sourceRange, silent)) {
			return std::nullopt;
		}
	}
		[[fallthrough]];
	case ast::ExpressionKind::NamedValue: {
		const ast::ValueSymbol &symbol = expr.as<ast::ValueExpressionBase>().symbol;
		if (context.netlist.is_inferred_memory(symbol)) {
			// Unless we are evaluating initial procedures, directly evaluating
			// the memory as an assignment target is disallowed. Memory writes should
			// be handled in `ProceduralContext::assign_rvalue_inner` before they
			// would get here.
			if (!(context.procedural &&
						context.procedural->timing.kind == ProcessTiming::Initial)) {
				if (!silent) {
					context.netlist.add_diag(diag::BadMemoryExpr, expr.sourceRange);
				}
				return std::nullopt;
			}
		}

		if (symbol.kind == ast::SymbolKind::ModportPort &&
				!context.netlist.scopes_remap.count(symbol.getParentScope())) {
			return analyze(
					context, *symbol.as<ast::ModportPortSymbol>().getConnectionExpr(), silent);
		}

		Variable var = context.variable(symbol);
		return LValue::variable(var);
	}
	case ast::ExpressionKind::RangeSelect: {
		const ast::RangeSelectExpression &rse = expr.as<ast::RangeSelectExpression>();
		ast_invariant(
				expr, rse.value().type->isBitstreamType() && rse.value().type->hasFixedRange());
		AddressingResolver resolver(context, rse);

		std::optional<LValue> inner = analyze(context, rse.value());
		if (!inner)
			return std::nullopt;

		return LValue::rangeSelect(
				std::move(*inner), std::move(resolver), expr.type->getBitstreamWidth());
	}
	case ast::ExpressionKind::ElementSelect: {
		// Handle element select as 1-item range select
		const ast::ElementSelectExpression &ese = expr.as<ast::ElementSelectExpression>();
		ast_invariant(
				expr, ese.value().type->isBitstreamType() && ese.value().type->hasFixedRange());

		if (context.netlist.is_inferred_memory(ese.value()) &&
				context.procedural->timing.kind != ProcessTiming::Initial) {
			ir::Value address = context(ese.selector());
			auto variable =
					Variable::from_symbol(&ese.value().as<ast::ValueExpressionBase>().symbol);
			return LValue::memoryWrite(variable, address, ese.type->getBitstreamWidth());
		}

		std::optional<LValue> inner = analyze(context, ese.value());
		if (!inner)
			return std::nullopt;

		AddressingResolver addr(context, ese);

		return LValue::rangeSelect(
				std::move(*inner), std::move(addr), expr.type->getBitstreamWidth());
	}
	case ast::ExpressionKind::Concatenation: {
		std::vector<LValue> elements;
		const ast::ConcatenationExpression &concat = expr.as<ast::ConcatenationExpression>();
		for (auto operand : concat.operands()) {
			auto element_lv = analyze(context, *operand, silent);
			if (!element_lv)
				return std::nullopt;
			elements.push_back(std::move(*element_lv));
		}
		return LValue::concatenation(std::move(elements));
	}
	case ast::ExpressionKind::MemberAccess: {
		const auto &acc = expr.as<ast::MemberAccessExpression>();

		std::optional<LValue> inner = analyze(context, acc.value());
		if (!inner)
			return std::nullopt;

		require(expr, acc.member.kind == ast::SymbolKind::Field);
		const auto &member = acc.member.as<ast::FieldSymbol>();
		require(expr, member.randMode == ast::RandMode::None);

		uint64_t bit_offset = bitstream_member_offset(member);

		return LValue::memberAccess(std::move(*inner), bit_offset, expr.type->getBitstreamWidth());
	}
	case ast::ExpressionKind::Conversion: {
		const ast::ConversionExpression &conv = expr.as<ast::ConversionExpression>();
		if (conv.operand().kind != ast::ExpressionKind::Streaming) {
			const ast::Type &from = conv.operand().type->getCanonicalType();
			const ast::Type &to = conv.type->getCanonicalType();
			if (to.isBitstreamType() && from.isBitstreamType() &&
					from.getBitstreamWidth() == to.getBitstreamWidth()) {
				return analyze(context, conv.operand(), silent);
			}
		}
	}
		[[fallthrough]];
	default:
		if (!silent) {
			context.netlist.add_diag(diag::UnsupportedLhs, expr.sourceRange);
		}
		return std::nullopt;
	}
}

LValue LValue::variable(Variable variable)
{
	return LValue(variable, variable.bitwidth(), true, true);
}

LValue LValue::concatenation(std::vector<LValue> elements)
{
	uint64_t size_total = 0;
	bool static_ = true;
	for (auto &element : elements) {
		size_total += element.bitsize;
		static_ &= element.static_;
	}
	return LValue(Concatenation{std::move(elements)}, size_total, static_,
			/* contiguous_slice_= */ false);
}

LValue LValue::rangeSelect(LValue inner, AddressingResolver resolver, uint64_t bitsize)
{
	bool static_ = inner.static_ && resolver.is_static();
	bool contiguous_slice_ = inner.contiguous_slice_;
	return LValue(RangeSelect{std::make_unique<AddressingResolver>(std::move(resolver)),
						  std::make_unique<LValue>(std::move(inner))},
			bitsize, static_, contiguous_slice_);
}

LValue LValue::memberAccess(LValue inner, uint64_t base_offset, uint64_t bitsize)
{
	bool static_ = inner.static_;
	bool contiguous_slice_ = inner.contiguous_slice_;
	return LValue(MemberAccess{base_offset, std::make_unique<LValue>(std::move(inner))}, bitsize,
			static_, contiguous_slice_);
}

LValue LValue::memoryWrite(Variable variable, ir::Value address, uint64_t bitsize)
{
	return LValue(MemoryWrite{variable, address}, bitsize, false, false);
}

bool LValue::is_static()
{
	return static_;
}

VariableBits LValue::evaluate_vbits()
{
	log_assert(static_);

	if (auto variable = std::get_if<Variable>(&descriptor)) {
		return *variable;
	} else if (auto concat = std::get_if<Concatenation>(&descriptor)) {
		VariableBits ret;
		ret.reserve(bitsize);
		auto &els = concat->elements;
		for (auto it = els.rbegin(); it != els.rend(); it++)
			ret.append(it->evaluate_vbits());
		return ret;
	} else if (auto range_sel = std::get_if<RangeSelect>(&descriptor)) {
		auto inner_vbits = range_sel->inner->evaluate_vbits();
		return range_sel->resolver->extract<VariableBits>(inner_vbits, bitsize);
	} else if (auto member_acc = std::get_if<MemberAccess>(&descriptor)) {
		auto inner_vbits = member_acc->inner->evaluate_vbits();
		return inner_vbits.extract(member_acc->base_offset, bitsize);
	} else {
		// unreachable
		log_abort();
	}
}

}; // namespace slang_frontend
