// clang-format off
//
// Derived from:
//   third_party/slang/source/ast/Statements.cpp
//   third_party/slang/source/ast/statements/MiscStatements.cpp
//
// Copyright (c) 2024 Martin Povišer
// Copyright (c) 2015-2025 Michael Popoloski
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.
//
#include "slang/ast/Compilation.h"
#include "slang/diagnostics/ConstEvalDiags.h"
#include "slang/diagnostics/DeclarationsDiags.h"
#include "slang/diagnostics/NumericDiags.h"

#include "diag.h"
#include "initial_eval.h"

#include <iostream>

using namespace slang;
using namespace slang::ast;
using ER = Statement::EvalResult;

namespace SlangInitial {

// These are pretty much low-quality placeholders
inline constexpr slang::DiagCode ParallelBlockUnsupported(DiagSubsystem::Netlist, 101);
inline constexpr slang::DiagCode TODO(DiagSubsystem::Netlist, 102);
inline constexpr slang::DiagCode BadEvaluation(DiagSubsystem::Netlist, 103);

EvalVisitor::EvalVisitor(Compilation *compilation, bool ignore_timing)
	: context(ASTContext(compilation->getRoot(), LookupLocation::max), /* HACK */ ast::EvalFlags::IsScript)
	, ignore_timing(ignore_timing)
{
	context.pushEmptyFrame();
}

ER EvalVisitor::visit(const StatementList &stmt)
{
	for (auto item : stmt.list) {
		ER result = item->visit(*this);
		if (result != ER::Success)
			return result;
	}

	return ER::Success;
}

ER EvalVisitor::visit(const BlockStatement &stmt)
{
	if (stmt.blockKind != StatementBlockKind::Sequential) {
		context.addDiag(ParallelBlockUnsupported, stmt.sourceRange);
		return ER::Fail;
	}

	ER result = stmt.body.visit(*this);

	if (result == ER::Disable) {
		// Check if the disable statement we evaluated was targeting this block.
		// If it was, we've already skipped enough statements, so just clear out
		// the target and continue on.
		auto target = context.getDisableTarget();
		SLANG_ASSERT(target);
		if (target == stmt.blockSymbol) {
			result = ER::Success;
			context.setDisableTarget(nullptr, {});
		}
	}

	return result;
}

ER EvalVisitor::visit(const ReturnStatement &stmt)
{
	if (stmt.expr) {
		const SubroutineSymbol *subroutine = context.topFrame().subroutine;
		// TODO: is this a slang invariant, or something we should emit
		// error message for
		SLANG_ASSERT(subroutine);

		ConstantValue *storage = context.findLocal(subroutine->returnValVar);
		SLANG_ASSERT(storage);

		*storage = stmt.expr->eval(context);
	}
	return ER::Return;
}

ER EvalVisitor::visit(const BreakStatement&)
{
	return ER::Break;
}

ER EvalVisitor::visit(const ContinueStatement&)
{
	return ER::Continue;
}

ER EvalVisitor::visit(const DisableStatement &stmt)
{
	// Hierarchical names are disallowed in constant expressions and constant functions
    auto& ase = stmt.target.as<ArbitrarySymbolExpression>();
    const bool isHierarchical = ase.hierRef.target != nullptr;
    if (isHierarchical) {
        context.addDiag(diag::ConstEvalHierarchicalName, stmt.sourceRange) << ase.symbol->name;
        return ER::Fail;
    }

    SLANG_ASSERT(!context.getDisableTarget());
    context.setDisableTarget(ase.symbol, stmt.sourceRange);
    return ER::Disable;
}

ER EvalVisitor::visit(const VariableSymbol &sym)
{
	// Figure out the initial value for the variable.
	ConstantValue initial;
	if (auto initializer = sym.getInitializer()) {
		// FIXME: look into lifetime and initialization semantics
		initial = initializer->eval(context);
		if (!initial) {
			context.addDiag(TODO, sym.location);
			return ER::Fail;
		}
	}

	if (!initial)
		initial = sym.getType().getDefaultValue();

	// Create storage for the variable.
	context.createLocal(&sym, initial);

	return ER::Success;
}

ER EvalVisitor::visit(const VariableDeclStatement &stmt)
{
	// Figure out the initial value for the variable.
	ConstantValue initial;
	if (auto initializer = stmt.symbol.getInitializer()) {
		// FIXME: look into lifetime and initialization semantics
		initial = initializer->eval(context);
		if (!initial) {
			context.addDiag(TODO, stmt.sourceRange);
			return ER::Fail;
		}
	}

	if (!initial)
		initial = stmt.symbol.getType().getDefaultValue();

	// Create storage for the variable.
	context.createLocal(&stmt.symbol, initial);

	return ER::Success;
}

struct EvalConditionalVisitor {
	EvalContext& context;
	SmallVector<const Statement*> items;
	bool bad = false;

	EvalConditionalVisitor(EvalContext& context) : context(context), items() {}

	void visit(const ConditionalStatement& stmt) {
		bool matched = true;
		for (auto& cond : stmt.conditions) {
			auto result = cond.expr->eval(context);
			bad |= result.bad();

			if (cond.pattern) {
				result = cond.pattern->eval(context, result, CaseStatementCondition::Normal);
				bad |= result.bad();
			}

			if (!result.isTrue()) {
				matched = false;
				break;
			}
		}

		if (matched)
			stmt.ifTrue.visit(*this);

		if (stmt.ifFalse) {
			if (ConditionalStatement::isKind(stmt.ifFalse->kind) || !matched)
				stmt.ifFalse->visit(*this);
		}
	}

	void visit(const Statement& stmt) { items.push_back(&stmt); }
};

ER EvalVisitor::visit(const ConditionalStatement &stmt)
{
	auto check = stmt.check;

	EvalConditionalVisitor visitor(context);
	stmt.visit(visitor);
	if (visitor.bad)
		return ER::Fail;

	if (visitor.items.empty()) {
		if (check == UniquePriorityCheck::Priority || check == UniquePriorityCheck::Unique) {
			auto& diag = context.addDiag(diag::ConstEvalNoIfItemsMatched,
										 stmt.conditions.back().expr->sourceRange);
			diag << (check == UniquePriorityCheck::Priority ? "priority"sv : "unique"sv);
		}
		return ER::Success;
	}

	bool unique = check == UniquePriorityCheck::Unique || check == UniquePriorityCheck::Unique0;
	if (unique && visitor.items.size() > 1) {
		auto& diag = context.addDiag(diag::ConstEvalIfItemsNotUnique,
									 visitor.items[1]->sourceRange);
		diag.addNote(diag::NotePreviousMatch, visitor.items[0]->sourceRange);
	}

	return visitor.items[0]->visit(*this);
}

static bool checkMatch(CaseStatementCondition condition, const ConstantValue& cvl,
					   const ConstantValue& cvr) {
	if (condition == CaseStatementCondition::Inside) {
		// Unpacked arrays get unwrapped into their members for comparison.
		if (cvr.isContainer()) {
			for (auto& elem : cvr) {
				if (checkMatch(condition, cvl, elem))
					return true;
			}
			return false;
		}

		// Otherwise, we do a wildcard comparison if both sides are integers
		// and an equivalence comparison if not.
		if (cvl.isInteger() && cvr.isInteger())
			return (bool)condWildcardEqual(cvl.integer(), cvr.integer());
	}
	else if (condition != CaseStatementCondition::Normal) {
		const SVInt& l = cvl.integer();
		const SVInt& r = cvr.integer();
		if (condition == CaseStatementCondition::WildcardJustZ)
			return caseZWildcardEqual(l, r);
		else
			return caseXWildcardEqual(l, r);
	}

	return cvl == cvr;
}

ER EvalVisitor::visit(const CaseStatement &stmt)
{
	const auto check = stmt.check;
	const auto &expr = stmt.expr;
	const auto &condition = stmt.condition;
	const auto defaultCase = stmt.defaultCase;

	const Type* condType = nullptr;
	auto cv = expr.eval(context);
	if (!cv) {
		if (expr.kind == ExpressionKind::TypeReference)
			condType = &expr.as<TypeReferenceExpression>().targetType;
		else
			return ER::Fail;
	}

	const Statement* matchedStmt = nullptr;
	SourceRange matchRange;
	bool unique = check == UniquePriorityCheck::Unique || check == UniquePriorityCheck::Unique0;

	for (auto& group : stmt.items) {
		for (auto item : group.expressions) {
			bool matched;
			if (item->kind == ExpressionKind::ValueRange) {
				ConstantValue val = item->as<ValueRangeExpression>().checkInside(context, cv);
				if (!val)
					return ER::Fail;

				matched = (bool)(logic_t)val.integer();
			}
			else {
				auto val = item->eval(context);
				if (val)
					matched = checkMatch(condition, cv, val);
				else if (condType && item->kind == ExpressionKind::TypeReference)
					matched = item->as<TypeReferenceExpression>().targetType.isMatching(*condType);
				else
					return ER::Fail;
			}

			if (matched) {
				// If we already matched with a previous item, the only we reason
				// we'd still get here is to check for uniqueness. The presence of
				// another match means we failed the uniqueness check.
				if (matchedStmt) {
					auto& diag =
						context.addDiag(diag::ConstEvalCaseItemsNotUnique, item->sourceRange) << cv;
					diag.addNote(diag::NotePreviousMatch, matchRange);
					unique = false;
				}
				else {
					// Always break out of the item group once we find a match -- even when
					// checking uniqueness, expressions in a single group are not required
					// to be unique.
					matchedStmt = group.stmt;
					matchRange = item->sourceRange;
				}
				break;
			}
		}

		if (matchedStmt && !unique)
			break;
	}

	if (!matchedStmt)
		matchedStmt = defaultCase;

	if (matchedStmt)
		return matchedStmt->visit(*this);

	if (check == UniquePriorityCheck::Priority || check == UniquePriorityCheck::Unique) {
		auto& diag = context.addDiag(diag::ConstEvalNoCaseItemsMatched, expr.sourceRange);
		diag << (check == UniquePriorityCheck::Priority ? "priority"sv : "unique"sv);
		diag << cv;
	}

	return ER::Success;
}

ER EvalVisitor::visit(const PatternCaseStatement &stmt)
{
	const auto check = stmt.check;
	const auto &expr = stmt.expr;
	const auto &condition = stmt.condition;
	const auto defaultCase = stmt.defaultCase;

	auto cv = expr.eval(context);
	if (!cv)
		return ER::Fail;

	const Statement* matchedStmt = nullptr;
	SourceRange matchRange;

	for (auto& item : stmt.items) {
		auto val = item.pattern->eval(context, cv, condition);
		if (!val)
			return ER::Fail;

		if (!val.isTrue())
			continue;

		if (item.filter) {
			val = item.filter->eval(context);
			if (!val)
				return ER::Fail;

			if (!val.isTrue())
				continue;
		}

		// If we already matched with a previous item, the only we reason
		// we'd still get here is to check for uniqueness. The presence of
		// another match means we failed the uniqueness check.
		if (matchedStmt) {
			auto& diag =
				context.addDiag(diag::ConstEvalCaseItemsNotUnique, item.pattern->sourceRange) << cv;
			diag.addNote(diag::NotePreviousMatch, matchRange);
			break;
		}

		matchedStmt = item.stmt;
		matchRange = item.pattern->sourceRange;

		if (check != UniquePriorityCheck::Unique && check != UniquePriorityCheck::Unique0)
			break;
	}

	if (!matchedStmt)
		matchedStmt = defaultCase;

	if (matchedStmt)
		return matchedStmt->visit(*this);

	if (check == UniquePriorityCheck::Priority || check == UniquePriorityCheck::Unique) {
		auto& diag = context.addDiag(diag::ConstEvalNoCaseItemsMatched, expr.sourceRange);
		diag << (check == UniquePriorityCheck::Priority ? "priority"sv : "unique"sv);
		diag << cv;
	}

	return ER::Success;
}


ER EvalVisitor::visit(const ForLoopStatement &stmt)
{
	for (auto init : stmt.initializers) {
		if (!init->eval(context))
			return ER::Fail;
	}

	while (true) {
		if (stmt.stopExpr) {
			auto result = stmt.stopExpr->eval(context);
			if (result.bad())
				return ER::Fail;

			if (!result.isTrue())
				break;
		}

		ER result = stmt.body.visit(*this);
		if (result != ER::Success) {
			if (result == ER::Break)
				break;
			else if (result != ER::Continue)
				return result;
		}

		for (auto step : stmt.steps) {
			if (!step->eval(context))
				return ER::Fail;
		}
	}

	return ER::Success;
}

ER EvalVisitor::visit(const RepeatLoopStatement &stmt)
{
	auto cv = stmt.count.eval(context);
	if (cv.bad())
		return ER::Fail;

	std::optional<int64_t> oc = cv.integer().as<int64_t>();
	if (!oc || oc < 0) {
		if (cv.integer().hasUnknown())
			oc = 0;
		else {
			auto& diag = context.addDiag(diag::ValueOutOfRange, stmt.count.sourceRange);
			diag << cv << 0 << INT64_MAX;
			return ER::Fail;
		}
	}

	int64_t c = *oc;
	for (int64_t i = 0; i < c; i++) {
		ER result = stmt.body.visit(*this);
		if (result != ER::Success) {
			if (result == ER::Break)
				break;
			else if (result != ER::Continue)
				return result;
		}
	}

	return ER::Success;
}

static ER foreachEvalRecursive(EvalVisitor &ev, const ForeachLoopStatement &stmt, EvalContext& context,
							   const ConstantValue& cv, std::span<const ForeachLoopStatement::LoopDim> currDims) {
	const auto &body = stmt.body;

	// If there is no loop var just skip this index.
	auto& dim = currDims[0];
	if (!dim.loopVar) {
		// Shouldn't ever be at the end here.
		return foreachEvalRecursive(ev, stmt, context, nullptr, currDims.subspan(1));
	}

	auto local = context.createLocal(dim.loopVar);

	// If this is an associative array, looping happens over the keys.
	if (cv.isMap()) {
		auto& map = *cv.map();
		for (auto& [key, val] : map) {
			*local = key;

			ER result;
			if (currDims.size() > 1)
				result = foreachEvalRecursive(ev, stmt, context, val, currDims.subspan(1));
			else
				result = body.visit(ev);

			if (result != ER::Success && result != ER::Continue)
				return result;
		}
	}
	else if (cv.isQueue()) {
		auto& q = *cv.queue();
		for (size_t i = 0; i < q.size(); i++) {
			*local = SVInt(32, i, true);

			ER result;
			if (currDims.size() > 1)
				result = foreachEvalRecursive(ev, stmt, context, q[i], currDims.subspan(1));
			else
				result = body.eval(context);

			if (result != ER::Success && result != ER::Continue)
				return result;
		}
	}
	else if (cv.isString()) {
		SLANG_ASSERT(currDims.size() == 1);

		auto& str = cv.str();
		for (size_t i = 0; i < str.size(); i++) {
			*local = SVInt(32, i, true);

			ER result = body.visit(ev);
			if (result != ER::Success && result != ER::Continue)
				return result;
		}
	}
	else {
		std::span<const ConstantValue> elements;
		if (cv.isUnpacked())
			elements = cv.elements();

		ConstantRange range;
		bool isLittleEndian;
		if (dim.range) {
			range = *dim.range;
			isLittleEndian = range.isLittleEndian();
		}
		else {
			range = {0, int32_t(elements.size()) - 1};
			isLittleEndian = false;
		}

		for (int32_t i = range.left; isLittleEndian ? i >= range.right : i <= range.right;
			 isLittleEndian ? i-- : i++) {

			*local = SVInt(32, uint64_t(i), true);

			ER result;
			if (currDims.size() > 1) {
				size_t index = size_t(i);
				if (dim.range)
					index = (size_t)range.reverse().translateIndex(i);

				result = foreachEvalRecursive(ev, stmt, context,
						elements.empty() ? nullptr : elements[index], currDims.subspan(1));
			}
			else {
				result = body.visit(ev);
			}

			if (result != ER::Success && result != ER::Continue)
				return result;
		}
	}

	return ER::Success;
}

ER EvalVisitor::visit(const ForeachLoopStatement &stmt)
{
	// If there are no loop dimensions, this does nothing.
	if (stmt.loopDims.empty())
		return ER::Success;

	ConstantValue cv = stmt.arrayRef.eval(context);
	if (!cv)
		return ER::Fail;

	ER result = foreachEvalRecursive(*this, stmt, context, cv, stmt.loopDims);
	if (result == ER::Break || result == ER::Continue)
		return ER::Success;

	return result;
}

ER EvalVisitor::visit(const WhileLoopStatement &stmt)
{
	while (true) {
		auto cv = stmt.cond.eval(context);
		if (cv.bad())
			return ER::Fail;

		if (!cv.isTrue())
			break;

		ER result = stmt.body.visit(*this);
		if (result != ER::Success) {
			if (result == ER::Break)
				break;
			else if (result != ER::Continue)
				return result;
		}
	}

	return ER::Success;
}

ER EvalVisitor::visit(const DoWhileLoopStatement &stmt)
{
	while (true) {
		ER result = stmt.body.visit(*this);
		if (result != ER::Success) {
			if (result == ER::Break)
				break;
			else if (result != ER::Continue)
				return result;
		}

		auto cv = stmt.cond.eval(context);
		if (cv.bad())
			return ER::Fail;

		if (!cv.isTrue())
			break;
	}

	return ER::Success;
}

ER EvalVisitor::visit(const ForeverLoopStatement &stmt)
{
	while (true) {
		ER result = stmt.body.visit(*this);
		if (result != ER::Success) {
			if (result == ER::Break)
				break;
			else if (result != ER::Continue)
				return result;
		}
	}

	return ER::Success;
}

void EvalVisitor::handleDisplay(const CallExpression &call,
								const std::vector<ConstantValue> &args)
{
	(void) args;
	context.addDiag(slang::diag::ConstSysTaskIgnored, call.sourceRange)
					<< call.getSubroutineName();
}

ER EvalVisitor::visit(const ExpressionStatement &stmt)
{
	const auto &expr = stmt.expr;

	if (expr.kind == ExpressionKind::Call) {
		const auto &call = expr.as<CallExpression>();
		if (call.isSystemCall() && call.getSubroutineKind() == SubroutineKind::Task) {
			if (call.getSubroutineName() == "$fatal") {
				context.addDiag(slang::diag::FatalTask, call.sourceRange);
				return ER::Fail;
			} else if (call.getSubroutineName() == "$display") {
				std::vector<ConstantValue> args;
				for (auto arg_expr : call.arguments())
					args.push_back(arg_expr->eval(context));
				for (auto arg : args)
					if (arg.bad())
						return ER::Fail;
				handleDisplay(call, args);
			} else {
				context.addDiag(slang::diag::ConstSysTaskIgnored, call.sourceRange)
								<< call.getSubroutineName();
			}
			return ER::Success;
		}
	}
	return expr.eval(context) ? ER::Success : ER::Fail;
}

ER EvalVisitor::visit(const ImmediateAssertionStatement &stmt)
{
	auto cv = stmt.cond.eval(context);
	if (cv.bad())
		return ER::Fail;
	if (!cv.isTrue()) {
		// TODO: raise a diagnostic here
		return ER::Fail;
	}
	return ER::Success;
}

ER EvalVisitor::visit(const TimedStatement &stmt)
{
	if (!ignore_timing)
		context.addDiag(slang_frontend::diag::GenericTimingUnsyn, stmt.sourceRange);

	// ignore timing and visit inner statement
	ER result = stmt.stmt.visit(*this);
	return result;
}

ER EvalVisitor::visit(const slang::ast::WaitStatement &stmt)
{
	context.addDiag(slang_frontend::diag::WaitStatementUnsupported, stmt.sourceRange);
	return ER::Success;
}

ER EvalVisitor::visit(const EmptyStatement&)
{
	return ER::Success;
}

};
