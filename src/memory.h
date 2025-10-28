//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#pragma once
#include "slang_frontend.h"

namespace slang_frontend {

class DiagnosticIssuer;
struct InferredMemoryDetector : public TimingPatternInterpretor,
								public ast::ASTVisitor<InferredMemoryDetector, true, true>,
								public DiagnosticIssuer
{
	Yosys::pool<const ast::Symbol *> memory_candidates;
	std::function<bool(const ast::InstanceSymbol &sym)> should_dissolve;
	bool disallow_implicit = false;

	InferredMemoryDetector(SynthesisSettings &settings,
			std::function<bool(const ast::InstanceSymbol &sym)> should_dissolve)
		: TimingPatternInterpretor(settings, (DiagnosticIssuer &)*this),
		  should_dissolve(should_dissolve),
		  disallow_implicit(settings.no_implicit_memories.value_or(false))
	{}

	void process(const ast::Symbol &root)
	{
		auto first_pass = ast::makeVisitor(
				[&](auto &, const ast::VariableSymbol &symbol) {
					if (symbol.lifetime == ast::VariableLifetime::Static &&
							symbol.getType().isUnpackedArray() &&
							symbol.getType().hasFixedRange() &&
							(!disallow_implicit || find_user_hint(symbol)) &&
							symbol.getParentScope()->getContainingInstance() &&
							symbol.getParentScope()
									->getContainingInstance()
									->parentInstance->isModule() &&
							symbol.kind != ast::SymbolKind::FormalArgument)
						memory_candidates.insert(&symbol);
				},
				[&](auto &visitor, const ast::GenerateBlockSymbol &symbol) {
					if (symbol.isUninstantiated)
						return;
					visitor.visitDefault(symbol);
				},
				[&](auto &visitor, const ast::InstanceSymbol &symbol) {
					if (should_dissolve(symbol))
						visitor.visitDefault(symbol);
				});
		root.visit(first_pass);
		root.visit(*this);
	}

	struct LHSVisitor : public ast::ASTVisitor<LHSVisitor, true, true>
	{
		InferredMemoryDetector &rhs;
		LHSVisitor(InferredMemoryDetector &rhs) : rhs(rhs) {}

		void handle(const ast::ElementSelectExpression &expr)
		{
			expr.value().visit(*this);
			expr.selector().visit(rhs);
		}

		void handle(const ast::RangeSelectExpression &expr)
		{
			expr.value().visit(*this);
			expr.left().visit(rhs);
			expr.right().visit(rhs);
		}

		void handle(const ast::ValueExpressionBase &expr)
		{
			rhs.disqualify(expr.symbol, expr.sourceRange.start());
		}
	};

	std::optional<std::string_view> find_user_hint(const ast::Symbol &symbol)
	{
		const static std::set<std::string> recognized = {"ram_block", "rom_block", "ram_style",
				"rom_style", "ramstyle", "romstyle", "syn_ramstyle", "syn_romstyle"};

		for (auto attr : global_compilation->getAttributes(symbol)) {
			if (recognized.count(std::string{attr->name}) && !attr->getValue().isFalse())
				return attr->name;
		}
		return {};
	}

	void disqualify(const ast::Symbol &symbol, slang::SourceLocation loc)
	{
		std::optional<std::string_view> found_attr;
		if (memory_candidates.count(&symbol) && (found_attr = find_user_hint(symbol))) {
			auto &diag = add_diag(diag::MemoryNotInferred, symbol.location);
			diag << found_attr.value();
			diag.addNote(diag::NoteUsageBlame, loc);
		}

		memory_candidates.erase(&symbol);
	}

	void handle(const ast::ValueExpressionBase &expr)
	{
		disqualify(expr.symbol, expr.sourceRange.start());
	}

	void handle(const ast::PortSymbol &symbol)
	{
		if (symbol.internalSymbol)
			disqualify(*symbol.internalSymbol, symbol.location);
		visitDefault(symbol);
	}

	void handle(const ast::AssignmentExpression &assign)
	{
		LHSVisitor lhs(*this);
		assign.left().visit(lhs);
		assign.right().visit(*this);
	}

	void handle(const ast::ElementSelectExpression &expr)
	{
		if (ast::ValueExpressionBase::isKind(expr.value().kind)) {
			// do nothing
		} else {
			expr.value().visit(*this);
		}

		expr.selector().visit(*this);
	}

	bool wr_allowed = false;

	void handle(const ast::ExpressionStatement &stmt)
	{
		if (stmt.expr.kind == ast::ExpressionKind::Assignment &&
				stmt.expr.as<ast::AssignmentExpression>().isNonBlocking() && wr_allowed) {
			auto &assign = stmt.expr.as<ast::AssignmentExpression>();
			assign.right().visit(*this);

			const ast::Expression *raw_lexpr = &assign.left();
			LHSVisitor fallback(*this);
			while (true) {
				switch (raw_lexpr->kind) {
				case ast::ExpressionKind::RangeSelect: {
					auto &sel = raw_lexpr->as<ast::RangeSelectExpression>();
					sel.left().visit(*this);
					sel.right().visit(*this);
					raw_lexpr = &sel.value();
				} break;
				case ast::ExpressionKind::ElementSelect: {
					auto &sel = raw_lexpr->as<ast::ElementSelectExpression>();
					sel.selector().visit(*this);
					raw_lexpr = &sel.value();
					if (ast::ValueExpressionBase::isKind(sel.value().kind)) {
						// a potential memory candidate
						return;
					}
				} break;
				case ast::ExpressionKind::MemberAccess: {
					const auto &acc = raw_lexpr->as<ast::MemberAccessExpression>();
					raw_lexpr = &acc.value();
				} break;
				default: raw_lexpr->visit(fallback); return;
				}
			}

			log_abort(); // unreachable
		}

		stmt.expr.visit(*this);
	}

	void handle(const ast::GenerateBlockSymbol &sym)
	{
		if (sym.isUninstantiated)
			return;
		visitDefault(sym);
	}

	void handle(const ast::ProceduralBlockSymbol &symbol) { interpret(symbol); }

	virtual void handle_comb_like_process(
			const ast::ProceduralBlockSymbol &, const ast::Statement &body)
	{
		body.visit(*this);
	}

	virtual void handle_ff_process(const ast::ProceduralBlockSymbol &,
			const ast::SignalEventControl &, const ast::StatementBlockSymbol *,
			std::vector<const ast::Statement *> prologue, const ast::Statement &sync_body,
			std::span<AsyncBranch> async)
	{
		for (auto stmt : prologue)
			stmt->visit(*this);
		for (auto &branch : async)
			branch.body.visit(*this);
		wr_allowed = true;
		sync_body.visit(*this);
		wr_allowed = false;
	}

	virtual void handle_initial_process(const ast::ProceduralBlockSymbol &, const ast::Statement &)
	{
		// Initial processes have no influence over memory inference
	}

	void handle(const ast::InstanceSymbol &sym)
	{
		if (should_dissolve(sym)) {
			visitDefault(sym);
		} else {
			for (auto *conn : sym.getPortConnections()) {
				if (auto expr = conn->getExpression())
					expr->visit(*this);
			}
		}
	}
};

}; // namespace slang_frontend