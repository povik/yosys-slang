//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//

struct InferredMemoryDetector : public ast::ASTVisitor<InferredMemoryDetector, true, true> {
public:
	Yosys::pool<const ast::Symbol *> memory_candidates;

	void handle(const ast::RootSymbol &root) {
		auto first_pass = ast::makeVisitor([&](auto&, const ast::VariableSymbol &symbol) {
			if (symbol.lifetime == ast::VariableLifetime::Static &&
					symbol.getType().isUnpackedArray() &&
					symbol.getType().hasFixedRange())
				memory_candidates.insert(&symbol);
		}, [&](auto& visitor, const ast::GenerateBlockSymbol &symbol) {
			if (symbol.isUninstantiated)
				return;
			visitor.visitDefault(symbol);
		});
		root.visit(first_pass);
		visitDefault(root);
	}

	struct LHSVisitor : public ast::ASTVisitor<LHSVisitor, true, true> {
		InferredMemoryDetector &rhs;
		LHSVisitor(InferredMemoryDetector &rhs) : rhs(rhs) {}

		void handle(const ast::ElementSelectExpression &expr) {
			expr.value().visit(*this);
			expr.selector().visit(rhs);
		}

		void handle(const ast::RangeSelectExpression &expr) {
			expr.value().visit(*this);
			expr.left().visit(rhs);
			expr.right().visit(rhs);
		}

		void handle(const ast::ValueExpressionBase &expr) {
			rhs.disqualify(expr.symbol, expr.sourceRange.start());
		}
	};

	bool has_user_hint(const ast::Symbol &symbol)
	{
		const static std::set<std::string> recognized =
			{"ram_block", "rom_block", "ram_style", "rom_style", "ramstyle",
			 "romstyle",  "syn_ramstyle", "syn_romstyle"};

		for (auto attr : global_compilation->getAttributes(symbol)) {
			if (recognized.count(std::string{attr->name}) && !attr->getValue().isFalse())
				return true;
		}
		return false;
	}

	void disqualify(const ast::Symbol &symbol, slang::SourceLocation loc)
	{
		if (memory_candidates.count(&symbol) && has_user_hint(symbol)) {
			auto &diag = symbol.getParentScope()->addDiag(diag::MemoryNotInferred, symbol.location);
			diag.addNote(diag::NoteUsageBlame, loc);
		}

		memory_candidates.erase(&symbol);
	}

	void handle(const ast::ValueExpressionBase &expr) {
		disqualify(expr.symbol, expr.sourceRange.start());
	}

	void handle(const ast::PortSymbol &symbol) {
		if (symbol.internalSymbol)
			disqualify(*symbol.internalSymbol, symbol.location);
		visitDefault(symbol);
	}

	void handle(const ast::AssignmentExpression &assign) {
		LHSVisitor lhs(*this);
		assign.left().visit(lhs);
		assign.right().visit(*this);
	}

	void handle(const ast::ElementSelectExpression &expr) {
		if (ast::ValueExpressionBase::isKind(expr.value().kind)) {
			// do nothing
		} else {
			expr.value().visit(*this);
		}

		expr.selector().visit(*this);
	}

	bool wr_allowed = false;

	void handle(const ast::ExpressionStatement &stmt) {
		if (stmt.expr.kind == ast::ExpressionKind::Assignment &&
				stmt.expr.as<ast::AssignmentExpression>().isNonBlocking() &&
				wr_allowed) {
			auto& assign = stmt.expr.as<ast::AssignmentExpression>();
			assign.right().visit(*this);

			const ast::Expression *raw_lexpr = &assign.left();
			LHSVisitor fallback(*this);
			while (true) {
				switch (raw_lexpr->kind) {
				case ast::ExpressionKind::RangeSelect:
					{
						auto &sel = raw_lexpr->as<ast::RangeSelectExpression>();
						sel.left().visit(*this);
						sel.right().visit(*this);
						raw_lexpr = &sel.value();
					}
					break;
				case ast::ExpressionKind::ElementSelect:
					{
						auto &sel = raw_lexpr->as<ast::ElementSelectExpression>();
						sel.selector().visit(*this);
						raw_lexpr = &sel.value();
						if (ast::ValueExpressionBase::isKind(sel.value().kind)) {
							// a potential memory candidate
							return;
						}
					}
					break;
				case ast::ExpressionKind::MemberAccess:
					{
						const auto &acc = raw_lexpr->as<ast::MemberAccessExpression>();
						raw_lexpr = &acc.value();
					}
					break;
				default:
					raw_lexpr->visit(fallback);
					return;
				}
			}

			log_abort(); // unreachable
		}

		stmt.expr.visit(*this);
	}

	void handle(const ast::ProceduralBlockSymbol &symbol)
	{
		if (symbol.procedureKind == ast::ProceduralBlockKind::Always ||
				symbol.procedureKind == ast::ProceduralBlockKind::AlwaysFF) {
			if (symbol.getBody().kind == ast::StatementKind::Timed) {
				const auto &timed = symbol.getBody().as<ast::TimedStatement>();
				const auto *top_ast_timing = &timed.timing;

				using TCKind = ast::TimingControlKind;
				std::span<const ast::TimingControl* const> events;
				const ast::TimingControl* const top_events[1] = {top_ast_timing};

				events = (top_ast_timing->kind == TCKind::EventList) ?
						top_ast_timing->as<ast::EventListControl>().events
						: std::span<const ast::TimingControl* const>(top_events);

				if (events.size() == 1 && events[0]->kind == ast::TimingControlKind::SignalEvent &&
						events[0]->as<ast::SignalEventControl>().edge != ast::EdgeKind::None) {
					wr_allowed = true;
				}
			}
		}

		visitDefault(symbol);
		wr_allowed = false;
	}

	void handle(const ast::GenerateBlockSymbol &sym)
	{
		if (sym.isUninstantiated)
			return;
		visitDefault(sym);
	}
};
