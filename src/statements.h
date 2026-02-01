//
// Yosys slang frontend
//
// Copyright 2025 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#pragma once

#include "kernel/rtlil.h"

#include "cases.h"
#include "slang/ast/ASTVisitor.h"
#include "slang_frontend.h"
#include "variables.h"

namespace slang_frontend {

struct StatementExecutor : public ast::ASTVisitor<StatementExecutor, true, false>
{
public:
	NetlistContext &netlist;
	ProceduralContext &context;
	EvalContext &eval;
	UnrollLimitTracking &unroll_limit;
	const ast::StatementBlockSymbol *containing_block = nullptr;

	StatementExecutor(ProceduralContext &context)
		: netlist(context.netlist), context(context), eval(context.eval),
		  unroll_limit(context.unroll_limit)
	{}

	struct SwitchHelper
	{
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

		SwitchHelper(const SwitchHelper &) = delete;
		SwitchHelper &operator=(const SwitchHelper &) = delete;
		SwitchHelper(SwitchHelper &&other)
			: parent(other.parent), current_case(other.current_case), sw(other.sw),
			  vstate(other.vstate), entered(other.entered), finished(other.finished)
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

		void branch(std::vector<RTLIL::SigSpec> compare, std::function<void()> f)
		{
			// TODO: extend detection
			if (compare.size() == 1 && compare[0].is_fully_def() && sw->signal.is_fully_def() &&
					sw->signal != compare[0]) {
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
					new_id = netlist.new_id(
							RTLIL::unescape_id(netlist.id(*symbol)) + chunk.slice_text());
				else
					new_id = netlist.new_id();

				RTLIL::SigSpec w_default = vstate.evaluate(netlist, chunk);
				RTLIL::Wire *w = netlist.canvas->addWire(new_id, chunk.bitwidth());
				if (sw->statement)
					transfer_attrs(netlist, *sw->statement, w);
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

					rule->aux_actions.push_back(
							RTLIL::SigSig(target_w, source.extract(done, chunk.bitwidth())));
					done += chunk.bitwidth();
				}
			}

			finished = true;
		}
	};

	static const ast::Statement *unwrap_statement(const ast::Statement *statement)
	{
		switch (statement->kind) {
		case ast::StatementKind::Block:
			return unwrap_statement(&statement->as<ast::BlockStatement>().body);
		case ast::StatementKind::List: {
			auto &list = statement->as<ast::StatementList>();
			if (list.list.size() == 1) {
				return unwrap_statement(list.list[0]);
			}
			break;
		}
		default: break;
		}
		return statement;
	}

	void handle(const ast::ImmediateAssertionStatement &statement)
	{
		if (netlist.settings.ignore_assertions.value_or(false))
			return;

		std::string flavor;
		switch (statement.assertionKind) {
		case ast::AssertionKind::Assert:        flavor = "assert"; break;
		case ast::AssertionKind::Assume:        flavor = "assume"; break;
		case ast::AssertionKind::CoverProperty: flavor = "cover"; break;
		default:                                netlist.add_diag(diag::AssertionUnsupported, statement.sourceRange); return;
		}

		RTLIL::IdString cell_name;

		if (containing_block &&
				unwrap_statement(containing_block->tryGetStatement()) == &statement &&
				!containing_block->name.empty()) {
			// If we are the sole statement in a block, use the block's label
			cell_name = netlist.id(*containing_block);
		} else {
			cell_name = netlist.new_id();
		}

		auto cell = netlist.canvas->addCell(cell_name, ID($check));

		context.set_effects_trigger(cell);
		cell->setParam(ID::FLAVOR, flavor);
		cell->setParam(ID::FORMAT, std::string(""));
		cell->setParam(ID::ARGS_WIDTH, 0);
		cell->setParam(ID::PRIORITY, --context.effects_priority);
		cell->setPort(ID::ARGS, {});
		cell->setPort(ID::A, netlist.ReduceBool(eval(statement.cond)));
		transfer_attrs(netlist, statement, cell);
	}

	void handle(const ast::ConcurrentAssertionStatement &stmt)
	{
		if (!netlist.settings.ignore_assertions.value_or(false)) {
			if (stmt.assertionKind == ast::AssertionKind::Expect) {
				netlist.add_diag(diag::ExpectStatementUnsupported, stmt.sourceRange);
			} else {
				netlist.add_diag(diag::SVAUnsupported, stmt.sourceRange);
			}
		}
	}

	RTLIL::SigSpec handle_call(const ast::CallExpression &call)
	{
		RTLIL::SigSpec ret;

		require(call, !call.isSystemCall());
		auto subroutine = std::get<0>(call.subroutine);
		auto arg_symbols = subroutine->getArguments();

		std::vector<RTLIL::SigSpec> arg_in, arg_out;

		for (int i = 0; i < (int)arg_symbols.size(); i++) {
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

			for (auto &member : subroutine->members())
				if (ast::VariableSymbol::isKind(member.kind)) {
					auto &var = member.as<ast::VariableSymbol>();

					if (var.kind == ast::SymbolKind::FormalArgument ||
							var.flags.has(ast::VariableFlags::CompilerGenerated))
						var.visit(*this);
				}

			for (int i = 0; i < (int)arg_symbols.size(); i++) {
				auto dir = arg_symbols[i]->direction;
				if (dir == ast::ArgumentDirection::In || dir == ast::ArgumentDirection::InOut)
					context.do_simple_assign(loc, eval.variable(*arg_symbols[i]), arg_in[i], true);
			}

			{
				RegisterEscapeConstructGuard escape_guard(
						context, EscapeConstructKind::FunctionBody, subroutine);
				subroutine->getBody().visit(*this);
			}

			for (int i = 0; i < (int)arg_symbols.size(); i++) {
				auto dir = arg_symbols[i]->direction;
				if (dir == ast::ArgumentDirection::Out || dir == ast::ArgumentDirection::InOut)
					arg_out.push_back(eval(*arg_symbols[i]));
				else
					arg_out.push_back({});
			}

			if (subroutine->returnValVar)
				ret = eval(*subroutine->returnValVar);
		}

		for (int i = 0; i < (int)arg_symbols.size(); i++) {
			const ast::Expression *arg = call.arguments()[i];
			auto dir = arg_symbols[i]->direction;

			if (dir == ast::ArgumentDirection::Out || dir == ast::ArgumentDirection::InOut)
				context.assign_rvalue(arg->as<ast::AssignmentExpression>(), arg_out[i]);
		}

		return ret;
	}

	void handle(const ast::ExpressionStatement &stmt) { eval(stmt.expr); }

	void handle(const ast::BlockStatement &blk)
	{
		require(blk, blk.blockKind == ast::StatementBlockKind::Sequential)
				EnterAutomaticScopeGuard guard(context.eval, blk.blockSymbol);

		if (blk.blockSymbol) {
			ast_invariant(*blk.blockSymbol, blk.blockSymbol->tryGetStatement() == &blk);
			const ast::StatementBlockSymbol *symbol_save = containing_block;
			containing_block = blk.blockSymbol;
			blk.body.visit(*this);
			containing_block = symbol_save;
		} else {
			blk.body.visit(*this);
		}
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
				context.do_simple_assign(
						slang::SourceLocation::NoLocation, disable, RTLIL::S0, true);
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

		RTLIL::SigSpec condition = netlist.ReduceBool(eval(*cond.conditions[0].expr));
		SwitchHelper b(context.current_case, context.vstate, condition);
		b.sw->statement = &cond;

		b.branch({RTLIL::S1}, [&]() {
			context.current_case->statement = &cond.ifTrue;
			cond.ifTrue.visit(*this);
		});

		if (cond.ifFalse) {
			b.branch({}, [&]() {
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
		case Condition::WildcardXOrZ: match_x = match_z = true; break;
		default:                      match_x = match_z = false; break;
		}

		RTLIL::SigSpec dispatch = eval(stmt.expr);
		SwitchHelper b(context.current_case, context.vstate,
				stmt.condition == ast::CaseStatementCondition::Inside ? RTLIL::SigSpec(RTLIL::S1)
																	  : dispatch);

		b.sw->statement = &stmt;
		switch (stmt.check) {
		case ast::UniquePriorityCheck::Priority: b.sw->full_case = true; break;
		case ast::UniquePriorityCheck::Unique:
			b.sw->full_case = true;
			b.sw->parallel_case = true;
			break;
		case ast::UniquePriorityCheck::Unique0: b.sw->parallel_case = true; break;
		case ast::UniquePriorityCheck::None:    break;
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

	void handle(const ast::WhileLoopStatement &stmt)
	{
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
				context.do_simple_assign(
						slang::SourceLocation::NoLocation, guard1.flag, RTLIL::S0, true);
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

	void handle(const ast::ForLoopStatement &stmt)
	{
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

	void handle(const ast::EmptyStatement &) {}

	void init_nonstatic_variable(const ast::ValueSymbol &symbol)
	{
		Variable target = eval.variable(symbol);
		log_assert((bool)target);

		if (!target.bitwidth())
			return;

		RTLIL::SigSpec initval;
		if (symbol.getInitializer()) {
			initval = eval(*symbol.getInitializer());
		} else {
			auto converted =
					netlist.convert_const(symbol.getType().getDefaultValue(), symbol.location);
			if (converted) {
				initval = *converted;
			} else {
				initval = {RTLIL::Sx, target.bitwidth()};
			}
		}
		context.do_simple_assign(symbol.location, target, initval, true);
	}

	void handle(const ast::VariableSymbol &symbol)
	{
		if (symbol.lifetime != ast::VariableLifetime::Static) {
			init_nonstatic_variable(symbol);
		}
	}
	void handle(const ast::VariableDeclStatement &stmt) { stmt.symbol.visit(*this); }

	void handle(const ast::BreakStatement &brk)
	{
		context.signal_escape(brk.sourceRange.start(), EscapeConstructKind::Loop);
	}

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
			context.do_simple_assign(stmt.sourceRange.start(),
					eval.variable(*subroutine->returnValVar), eval(*stmt.expr), true);
		}

		context.signal_escape(stmt.sourceRange.start(), EscapeConstructKind::FunctionBody);
	}

	void handle(const ast::TimedStatement &stmt)
	{
		if (!netlist.settings.ignore_timing.value_or(false))
			netlist.add_diag(diag::GenericTimingUnsyn, stmt.timing.sourceRange);

		stmt.stmt.visit(*this);
	}

	void handle(const ast::WaitStatement &stmt)
	{
		netlist.add_diag(diag::WaitStatementUnsupported, stmt.sourceRange);
	}

	void handle(const ast::Statement &stmt)
	{
		netlist.add_diag(diag::LangFeatureUnsupported, stmt.sourceRange.start());
	}

	void handle(const ast::Expression &expr) { unimplemented(expr); }
};

}; // namespace slang_frontend
