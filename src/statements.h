//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#pragma once

#include "kernel/rtlil.h"

#include "cases.h"
#include "slang/ast/ASTVisitor.h"
#include "slang_frontend.h"
#include "variables.h"

namespace slang_frontend {

struct StatementExecutor : public ast::ASTVisitor<StatementExecutor, ast::VisitFlags::Statements>
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

#ifdef SLANG_MUX_LOWERING
	struct SwitchHelper
	{
		using VariableState = ProceduralContext::VariableState;
		ProceduralContext &context;
		VariableState &vstate;
		VariableState::Snapshot save_snap;

		ir::Value dispatch;
		struct CaseInfo
		{
			std::vector<ValuePattern> compare;
			ir::Net cond;
		};

		std::optional<CaseInfo> current_case_info;
		std::vector<std::tuple<CaseInfo, VariableBits, ir::Value>> branch_updates;
		bool finished = false;

		// Enable coming from upstream of the current switch
		ir::Net original_enabled;
		// `original_enabled` with masking to account for already
		// processed branches
		ir::Net masked_enabled;

		SwitchHelper(ProceduralContext &context, ir::Value signal,
				const ast::Statement *statement = nullptr)
			: context(context), vstate(context.vstate), dispatch(signal),
			  original_enabled(context.enabled), masked_enabled(context.enabled)
		{}

		~SwitchHelper()
		{
			log_assert(!current_case_info.has_value());
			log_assert(branch_updates.empty() || finished);
		}

		SwitchHelper(const SwitchHelper &) = delete;
		SwitchHelper &operator=(const SwitchHelper &) = delete;
		SwitchHelper(SwitchHelper &&other)
			: context(other.context), vstate(other.vstate), dispatch(std::move(other.dispatch)),
			  current_case_info(std::move(other.current_case_info)),
			  original_enabled(other.original_enabled), masked_enabled(other.masked_enabled),
			  finished(other.finished)
		{
			branch_updates.swap(other.branch_updates);
			std::swap(save_snap, other.save_snap);
			other.current_case_info = std::nullopt;
			other.finished = false;
		}

		ir::Net compute_condition(NetlistContext &netlist, const std::vector<ValuePattern> &compare)
		{
			if (compare.empty())
				return ir::S1;

			ir::Net cond = ir::S0;
			for (auto &pat : compare)
				cond = netlist.LogicOr(cond, matches_pattern(netlist, pat, dispatch));
			return cond;
		}

		void enter_branch(
				std::vector<ValuePattern> compare, const ast::Statement *case_statement = nullptr)
		{
			auto &netlist = context.netlist;
			save_snap = {};
			vstate.save(save_snap);
			log_assert(!current_case_info.has_value());
			ir::Net cond = compute_condition(netlist, compare);
			current_case_info = CaseInfo{compare, cond};
			context.enabled = netlist.LogicAnd(masked_enabled, ir::Value(cond));
		}

		void exit_branch()
		{
			auto &netlist = context.netlist;
			log_assert(current_case_info.has_value());
			masked_enabled =
					netlist.LogicAnd(masked_enabled, netlist.LogicNot(current_case_info->cond));
			auto updates = vstate.restore(save_snap);
			std::optional<CaseInfo> info;
			info.swap(current_case_info);
			branch_updates.push_back(std::make_tuple(*info, updates.first, updates.second));
		}

		void branch(std::vector<ValuePattern> compare, std::function<void()> f,
				const ast::Statement *case_statement = nullptr)
		{
			if (compare.size() == 1 && compare[0].is_fully_concrete() && dispatch.is_fully_def() &&
					dispatch != lower_pattern(compare[0])) {
				return;
			}

			enter_branch(compare, case_statement);
			f();
			exit_branch();
		}

		bool detect_full_case()
		{
			int full_width = dispatch.size();
			int width = full_width;
			while (width > 0 && dispatch[width - 1] == ir::S0)
				width--;
			if (width == 0 || width > 16)
				return false;

			int total = 1 << width;
			std::vector<bool> covered(total, false);
			for (auto &[case1, target, updates] : branch_updates) {
				if (case1.compare.empty()) {
					std::fill(covered.begin(), covered.end(), true);
				} else {
					for (auto &pat : case1.compare) {
						if (pat.size() < width)
							continue;

						bool skip_pattern = false;
						for (int i = width; i < pat.size(); i++) {
							if (pat.bits[i] != PatternBit(ir::S0)) {
								skip_pattern = true;
								break;
							}
						}
						if (skip_pattern)
							continue;

						uint64_t base = 0;
						uint64_t dc_mask = 0;

						for (int i = 0; i < width; i++) {
							auto bit = pat.bits[i];
							if (bit.is_wildcard()) {
								dc_mask |= ((uint64_t)1) << i;
							} else if (pat.bits[i] == PatternBit(ir::S1)) {
								base |= ((uint64_t)1) << i;
							} else if (pat.bits[i] == PatternBit(ir::S0)) {
								// do nothing
							} else {
								skip_pattern = true;
							}
						}
						if (skip_pattern)
							continue;

						for (uint64_t dc_val = 0;; dc_val = (((dc_val | ~dc_mask) + 1) & dc_mask)) {
							covered[base | dc_val] = true;
							if (dc_val == dc_mask)
								break;
						}
					}
				}
			}

			for (int i = 0; i < total; i++)
				if (!covered[i])
					return false;

			return true;
		}

		void finish(NetlistContext &netlist, bool full_case = false, bool parallel_case = false)
		{
			if (!full_case)
				full_case = detect_full_case();

			VariableBits updated_anybranch;
			for (auto &branch : branch_updates)
				updated_anybranch.append(std::get<1>(branch));
			updated_anybranch.sort_and_unify();

			Yosys::pool<Variable> eos_variables;
			auto &va = vstate.visible_assignments;
			for (auto bit : updated_anybranch)
				if (bit.variable.kind != Variable::Static && !va.count(bit))
					eos_variables.insert(bit.variable);

			ir::Value background;
			for (auto chunk : updated_anybranch.chunks()) {
				if (chunk.variable.kind != Variable::Static &&
						eos_variables.count(chunk.variable)) {
					for (int i = 0; i < chunk.bitwidth(); i++)
						log_assert(!va.count(chunk[i]));
					background.append(ir::Value(ir::Sx, chunk.bitwidth()));
					continue;
				}
				background.append(vstate.evaluate(netlist, chunk));
				if (full_case)
					vstate.set(chunk, ir::Value(ir::Sx, chunk.bitwidth()));
			}

			for (auto it = branch_updates.rbegin(); it != branch_updates.rend(); it++) {
				auto &[info, target, updates] = *it;

				int done = 0;
				for (auto chunk : updated_anybranch.chunks()) {
					if (eos_variables.count(chunk.variable)) {
						done += chunk.bitwidth();
						continue;
					}

					ir::Value chunk_updated;
					for (int i = 0; i < chunk.bitwidth(); i++) {
						auto lb = std::lower_bound(target.begin(), target.end(), chunk[i]);
						bool exists = (lb != target.end() && *lb == chunk[i]);
						if (exists)
							chunk_updated.append(updates[lb - target.begin()]);
						else
							chunk_updated.append(background[done + i]);
					}
					vstate.set(chunk,
							netlist.Mux(vstate.evaluate(netlist, chunk), chunk_updated, info.cond));
					done += chunk.bitwidth();
				}
			}

			context.enabled = original_enabled;
			finished = true;
		}
	};
#else
	struct SwitchHelper
	{
		Case *parent;
		Case *&current_case;
		Switch *sw;

		using VariableState = ProceduralContext::VariableState;

		VariableState &vstate;
		VariableState::Snapshot save_snap;
		std::vector<std::tuple<Case *, VariableBits, ir::Value>> branch_updates;
		bool entered = false, finished = false;

		SwitchHelper(ProceduralContext &context, ir::Value signal,
				const ast::Statement *statement = nullptr)
			: parent(context.current_case), current_case(context.current_case),
			  vstate(context.vstate)
		{
			sw = parent->add_switch(signal);
			sw->statement = statement;
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
			std::swap(save_snap, other.save_snap);
			other.entered = false;
			other.finished = false;
		}

		void enter_branch(
				std::vector<ValuePattern> compare, const ast::Statement *case_statement = nullptr)
		{
			save_snap = {};
			vstate.save(save_snap);
			log_assert(!entered);
			log_assert(current_case == parent);
			current_case = sw->add_case(compare);
			current_case->statement = case_statement;
			entered = true;
		}

		void exit_branch()
		{
			log_assert(entered);
			log_assert(current_case != parent);
			Case *this_case = current_case;
			current_case = parent;
			entered = false;
			auto updates = vstate.restore(save_snap);
			branch_updates.push_back(std::make_tuple(this_case, updates.first, updates.second));
		}

		void branch(std::vector<ValuePattern> compare, std::function<void()> f,
				const ast::Statement *case_statement = nullptr)
		{
			// TODO: extend detection
			if (compare.size() == 1 && compare[0].is_fully_def() && sw->signal.is_fully_def() &&
					sw->signal != lower_pattern(compare[0])) {
				// dead branch
				return;
			}

			enter_branch(compare, case_statement);
			f();
			exit_branch();
		}

		void finish(NetlistContext &netlist, bool full_case = false, bool parallel_case = false)
		{
			sw->full_case = full_case;
			sw->parallel_case = parallel_case;
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
					for (uint64_t i = 0; i < chunk.bitwidth(); i++)
						log_assert(!va.count(chunk[i]));

					continue;
				}

				std::string name_suggestion;
				if (auto symbol = chunk.variable.get_symbol())
					name_suggestion = RTLIL::unescape_id(netlist.id(*symbol)) + chunk.slice_text();

				AttributeGuard guard(netlist);
				if (sw->statement)
					transfer_attrs(netlist, *sw->statement, guard);

				ir::Value w_default = vstate.evaluate(netlist, chunk);
				ir::Value w = netlist.add_placeholder_signal(chunk.bitwidth(), name_suggestion);
				parent->aux_actions.push_back(RTLIL::SigSig(w, w_default));
				vstate.set(chunk, w);
			}

			for (auto &branch : branch_updates) {
				Case *rule;
				VariableBits target;
				ir::Value source;
				std::tie(rule, target, source) = branch;

				int done = 0;
				for (auto chunk : target.chunks()) {
					if (eos_variables.count(chunk.variable)) {
						done += (int)chunk.bitwidth();
						continue;
					}

					// get the wire (or some part of it) which we created up above
					ir::Value target_w;
					for (uint64_t i = 0; i < chunk.bitwidth(); i++) {
						log_assert(va.count(chunk[i]));
						target_w.append(va.at(chunk[i]));
					}

					rule->aux_actions.push_back(
							RTLIL::SigSig(target_w, source.extract(done, (int)chunk.bitwidth())));
					done += (int)chunk.bitwidth();
				}
			}

			finished = true;
		}
	};
#endif

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
		cell->setPort(ID::A, {netlist.ReduceBool(eval(statement.cond))});
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

	ir::Value handle_call(const ast::CallExpression &call)
	{
		ir::Value ret;

		require(call, !call.isSystemCall());
		auto subroutine = std::get<0>(call.subroutine);
		auto arg_symbols = subroutine->getArguments();

		std::vector<ir::Value> arg_in, arg_out;

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
					arg_out.push_back(context.substitute_rvalue(eval.variable(*arg_symbols[i])));
				else
					arg_out.push_back({});
			}

			if (subroutine->returnValVar)
				ret = context.substitute_rvalue(eval.variable(*subroutine->returnValVar));
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
			ir::Value disable_rv = disable ? context.substitute_rvalue(disable) : ir::Value(ir::S0);
			if (!disable_rv.is_fully_const()) {
				auto &b = sw_stack.emplace_back(context, disable_rv, stmt);
				b.enter_branch({ir::S0}, stmt);

				// From a semantical POV the following is a no-op, but it allows us to
				// do more constant folding.
				context.do_simple_assign(slang::SourceLocation::NoLocation, disable, ir::S0, true);
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

		ir::Net condition = netlist.ReduceBool(eval(*cond.conditions[0].expr));

		if (condition.is_def()) {
			if (condition == ir::S1) {
				cond.ifTrue.visit(*this);
				return;
			} else if (condition == ir::S0) {
				if (cond.ifFalse)
					cond.ifFalse->visit(*this);
				return;
			}
			// fall through on Sx
		}

		SwitchHelper b(context, condition);
		b.branch({ir::S1}, [&]() { cond.ifTrue.visit(*this); }, &cond.ifTrue);
		if (cond.ifFalse) {
			b.branch({}, [&]() { cond.ifFalse->visit(*this); }, cond.ifFalse);
		}
		b.finish(netlist);

		// descend into an empty switch so we force action priority for follow-up statements
		context.descend_into_empty_case();
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

		ir::Value dispatch = eval(stmt.expr);
		SwitchHelper b(context,
				stmt.condition == ast::CaseStatementCondition::Inside ? ir::Value(ir::S1)
																	  : dispatch,
				&stmt);

		bool full_case = false, parallel_case = false;
		switch (stmt.check) {
		case ast::UniquePriorityCheck::Priority: full_case = true; break;
		case ast::UniquePriorityCheck::Unique:   full_case = parallel_case = true; break;
		case ast::UniquePriorityCheck::Unique0:  parallel_case = true; break;
		case ast::UniquePriorityCheck::None:     break;
		}

		for (auto item : stmt.items) {
			std::vector<ValuePattern> compares;
			for (auto expr : item.expressions) {
				log_assert(expr);

				if (stmt.condition == ast::CaseStatementCondition::Inside) {
					require(stmt, stmt.expr.type->isIntegral());
					compares.push_back(inside_comparison(eval, dispatch, *expr));
					continue;
				}

				if (match_z || match_x) {
					auto const_result = expr->eval(eval.const_);
					if (const_result && const_result.isInteger()) {
						auto pat = svint_to_pattern(netlist, const_result.integer(), match_x,
								match_z, expr->sourceRange.start());
						log_assert(pat.size() == dispatch.size());
						compares.push_back(std::move(pat));
						continue;
					}
				}

				ValuePattern compare = eval(*expr);
				if (match_x) {
					for (auto &bit : compare.bits) {
						if (bit == PatternBit(ir::Sx)) {
							bit = PatternBit::wildcard();
						}
					}
				}
				log_assert(compare.size() == dispatch.size());
				compares.push_back(compare);
			}
			require(stmt, !compares.empty());
			b.branch(compares, [&]() { item.stmt->visit(*this); }, item.stmt);
		}

		if (stmt.defaultCase) {
			b.branch(
					std::vector<ValuePattern>{}, [&]() { stmt.defaultCase->visit(*this); },
					stmt.defaultCase);
		}
		b.finish(netlist, full_case, parallel_case);

		context.descend_into_empty_case();
	}

	void handle(const ast::WhileLoopStatement &stmt)
	{
		RegisterEscapeConstructGuard guard1(context, EscapeConstructKind::Loop, &stmt);
		std::vector<SwitchHelper> sw_stack;
		unroll_limit.enter_unrolling();
		while (true) {
			ir::Value cv = netlist.ReduceBool(eval(stmt.cond));
			ir::Value break_rv = context.vstate.evaluate(netlist, guard1.flag);
			ir::Value joint_break = netlist.LogicOr(netlist.LogicNot(cv), break_rv);

			if (!joint_break.is_fully_const()) {
				auto &b = sw_stack.emplace_back(context, joint_break, &stmt);
				b.enter_branch({ir::S0}, &stmt.body);

				// From a semantical POV the following is a no-op, but it allows us to
				// do more constant folding.
				context.do_simple_assign(
						slang::SourceLocation::NoLocation, guard1.flag, ir::S0, true);
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

		context.descend_into_empty_case();
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
			ir::Value cv = netlist.ReduceBool(eval(*stmt.stopExpr));

			if (!cv.is_fully_const()) {
				auto &b = sw_stack.emplace_back(context, cv, &stmt);
				b.enter_branch({ir::S1}, &stmt.body);
			} else if (!cv.as_bool()) {
				break;
			} else {
				log_assert(cv.as_bool());
			}

			{
				RegisterEscapeConstructGuard guard2(context, EscapeConstructKind::LoopBody, &stmt);
				stmt.body.visit(*this);
			}

			ir::Value break_rv = context.substitute_rvalue(guard1.flag);

			if (!break_rv.is_fully_const()) {
				auto &b = sw_stack.emplace_back(context, break_rv, &stmt);
				b.enter_branch({ir::S0}, &stmt.body);
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

		context.descend_into_empty_case();
	}

	void handle(const ast::ForeachLoopStatement &stmt)
	{
		auto set_iterator_value = [this, &stmt](const ast::VariableSymbol &target, int32_t value) {
			context.do_simple_assign(
					stmt.sourceRange.start(), eval.variable(target), RTLIL::Const(value, 32), true);
		};

		std::vector<SwitchHelper> sw_stack;
		std::vector<std::optional<int32_t>> loopVarStack(stmt.loopDims.size(), std::nullopt);
		// Initialize loop vars ranges
		for (auto i = 0; i < stmt.loopDims.size(); ++i) {
			auto loopDim = stmt.loopDims[i];
			if (loopDim.loopVar && loopDim.range) {
				loopVarStack[loopVarStack.size() - i - 1] = loopDim.range->left;
				set_iterator_value(*loopDim.loopVar, loopDim.range->left);
			}
		}

		std::vector<slang::ast::ForeachLoopStatement::LoopDim> reversedDims(
				stmt.loopDims.rbegin(), stmt.loopDims.rend());
		for (auto i = 0; i < loopVarStack.size(); ++i) {
			if (loopVarStack[i]) {
				auto currDim = reversedDims[i];
			}
		}

		RegisterEscapeConstructGuard guard1(context, EscapeConstructKind::Loop, &stmt);
		unroll_limit.enter_unrolling();
		while (true) {
			{
				RegisterEscapeConstructGuard guard2(context, EscapeConstructKind::LoopBody, &stmt);
				stmt.body.visit(*this);
			}

			ir::Value break_rv = context.substitute_rvalue(guard1.flag);

			if (!break_rv.is_fully_const()) {
				auto &b = sw_stack.emplace_back(context, break_rv, &stmt);
				b.enter_branch({ir::S0}, &stmt.body);
			} else if (break_rv.as_bool()) {
				break;
			} else {
				log_assert(!break_rv.as_bool());
			}

			bool doBreak = true;
			for (int i = 0; i < loopVarStack.size(); ++i) {
				if (!loopVarStack[i])
					continue;

				if (*loopVarStack[i] != reversedDims[i].range->right) {
					*loopVarStack[i] = *loopVarStack[i] > reversedDims[i].range->right
											   ? *loopVarStack[i] - 1
											   : *loopVarStack[i] + 1;
					doBreak = false;
					break;
				} else if (i != loopVarStack.size() - 1) {
					bool nextDimFound = false;
					int j = i + 1;
					for (; j < loopVarStack.size(); ++j) {
						if (loopVarStack[j] && *loopVarStack[j] != reversedDims[j].range->right) {
							nextDimFound = true;
							break;
						}
					}

					if (nextDimFound) {
						*loopVarStack[j] = *loopVarStack[j] > reversedDims[j].range->right
												   ? *loopVarStack[j] - 1
												   : *loopVarStack[j] + 1;
						doBreak = false;
						for (int k = 0; k < j; ++k) {
							if (loopVarStack[k])
								*loopVarStack[k] = reversedDims[k].range->left;
						}

						break;
					}
				}
			}

			for (auto i = 0; i < loopVarStack.size(); ++i) {
				if (loopVarStack[i]) {
					auto currDim = reversedDims[i];
					set_iterator_value(*currDim.loopVar, *loopVarStack[i]);
				}
			}

			if (doBreak || !unroll_limit.unroll_tick(&stmt))
				break;
		}
		unroll_limit.exit_unrolling();

		for (auto it = sw_stack.rbegin(); it != sw_stack.rend(); it++) {
			it->exit_branch();
			it->finish(netlist);
		}

		context.descend_into_empty_case();
	}

	void handle(const ast::EmptyStatement &) {}

	void init_nonstatic_variable(const ast::ValueSymbol &symbol)
	{
		Variable target = eval.variable(symbol);
		log_assert((bool)target);

		if (!target.bitwidth())
			return;

		ir::Value initval;
		if (symbol.getInitializer()) {
			initval = eval(*symbol.getInitializer());
		} else {
			auto converted =
					netlist.convert_const(symbol.getType().getDefaultValue(), symbol.location);
			if (converted) {
				initval = *converted;
			} else {
				initval = ir::Value(ir::Sx, target.bitwidth());
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
