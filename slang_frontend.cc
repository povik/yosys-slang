//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/driver/Driver.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/text/Json.h"
#include "slang/util/Util.h"

#include "kernel/fmt.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"

PRIVATE_NAMESPACE_BEGIN

using Yosys::log;
using Yosys::log_error;
using Yosys::log_warning;
using Yosys::log_id;
using Yosys::ys_debug;
using Yosys::ceil_log2;

namespace RTLIL = Yosys::RTLIL;
namespace ast = slang::ast;

ast::Compilation *global_compilation;
const slang::SourceManager *global_sourcemgr;

template<typename T>
void unimplemented_(const T &obj, const char *file, int line, const char *condition)
{
	slang::JsonWriter writer;
	writer.setPrettyPrint(true);
	ast::ASTSerializer serializer(*global_compilation, writer);
	serializer.serialize(obj);
	std::cout << writer.view() << std::endl;
	log_error("Feature unimplemented at %s:%d, see AST dump above%s%s%s\n",
			  file, line, condition ? " (failed condition \"" : "", condition ? condition : "", condition ? "\")" : "");
}
#define require(obj, property) { if (!(property)) unimplemented_(obj, __FILE__, __LINE__, #property); }
#define unimplemented(obj) { unimplemented_(obj, __FILE__, __LINE__, NULL); }

const RTLIL::IdString id(const std::string_view &view)
{
	return RTLIL::escape_id(std::string(view));
}

static const RTLIL::IdString net_id(const ast::Symbol &symbol)
{
	std::string hierPath;
	symbol.getHierarchicalPath(hierPath);
	return RTLIL::escape_id(hierPath);
}

static const RTLIL::Const svint_const(const slang::SVInt &svint)
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

template<typename T>
void transfer_attrs(T &from, RTLIL::AttrObject *to)
{
	auto sm = global_sourcemgr;
	auto &sr = from.sourceRange;
	if (sm->isFileLoc(sr.start()) && sm->isFileLoc(sr.end())) {
		std::string fn{sm->getFileName(sr.start())};
		to->set_src_attribute(Yosys::stringf("%s:%d.%d-%d.%d",
			fn.c_str(), (int) sm->getLineNumber(sr.start()), (int) sm->getColumnNumber(sr.start()),
			(int) sm->getLineNumber(sr.end()), (int) sm->getColumnNumber(sr.end())));
	}

	for (auto attr : global_compilation->getAttributes(from)) {
		require(*attr, attr->getValue().isInteger());
		to->attributes[id(attr->name)] = svint_const(attr->getValue().integer());
	}
}

template<typename T>
void transfer_attrs2(T &from, RTLIL::AttrObject *to)
{
	auto sm = global_sourcemgr;
	auto &loc = from.location;
	if (sm->isFileLoc(loc)) {
		std::string fn{sm->getFileName(loc)};
		to->set_src_attribute(Yosys::stringf("%s:%d.%d",
			fn.c_str(), (int) sm->getLineNumber(loc), (int) sm->getColumnNumber(loc)));
	}

	for (auto attr : global_compilation->getAttributes(from)) {
		require(*attr, attr->getValue().isInteger());
		to->attributes[id(attr->name)] = svint_const(attr->getValue().integer());
	}
}


static const RTLIL::SigSpec evaluate_lhs(RTLIL::Module *mod, const ast::Expression &expr)
{
	RTLIL::SigSpec ret;

	switch (expr.kind) {
	case ast::ExpressionKind::NamedValue:
		{
			const ast::Symbol &sym = expr.as<ast::NamedValueExpression>().symbol;
			RTLIL::Wire *wire = mod->wire(net_id(sym));
			log_assert(wire);
			ret = wire;
		}
		break;
	case ast::ExpressionKind::RangeSelect:
		{
			const ast::RangeSelectExpression &sel = expr.as<ast::RangeSelectExpression>();
			require(expr, sel.getSelectionKind() == ast::RangeSelectionKind::Simple);
			require(expr, sel.right().constant && sel.left().constant);
			int right = sel.right().constant->integer().as<int>().value(); // TODO: left vs right
			int left = sel.left().constant->integer().as<int>().value();

			ret = evaluate_lhs(mod, sel.value()).extract(right, left - right + 1);
		}
		break;
	case ast::ExpressionKind::Concatenation:
		{
			const ast::ConcatenationExpression &concat = expr.as<ast::ConcatenationExpression>();
			for (auto op : concat.operands())
				ret = {ret, evaluate_lhs(mod, *op)};
		}
		break;
	case ast::ExpressionKind::ElementSelect:
		{
			const ast::ElementSelectExpression &elemsel = expr.as<ast::ElementSelectExpression>();
			require(expr, elemsel.selector().constant);
			require(expr, elemsel.value().type->getArrayElementType()); // TODO: extend
			int idx = elemsel.selector().constant->integer().as<int>().value();
			int stride = elemsel.value().type->getArrayElementType()->getBitWidth();
			ret = evaluate_lhs(mod, elemsel.value()).extract(stride * idx, stride);
		}
		break;
	default:
		unimplemented(expr);
		break;
	}

	log_assert(ret.size() == (int) expr.type->getBitstreamWidth());
	return ret;
}

static const RTLIL::SigSpec evaluate_rhs(RTLIL::Module *mod, const ast::Expression &expr,
										 const Yosys::dict<RTLIL::SigBit, RTLIL::SigBit> *subs)
{
	RTLIL::SigSpec ret;

	{
		// TODO: we seem to need this for `expr.constant`, are we using it right?
		ast::ASTContext ctx(global_compilation->getRoot(), ast::LookupLocation::max);
		ctx.tryEval(expr);
	}

	if (true && expr.constant) {
		ret = svint_const(expr.constant->integer());
		goto done;
	}

	switch (expr.kind) {
	case ast::ExpressionKind::NamedValue:
		{
			const ast::Symbol &sym = expr.as<ast::NamedValueExpression>().symbol;

			switch (sym.kind) {
			case ast::SymbolKind::Net:
			case ast::SymbolKind::Variable:
				{
					RTLIL::Wire *wire = mod->wire(net_id(sym));
					log_assert(wire);
					ret = wire;
					if (subs)
						ret.replace(*subs);
				}
				break;
			case ast::SymbolKind::Parameter:
				{
					auto &valsym = sym.as<ast::ValueSymbol>();
					require(valsym, valsym.getInitializer());
					auto exprconst = valsym.getInitializer()->constant;
					require(valsym, exprconst && exprconst->isInteger());
					ret = svint_const(exprconst->integer());
				}
				break;
			default:
				unimplemented(sym);
			}
		}
		break;
	case ast::ExpressionKind::UnaryOp:
		{
			const ast::UnaryExpression &unop = expr.as<ast::UnaryExpression>();
			RTLIL::SigSpec left = evaluate_rhs(mod, unop.operand(), subs);
			bool invert = false;

			RTLIL::IdString type;
			switch (unop.op) {
			case ast::UnaryOperator::LogicalNot: type = ID($logic_not); break;
			case ast::UnaryOperator::BitwiseNot: type = ID($not); break;
			case ast::UnaryOperator::BitwiseOr: type = ID($reduce_or); break;
			case ast::UnaryOperator::BitwiseAnd: type = ID($reduce_and); break;
			case ast::UnaryOperator::BitwiseNand: type = ID($reduce_and); invert = true; break;
			default:
				unimplemented(unop);
			}

			RTLIL::Cell *cell = mod->addCell(NEW_ID, type);
			cell->setPort(RTLIL::ID::A, left);
			cell->setParam(RTLIL::ID::A_WIDTH, left.size());
			cell->setParam(RTLIL::ID::A_SIGNED, unop.operand().type->isSigned());
			cell->setParam(RTLIL::ID::Y_WIDTH, expr.type->getBitstreamWidth());
			ret = mod->addWire(NEW_ID, expr.type->getBitstreamWidth());
			cell->setPort(RTLIL::ID::Y, ret);
			transfer_attrs(unop, cell);

			if (invert) {
				RTLIL::SigSpec new_ret = mod->addWire(NEW_ID, 1);
				transfer_attrs(unop, mod->addLogicNot(NEW_ID, ret, new_ret));
			}
		}
		break;
	case ast::ExpressionKind::BinaryOp:
		{
			const ast::BinaryExpression &biop = expr.as<ast::BinaryExpression>();
			RTLIL::SigSpec left = evaluate_rhs(mod, biop.left(), subs);
			RTLIL::SigSpec right = evaluate_rhs(mod, biop.right(), subs);

			RTLIL::IdString type;
			switch (biop.op) {
			case ast::BinaryOperator::Add:      type = ID($add); break;
			case ast::BinaryOperator::Subtract: type = ID($sub); break;
			case ast::BinaryOperator::Multiply:	type = ID($mul); break;
			case ast::BinaryOperator::Divide:	type = ID($divfloor); break; // TODO: check
			case ast::BinaryOperator::Mod:		type = ID($mod); break; // TODO: check
			case ast::BinaryOperator::BinaryAnd: type = ID($and); break;
			case ast::BinaryOperator::BinaryOr:	type = ID($or); break;
			case ast::BinaryOperator::BinaryXor:	type = ID($xor); break;
			case ast::BinaryOperator::BinaryXnor:	type = ID($xnor); break;
			case ast::BinaryOperator::Equality:		type = ID($eq); break;
			case ast::BinaryOperator::Inequality:	type = ID($ne); break;
			//case ast::BinaryOperator::CaseEquality;
			//case ast::BinaryOperator::CaseInequality;
			case ast::BinaryOperator::GreaterThanEqual:	type = ID($ge); break;
			case ast::BinaryOperator::GreaterThan:		type = ID($gt); break;
			case ast::BinaryOperator::LessThanEqual:	type = ID($le); break;
			case ast::BinaryOperator::LessThan:			type = ID($lt); break;
			//case ast::BinaryOperator::WildcardEquality;
			//case ast::BinaryOperator::WildcardInequality;
			case ast::BinaryOperator::LogicalAnd:	type = ID($logic_and); break;
			case ast::BinaryOperator::LogicalOr:	type = ID($logic_or); break;
			//case ast::BinaryOperator::LogicalImplication;
			//case ast::BinaryOperator::LogicalEquivalence;
			case ast::BinaryOperator::LogicalShiftLeft:	type = ID($sshl); break;
			case ast::BinaryOperator::LogicalShiftRight:	type = ID($sshr); break;
			case ast::BinaryOperator::ArithmeticShiftLeft:	type = ID($shl); break; // TODO: check shl vs sshl
			case ast::BinaryOperator::ArithmeticShiftRight:	type = ID($shr); break;
			case ast::BinaryOperator::Power:	type = ID($pow); break;
			default:
				unimplemented(biop);
			}

			RTLIL::Cell *cell = mod->addCell(NEW_ID, type);
			cell->setPort(RTLIL::ID::A, left);
			cell->setPort(RTLIL::ID::B, right);
			cell->setParam(RTLIL::ID::A_WIDTH, left.size());
			cell->setParam(RTLIL::ID::B_WIDTH, right.size());
			cell->setParam(RTLIL::ID::A_SIGNED, biop.left().type->isSigned());
			cell->setParam(RTLIL::ID::B_SIGNED, biop.right().type->isSigned());
			cell->setParam(RTLIL::ID::Y_WIDTH, expr.type->getBitWidth());
			ret = mod->addWire(NEW_ID, expr.type->getBitstreamWidth());
			cell->setPort(RTLIL::ID::Y, ret);
			transfer_attrs(biop, cell);

			// fixups
			if (cell->type == ID($shr)) {
				// TODO: is this kosher?
				cell->setParam(RTLIL::ID::B_SIGNED, false);
			}

			if (cell->type.in(ID($sshr), ID($sshl))) {
				// TODO: is this kosher?
				cell->setParam(RTLIL::ID::A_SIGNED, false);
				cell->setParam(RTLIL::ID::B_SIGNED, false);
			}
		}
		break;
	case ast::ExpressionKind::Conversion:
		{
			const ast::ConversionExpression &conv = expr.as<ast::ConversionExpression>();
			const ast::Type &from = conv.operand().type->getCanonicalType();
			const ast::Type &to = conv.type->getCanonicalType();
			require(expr, from.isIntegral() /* && from.isScalar() */);
			require(expr, to.isIntegral() /* && to.isScalar() */);
			require(conv, from.isSigned() == to.isSigned() || to.getBitWidth() <= from.getBitWidth());
			ret = evaluate_rhs(mod, conv.operand(), subs);
			ret.extend_u0((int) to.getBitWidth(), to.isSigned());
		}
		break;
	case ast::ExpressionKind::IntegerLiteral:
		{
			const ast::IntegerLiteral &lit = expr.as<ast::IntegerLiteral>();
			ret = svint_const(lit.getValue());
		}
		break;
	case ast::ExpressionKind::RangeSelect:
		{
			const ast::RangeSelectExpression &sel = expr.as<ast::RangeSelectExpression>();
			require(expr, sel.getSelectionKind() == ast::RangeSelectionKind::Simple);
			require(expr, sel.right().constant && sel.left().constant);
			int right = sel.right().constant->integer().as<int>().value(); // TODO: left vs right
			int left = sel.left().constant->integer().as<int>().value();
			ret = evaluate_rhs(mod, sel.value(), subs).extract(right, left - right + 1);
		}
		break;
	case ast::ExpressionKind::ElementSelect:
		{
			const ast::ElementSelectExpression &elemsel = expr.as<ast::ElementSelectExpression>();
			require(expr, elemsel.value().type->getArrayElementType());
			int stride = elemsel.value().type->getArrayElementType()->getBitWidth();

			// TODO: check what's proper out-of-range handling
			RTLIL::SigSpec idx = evaluate_rhs(mod, elemsel.selector(), subs);
			RTLIL::SigSpec val = evaluate_rhs(mod, elemsel.value(), subs);
			log_assert(val.size() % stride == 0);
			RTLIL::SigBit valid = RTLIL::State::S1;
			if (ceil_log2(val.size() / stride) < idx.size())
				valid = mod->LogicNot(NEW_ID, idx.extract_end(ceil_log2(val.size())));

			val.extend_u0(stride * (1 << ceil_log2(val.size()))); // extend val
			idx.extend_u0(ceil_log2(val.size() / stride)); // crop idx
			ret = mod->Mux(NEW_ID, RTLIL::SigSpec(RTLIL::State::Sx, stride), mod->Bmux(NEW_ID, val, idx), valid);
		}
		break;
	case ast::ExpressionKind::Concatenation:
		{
			const ast::ConcatenationExpression &concat = expr.as<ast::ConcatenationExpression>();
			for (auto op : concat.operands())
				ret = {ret, evaluate_rhs(mod, *op, subs)};
		}
		break;
	case ast::ExpressionKind::ConditionalOp:
		{
			const auto &ternary = expr.as<ast::ConditionalExpression>();

			require(expr, ternary.conditions.size() == 1);
			require(expr, !ternary.conditions[0].pattern);

			ret = mod->Mux(NEW_ID,
				evaluate_rhs(mod, ternary.right(), subs),
				evaluate_rhs(mod, ternary.left(), subs),
				mod->ReduceBool(NEW_ID, evaluate_rhs(mod, *(ternary.conditions[0].expr), subs))
			);
		}
		break;
	case ast::ExpressionKind::Replication:
		{
			const auto &repl = expr.as<ast::ReplicationExpression>();
			require(expr, repl.count().constant); // TODO: message
			int reps = repl.count().constant->integer().as<int>().value(); // TODO: checking
			RTLIL::SigSpec concat = evaluate_rhs(mod, repl.concat(), subs);
			for (int i = 0; i < reps; i++)
				ret.append(concat);
		}
		break;
	case ast::ExpressionKind::Call:
		{
			const auto &call = expr.as<ast::CallExpression>();
			// TODO: message
			require(expr, call.getSubroutineName() == "$signed");
			require(expr, call.arguments().size() == 1);
			return evaluate_rhs(mod, *call.arguments()[0], subs);
		}
		break;
	default:
		unimplemented(expr);
	}

done:
	log_assert(ret.size() == (int) expr.type->getBitstreamWidth());
	return ret;
}

struct SwitchBuilder {
	RTLIL::CaseRule *parent;
	RTLIL::SwitchRule *sw;
	Yosys::dict<RTLIL::SigBit, RTLIL::SigBit> *rvalue_subs;
	Yosys::dict<RTLIL::SigBit, RTLIL::SigBit> rvalue_subs_save;

	std::vector<std::pair<RTLIL::CaseRule *, RTLIL::SigSig>> branch_updates;

	SwitchBuilder(RTLIL::CaseRule *parent, Yosys::dict<RTLIL::SigBit, RTLIL::SigBit> *rvalue_subs,
				  RTLIL::SigSpec signal)
		: parent(parent), rvalue_subs(rvalue_subs), rvalue_subs_save(*rvalue_subs)
	{
		sw = new RTLIL::SwitchRule;
		sw->signal = signal;
		parent->switches.push_back(sw);
	}

	void branch(std::vector<RTLIL::SigSpec> compare,
				std::function<void(RTLIL::CaseRule *case_rule)> f)
	{
		RTLIL::CaseRule *case_rule = new RTLIL::CaseRule;	
		sw->cases.push_back(case_rule);
		case_rule->compare = compare;
		f(case_rule);

		RTLIL::SigSpec update;
		for (auto pair : *rvalue_subs)
		if (!rvalue_subs_save.count(pair.first)
				|| pair.second != rvalue_subs_save.at(pair.first))
			update.append(pair.first);
		update.sort();

		RTLIL::SigSpec update_map = update;
		update_map.replace(*rvalue_subs);
		branch_updates.push_back(std::make_pair(case_rule, RTLIL::SigSig(update, update_map)));

		*rvalue_subs = rvalue_subs_save;
	}

	void finish(RTLIL::Module *mod)
	{
		RTLIL::SigSpec updated_anybranch;
		for (auto &branch : branch_updates)
			updated_anybranch.append(branch.second.first);
		updated_anybranch.sort_and_unify();

		for (auto chunk : updated_anybranch.chunks()) {
			RTLIL::SigSpec w = mod->addWire(NEW_ID, chunk.size());
			RTLIL::SigSpec w_default = chunk;
			w_default.replace(*rvalue_subs);
			parent->actions.push_back(RTLIL::SigSig(w, w_default));
			for (int i = 0; i < chunk.size(); i++)
				(*rvalue_subs)[RTLIL::SigSpec(chunk)[i]] = w[i];
		}

		for (auto &branch : branch_updates) {
			RTLIL::CaseRule *rule = branch.first;
			RTLIL::SigSpec target = branch.second.first;
			RTLIL::SigSpec source = branch.second.second;
			int done = 0;
			for (auto chunk : target.chunks()) {
				RTLIL::SigSpec target_w = chunk;
				target_w.replace(*rvalue_subs);
				rule->actions.push_back(RTLIL::SigSig(target_w, source.extract(done, chunk.size())));
				done += chunk.size();
			}
		}
	}
};

struct ProceduralVisitor : public ast::ASTVisitor<ProceduralVisitor, true, false> {
public:
	RTLIL::Module *mod;
	RTLIL::Process *proc;
	RTLIL::CaseRule *current_case;

	// rvalue substitutions from blocking assignments
	Yosys::dict<RTLIL::SigBit, RTLIL::SigBit> rvalue_subs;

	Yosys::SigPool assigned_blocking;
	Yosys::SigPool assigned_nonblocking;

	int print_priority = 0;

	ProceduralVisitor(RTLIL::Module *mod, RTLIL::Process *proc)
			: mod(mod), proc(proc) {
		RTLIL::SwitchRule *top_switch = new RTLIL::SwitchRule;
		proc->root_case.switches.push_back(top_switch);
		current_case = new RTLIL::CaseRule;
		top_switch->cases.push_back(current_case);
	}

	Yosys::dict<RTLIL::SigBit, RTLIL::SigBit> staging;
	RTLIL::SigSpec staging_signal(RTLIL::SigSpec lvalue)
	{
		RTLIL::SigSpec to_create;
		for (auto bit : lvalue) {
			log_assert(bit.wire);
			if (!staging.count(bit))
				to_create.append(bit);
		}

		to_create.sort_and_unify();
		for (auto chunk : to_create.chunks()) {
			RTLIL::SigSpec w = mod->addWire(NEW_ID_SUFFIX("staging"), chunk.size());
			for (int i = 0; i < chunk.size(); i++)
				staging[RTLIL::SigSpec(chunk)[i]] = w[i];
		}

		lvalue.replace(staging);
		return lvalue;
	}

	void staging_done()
	{
		RTLIL::SigSpec all_driven;
		for (auto pair : staging)
			all_driven.append(pair.first);
		all_driven.sort_and_unify();

		RTLIL::CaseRule *root_case = &proc->root_case;
		for (auto chunk : all_driven.chunks()) {
			RTLIL::SigSpec mapped = chunk;
			mapped.replace(staging);
			for (auto sync : proc->syncs)
				sync->actions.push_back(RTLIL::SigSig(chunk, mapped));
			root_case->actions.push_back(RTLIL::SigSig(mapped, chunk));
		}
	}

	// Return an enable signal for the current context
	RTLIL::SigBit context_enable()
	{
		RTLIL::SigBit ret = mod->addWire(NEW_ID, 1);
		proc->root_case.actions.emplace_back(ret, RTLIL::State::S0);
		current_case->actions.emplace_back(ret, RTLIL::State::S1);
		return ret;
	}

	// For $check, $print cells
	void set_cell_trigger(RTLIL::Cell *cell)
	{
		bool implicit = false;
		RTLIL::SigSpec triggers;
		RTLIL::Const polarity;

		for (auto sync : proc->syncs)
		switch(sync->type) {
		case RTLIL::STn:
		case RTLIL::STp:
			log_assert(sync->signal.size() == 1);
			triggers.append(sync->signal);
			polarity.bits.push_back(sync->type == RTLIL::STp ? RTLIL::S1 : RTLIL::S0);
			break;

		case RTLIL::STa:
			implicit = true;
			break;

		default:
			log_abort();
		}

		log_assert(!triggers.empty() || implicit);
		log_assert(!(!triggers.empty() && implicit));
		cell->parameters[Yosys::ID::TRG_ENABLE] = !implicit;
		cell->parameters[Yosys::ID::TRG_WIDTH] = triggers.size();
		cell->parameters[Yosys::ID::TRG_POLARITY] = polarity;
		cell->setPort(Yosys::ID::TRG, triggers);
		cell->setPort(Yosys::ID::EN, context_enable());
	}

	// TODO: add other kids of statements

	void handle(const ast::ExpressionStatement &expr)
	{
		switch (expr.expr.kind) {
		case ast::ExpressionKind::Call:
			{
				auto &call = expr.expr.as<ast::CallExpression>();
				if (call.getSubroutineName() == "empty_statement") {
					return; // TODO: workaround for picorv32, do better
				} else if (call.getSubroutineName() == "$display") {
					auto cell = mod->addCell(NEW_ID, ID($print));
					transfer_attrs(expr, cell);
					set_cell_trigger(cell);
					cell->parameters[Yosys::ID::PRIORITY] = --print_priority;
					std::vector<Yosys::VerilogFmtArg> fmt_args;
					for (auto arg : call.arguments()) {
						log_assert(arg);
						Yosys::VerilogFmtArg fmt_arg = {};
						// TODO: location info in fmt_arg
						switch (arg->kind) {
						case ast::ExpressionKind::StringLiteral:
							fmt_arg.type = Yosys::VerilogFmtArg::STRING;
							fmt_arg.str = std::string{arg->as<ast::StringLiteral>().getValue()};
							fmt_arg.sig = {}; // TODO
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
								/* fallthrough */
							}
						default:
							fmt_arg.type = Yosys::VerilogFmtArg::INTEGER;
							fmt_arg.sig = evaluate_rhs(mod, *arg, &rvalue_subs);
							fmt_arg.signed_ = arg->type->isSigned();
							break;
						}
						fmt_args.push_back(fmt_arg);						
						
					}
					Yosys::Fmt fmt = {};
					fmt.parse_verilog(fmt_args, /* sformat_like */ false, /* default_base */ 10,
									  std::string{call.getSubroutineName()}, mod->name);
					fmt.append_string("\n");
					fmt.emit_rtlil(cell);
				} else {
					unimplemented(expr);
				}
			}
			return;
		case ast::ExpressionKind::Assignment:
			/* handled further below */
			break;
		default:
			unimplemented(expr);
		}

		require(expr, expr.expr.kind == ast::ExpressionKind::Assignment);
		const auto &assign = expr.expr.as<ast::AssignmentExpression>();
		bool blocking = !assign.isNonBlocking();

		RTLIL::SigSpec lvalue;
		RTLIL::SigSpec rvalue;

		if (assign.left().kind == ast::ExpressionKind::ElementSelect \
				&& !assign.left().as<ast::ElementSelectExpression>().selector().constant) {
			auto &elemsel = assign.left().as<ast::ElementSelectExpression>();
			RTLIL::SigSpec selvalue = evaluate_rhs(mod, elemsel.selector(), &rvalue_subs);
			require(expr, elemsel.value().type->getArrayElementType()); // TODO: extend
			int stride = elemsel.value().type->getArrayElementType()->getBitWidth();

			lvalue = evaluate_lhs(mod, elemsel.value());
			log_assert(lvalue.size() % stride == 0);
			// TODO: check out-of-range handling
			RTLIL::SigSpec mask = mod->Demux(NEW_ID, RTLIL::SigSpec(RTLIL::State::S1, stride), selvalue);
			RTLIL::SigSpec lvalue_rhs = evaluate_rhs(mod, elemsel.value(), &rvalue_subs);
			RTLIL::SigSpec rvalue_repeat;
			rvalue = evaluate_rhs(mod, assign.right(), &rvalue_subs);
			while (rvalue_repeat.size() < lvalue.size())
				rvalue_repeat.append(rvalue);
			mask.extend_u0(lvalue.size());
			rvalue = mod->Bwmux(NEW_ID, lvalue_rhs, rvalue_repeat, mask);
		} else {
			lvalue = evaluate_lhs(mod, assign.left());
			rvalue = evaluate_rhs(mod, assign.right(), &rvalue_subs);
		}
		log_assert(lvalue.size() == rvalue.size());

		if (blocking) {
			for (int i = 0; i < lvalue.size(); i++)
				rvalue_subs[lvalue[i]] = rvalue[i];
			// TODO: proper message on blocking/nonblocking mixing
			log_assert(!assigned_nonblocking.check_any(lvalue));
			assigned_blocking.add(lvalue);
		} else {
			 // TODO: proper message on blocking/nonblocking mixing
			log_assert(!assigned_blocking.check_any(lvalue));
			assigned_nonblocking.add(lvalue);
		}

		current_case->actions.push_back(RTLIL::SigSig(
			staging_signal(lvalue),
			rvalue
		));
	}

	void handle(const ast::BlockStatement &blk) {
		require(blk, blk.blockKind == ast::StatementBlockKind::Sequential)
		blk.body.visit(*this);
	}

	void handle(const ast::StatementList &list) {
		for (auto &stmt : list.list)
			stmt->visit(*this);
	}

	void handle(const ast::ConditionalStatement &cond)
	{
		require(cond, cond.conditions.size() == 1);
		require(cond, cond.conditions[0].pattern == NULL);

		RTLIL::CaseRule *case_save = current_case;
		RTLIL::SigSpec condition = mod->ReduceBool(NEW_ID,
			evaluate_rhs(mod, *cond.conditions[0].expr, &rvalue_subs)
		);
		SwitchBuilder b(current_case, &rvalue_subs, condition);
		transfer_attrs(cond, b.sw);

		b.branch({RTLIL::S1}, [&](RTLIL::CaseRule *rule){
			current_case = rule;
			transfer_attrs(cond.ifTrue, rule);
			cond.ifTrue.visit(*this);
		});

		if (cond.ifFalse) {
			b.branch({}, [&](RTLIL::CaseRule *rule){
				current_case = rule;
				transfer_attrs(*cond.ifFalse, rule);
				cond.ifFalse->visit(*this);
			});	
		}
		b.finish(mod);

		current_case = case_save;
		// descend into an empty switch so we force action priority for follow up statements
		RTLIL::SwitchRule *dummy_switch = new RTLIL::SwitchRule;
		current_case->switches.push_back(dummy_switch);
		current_case = new RTLIL::CaseRule;
		dummy_switch->cases.push_back(current_case);
	}

	void handle(const ast::CaseStatement &stmt)
	{
		require(stmt, stmt.condition == ast::CaseStatementCondition::Normal);
		require(stmt, stmt.check == ast::UniquePriorityCheck::None);

		RTLIL::CaseRule *case_save = current_case;
		RTLIL::SigSpec dispatch = evaluate_rhs(mod, stmt.expr, &rvalue_subs);
		SwitchBuilder b(current_case, &rvalue_subs, dispatch);
		transfer_attrs(stmt, b.sw);

		for (auto item : stmt.items) {
			std::vector<RTLIL::SigSpec> compares;
			for (auto expr : item.expressions) {
				log_assert(expr);
				RTLIL::SigSpec compare = evaluate_rhs(mod, *expr, &rvalue_subs);
				log_assert(compare.size() == dispatch.size());
				compares.push_back(compare);
			}
			require(stmt, !compares.empty());
			b.branch(compares, [&](RTLIL::CaseRule *rule) {
				current_case = rule;
				transfer_attrs(*item.stmt, rule);
				item.stmt->visit(*this);
			});
		}

		if (stmt.defaultCase) {
			b.branch(std::vector<RTLIL::SigSpec>{}, [&](RTLIL::CaseRule *rule) {
				current_case = rule;
				transfer_attrs(*stmt.defaultCase, rule);
				stmt.defaultCase->visit(*this);
			});
		}

		b.finish(mod);

		current_case = case_save;
		// descend into an empty switch so we force action priority for follow up statements
		RTLIL::SwitchRule *dummy_switch = new RTLIL::SwitchRule;
		current_case->switches.push_back(dummy_switch);
		current_case = new RTLIL::CaseRule;
		dummy_switch->cases.push_back(current_case);
	}

	void handle(YS_MAYBE_UNUSED const ast::InvalidStatement &stmt) { log_abort(); }
	void handle(YS_MAYBE_UNUSED const ast::EmptyStatement &stmt) {}

	void handle(const ast::Statement &stmt)
	{
		unimplemented(stmt);
	}
};

struct WireAddingVisitor : public ast::ASTVisitor<WireAddingVisitor, true, false> {
public:
	RTLIL::Module *mod;

	WireAddingVisitor(RTLIL::Module *mod)
		: mod(mod) {}

	// Do not descend into other modules
	void handle(YS_MAYBE_UNUSED const ast::InstanceSymbol &sym) { }

	void handle(const ast::ValueSymbol &sym)
	{
		auto w = mod->addWire(net_id(sym), sym.getType().getBitstreamWidth());
		transfer_attrs2(sym, w);
	}
};

struct InitialProceduralVisitor : public ast::ASTVisitor<InitialProceduralVisitor, true, false> {
public:
	RTLIL::Module *mod;
	InitialProceduralVisitor(RTLIL::Module *mod)
		: mod(mod) {}

	void handle(const ast::Symbol &sym)
	{
		unimplemented(sym);
	}
};

struct ModulePopulatingVisitor : public ast::ASTVisitor<ModulePopulatingVisitor, true, false> {
public:
	RTLIL::Module *mod;
	ModulePopulatingVisitor(RTLIL::Module *mod)
		: mod(mod) {}

	bool populate_sync(RTLIL::Process *proc, const ast::TimingControl &timing)
	{
		switch (timing.kind) {
		case ast::TimingControlKind::SignalEvent:
			{
				const auto &sigevent = timing.as<ast::SignalEventControl>();
				RTLIL::SyncRule *sync = new RTLIL::SyncRule();
				proc->syncs.push_back(sync);
				RTLIL::SigSpec sig = evaluate_rhs(mod, sigevent.expr, NULL);
				require(sigevent, sig.size() == 1);
				require(sigevent, sigevent.iffCondition == NULL);
				sync->signal = sig;
				switch (sigevent.edge) {
				case ast::EdgeKind::None:
					return false;
				case ast::EdgeKind::PosEdge:
					sync->type = RTLIL::SyncType::STp;
					break;
				case ast::EdgeKind::NegEdge:
					sync->type = RTLIL::SyncType::STn;
					break;
				case ast::EdgeKind::BothEdges:
					sync->type = RTLIL::SyncType::STe;
					break;
				}
			}
			return true;
		case ast::TimingControlKind::ImplicitEvent:
			{
				RTLIL::SyncRule *sync = new RTLIL::SyncRule();
				proc->syncs.push_back(sync);
				sync->type = RTLIL::SyncType::STa;
			}
			return true;
		case ast::TimingControlKind::EventList:
			{
				const auto &evlist = timing.as<ast::EventListControl>();
				for (auto ev : evlist.events) {
					log_assert(ev);
					if (!populate_sync(proc, *ev))
						return false;
				}
			}
			return true;
		default:
			return false;
		}
	}

	void handle(const ast::ProceduralBlockSymbol &sym)
	{
		switch (sym.procedureKind) {
		case ast::ProceduralBlockKind::Always:
		case ast::ProceduralBlockKind::AlwaysFF:
			{
				RTLIL::Process *proc = mod->addProcess(NEW_ID);
				require(sym, sym.getBody().kind == ast::StatementKind::Timed);

				const auto &timed = sym.getBody().as<ast::TimedStatement>();
				if (!populate_sync(proc, timed.timing))
					unimplemented(timed)

				ProceduralVisitor visitor(mod, proc);
				timed.stmt.visit(visitor);
				visitor.staging_done();
			}
			break;

		case ast::ProceduralBlockKind::AlwaysComb:
			{
				RTLIL::Process *proc = mod->addProcess(NEW_ID);
				RTLIL::SyncRule *sync = new RTLIL::SyncRule;
				proc->syncs.push_back(sync);
				sync->type = RTLIL::SyncType::STa;

				ProceduralVisitor visitor(mod, proc);
				sym.getBody().visit(visitor);
				visitor.staging_done();
			}
			break;

		case ast::ProceduralBlockKind::Initial:
			{
				InitialProceduralVisitor visitor(mod);
				sym.getBody().visit(visitor);
			}
			break;
		default:
			unimplemented(sym);
		}		
	}

	void handle(YS_MAYBE_UNUSED const ast::ParameterSymbol &sym) {}

	void handle(const ast::NetSymbol &sym)
	{
		if (sym.getInitializer())
			mod->connect(mod->wire(net_id(sym)), evaluate_rhs(mod, *sym.getInitializer(), NULL));
	}

	void handle(const ast::VariableSymbol &sym)
	{
		RTLIL::Wire *w = mod->wire(net_id(sym));
		log_assert(w);
		RTLIL::Const initval;
		if (sym.getInitializer()) {
			auto init = sym.getInitializer();
			{ // TODO: get rid of
				ast::ASTContext ctx(global_compilation->getRoot(), ast::LookupLocation::max);
				ctx.tryEval(*init);
			}
			require(sym, init->constant);
			auto const_ = init->constant;
			require(sym, const_->isInteger());
			initval = svint_const(const_->integer());
		} else {
			require(sym, sym.getType().isIntegral());
			if (sym.getType().isFourState())
				initval = {RTLIL::S0, w->width};
			else
				initval = {RTLIL::Sx, w->width};
		}
		if (!initval.is_fully_undef())
			w->attributes[RTLIL::ID::init] = initval;
	}

	void handle(const ast::PortSymbol &sym)
	{
		RTLIL::Wire *wire = mod->wire(net_id(*sym.internalSymbol));
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

	void handle(const ast::InstanceSymbol &sym)
	{
		require(sym, sym.isModule());
		RTLIL::Cell *cell = mod->addCell(id(sym.name), id(sym.body.name));
		for (auto *conn : sym.getPortConnections()) {
			if (!conn->getExpression())
				continue;
			auto &expr = *conn->getExpression();
			RTLIL::SigSpec signal;
			if (expr.kind == ast::ExpressionKind::Assignment) {
				auto &assign = expr.as<ast::AssignmentExpression>();
				require(expr, assign.right().kind == ast::ExpressionKind::EmptyArgument);
				signal = evaluate_lhs(mod, assign.left());
			} else {
				signal = evaluate_rhs(mod, expr, NULL);
			}
			cell->setPort(net_id(conn->port), signal);
		}
		transfer_attrs2(sym, cell);
	}

	void handle(const ast::ContinuousAssignSymbol &sym)
	{
		const ast::AssignmentExpression &expr = sym.getAssignment().as<ast::AssignmentExpression>();
		mod->connect(evaluate_lhs(mod, expr.left()), evaluate_rhs(mod, expr.right(), NULL));		
	}

	void handle(const ast::SubroutineSymbol &sym)
	{
		require(sym, sym.members().empty());
	}

	void handle(const ast::GenerateBlockSymbol &sym)
	{
		if (sym.isUninstantiated)
			return;
		visitDefault(sym);
	}

	void handle(const ast::InstanceBodySymbol &sym)
	{
		visitDefault(sym);
	}

	void handle(const ast::TypeAliasType &type) {}

	void handle(const ast::Symbol &sym)
	{
		unimplemented(sym);
	}
};

struct RTLILGenVisitor : public ast::ASTVisitor<RTLILGenVisitor, true, false> {
public:
	ast::Compilation &compilation;
	RTLIL::Design *design;

	RTLILGenVisitor(ast::Compilation &compilation, RTLIL::Design *design)
		: compilation(compilation), design(design) {}

	void handle(const ast::InstanceSymbol &symbol)
	{
		std::string name{symbol.name};

		if (symbol.name.empty()) {
			// NetlistVisitor.h says we should ignore this
			return;
		}

		RTLIL::Module *mod = design->addModule(id(symbol.body.name));
		transfer_attrs2(symbol.body, mod);

		WireAddingVisitor wadder(mod);
		symbol.body.visit(wadder);

		ModulePopulatingVisitor modpop(mod);
		symbol.body.visit(modpop);

		mod->fixup_ports();
		mod->check();

		this->visitDefault(symbol);
	}
};

USING_YOSYS_NAMESPACE

struct SlangFrontend : Frontend {
	SlangFrontend() : Frontend("slang", "read SystemVerilog (slang)") {}

	void help() override
	{
		slang::driver::Driver driver;
		driver.addStandardArgs();
		std::optional<bool> dump_ast;
		driver.cmdLine.add("--dump-ast", dump_ast, "Dump the AST");
		log("%s\n", driver.cmdLine.getHelpText("Slang-based SystemVerilog frontend").c_str());
	}

	void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		(void) f;
		(void) filename;
		log_header(design, "Executing SLANG frontend.\n");

		slang::driver::Driver driver;
		driver.addStandardArgs();
		std::optional<bool> dump_ast;
		driver.cmdLine.add("--dump-ast", dump_ast, "Dump the AST");
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

		try {
			if (!driver.parseAllSources())
				log_error("Parsing failed\n");

			auto compilation = driver.createCompilation();

			if (!driver.reportCompilation(*compilation, /* quiet */ false))
				log_error("Compilation failed\n");

			if (dump_ast.has_value() && dump_ast.value()) {
				slang::JsonWriter writer;
				writer.setPrettyPrint(true);
				ast::ASTSerializer serializer(*compilation, writer);
				serializer.serialize(compilation->getRoot());
				std::cout << writer.view() << std::endl;
			}

			global_compilation = &(*compilation);
			global_sourcemgr = compilation->getSourceManager();
			RTLILGenVisitor visitor(*compilation, design);
			compilation->getRoot().visit(visitor);
		} catch (const std::exception& e) {
			log_error("Exception: %s\n", e.what());
		}
	}
} SlangFrontend;

PRIVATE_NAMESPACE_END
