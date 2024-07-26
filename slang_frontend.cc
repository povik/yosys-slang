//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/ast/ASTVisitor.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/diagnostics/DiagnosticEngine.h"
#include "slang/diagnostics/TextDiagnosticClient.h"
#include "slang/driver/Driver.h"
#include "slang/syntax/SyntaxPrinter.h"
#include "slang/syntax/SyntaxTree.h"
#include "slang/syntax/AllSyntax.h"
#include "slang/text/Json.h"
#include "slang/util/Util.h"

#include "kernel/bitpattern.h"
#include "kernel/fmt.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"

#include "initial_eval.h"
#include "slang_frontend.h"

inline namespace slang_frontend {

struct SynthesisSettings {
	std::optional<bool> dump_ast;
	std::optional<bool> no_proc;
	std::optional<bool> translate_on_off_compat;

	void addOptions(slang::CommandLine &cmdLine) {
		cmdLine.add("--dump-ast", dump_ast, "Dump the AST");
		cmdLine.add("--no-proc", no_proc, "Disable lowering of processes");
		cmdLine.add("--translate-on-off-compat", translate_on_off_compat,
					"Interpret translate_on/translate_off comment pragmas for compatiblity with other tools");
	}
};

using Yosys::log;
using Yosys::log_error;
using Yosys::log_warning;
using Yosys::log_id;
using Yosys::log_signal;
using Yosys::ys_debug;
using Yosys::ceil_log2;

namespace RTLIL = Yosys::RTLIL;
namespace ID = Yosys::RTLIL::ID;
namespace ast = slang::ast;
namespace syntax = slang::syntax;
namespace parsing = slang::parsing;

ast::Compilation *global_compilation;
const slang::SourceManager *global_sourcemgr;
slang::DiagnosticEngine *global_diagengine;
slang::TextDiagnosticClient *global_diagclient;

slang::SourceRange source_location(const ast::Symbol &obj)			{ return slang::SourceRange(obj.location, obj.location); }
slang::SourceRange source_location(const ast::Expression &expr)		{ return expr.sourceRange; }
slang::SourceRange source_location(const ast::Statement &stmt)		{ return stmt.sourceRange; }
slang::SourceRange source_location(const ast::TimingControl &stmt)	{ return stmt.sourceRange; }

template<typename T>
std::string format_src(const T &obj)
{
	auto sm = global_sourcemgr;
	auto sr = source_location(obj);

	if (!sm->isFileLoc(sr.start()) || !sm->isFileLoc(sr.end()))
		return "";

	if (sr.start() == sr.end()) {
		auto loc = sr.start();
		std::string fn{sm->getFileName(loc)};
		return Yosys::stringf("%s:%d.%d", fn.c_str(),
			(int) sm->getLineNumber(loc), (int) sm->getColumnNumber(loc));
	} else {
		std::string fn{sm->getFileName(sr.start())};
		return Yosys::stringf("%s:%d.%d-%d.%d", fn.c_str(),
			(int) sm->getLineNumber(sr.start()), (int) sm->getColumnNumber(sr.start()),
			(int) sm->getLineNumber(sr.end()), (int) sm->getColumnNumber(sr.end()));
	}
}

template<typename T>
[[noreturn]] void unimplemented_(const T &obj, const char *file, int line, const char *condition)
{
	slang::JsonWriter writer;
	writer.setPrettyPrint(true);
	ast::ASTSerializer serializer(*global_compilation, writer);
	serializer.serialize(obj);
	std::cout << writer.view() << std::endl;
	auto loc = source_location(obj);
	log_assert(loc.start().buffer() == loc.end().buffer());
	std::string_view source_text = global_sourcemgr->getSourceText(loc.start().buffer());
	int col_no = global_sourcemgr->getColumnNumber(loc.start());
	const char *line_start = source_text.data() + loc.start().offset() - col_no + 1;
	const char *line_end = line_start;
	while (*line_end && *line_end != '\n' && *line_end != '\r') line_end++;
	std::cout << "Source line " << format_src(obj) << ": " << std::string_view(line_start, line_end) << std::endl;
	log_error("Feature unimplemented at %s:%d, see AST and code line dump above%s%s%s\n",
			  file, line, condition ? " (failed condition \"" : "", condition ? condition : "", condition ? "\")" : "");
}
#define require(obj, property) { if (!(property)) unimplemented_(obj, __FILE__, __LINE__, #property); }
#define unimplemented(obj) { unimplemented_(obj, __FILE__, __LINE__, NULL); }

};

#include "addressing.h"

inline namespace slang_frontend {

// step outside slang_frontend namespace for a minute, to patch in
// unimplemented() into the SlangInitial evaluator
};
ast::Statement::EvalResult SlangInitial::EvalVisitor::visit(const ast::Statement &stmt)
{
	unimplemented(stmt);
}
inline namespace slang_frontend {

const RTLIL::IdString id(const std::string_view &view)
{
	return RTLIL::escape_id(std::string(view));
}

static void build_hierpath(std::ostringstream &s, const ast::Scope *scope)
{
	if (!scope ||
		// stop at the containing instance
		scope->asSymbol().kind == ast::SymbolKind::InstanceBody)
		return;

	if (auto parent = scope->asSymbol().getHierarchicalParent())
		build_hierpath(s, parent);

	auto symbol = &scope->asSymbol();

	if (symbol->kind == ast::SymbolKind::GenerateBlockArray) {
		auto &array = symbol->as<ast::GenerateBlockArraySymbol>();
		s << array.getExternalName();
	} else if (symbol->kind == ast::SymbolKind::GenerateBlock) {
		auto &block = symbol->as<ast::GenerateBlockSymbol>();
		if (auto index = block.arrayIndex) {
			s << "[" << index->toString(slang::LiteralBase::Decimal, false) << "]."; 
		} else {
			s << block.getExternalName() << ".";
		}
	} else if (symbol->kind == ast::SymbolKind::Instance ||
			   symbol->kind == ast::SymbolKind::CheckerInstance) {
		auto &inst = symbol->as<ast::InstanceSymbolBase>();
		if (!inst.arrayPath.empty()) {
            for (size_t i = 0; i < inst.arrayPath.size(); i++)
            	s << "[" << inst.arrayPath[i] << "]";
		}
	} else if (!symbol->name.empty()) {
		s << symbol->name << ".";
	}
}

static const RTLIL::IdString scoped_id(const ast::Symbol &symbol)
{
	std::ostringstream path;
	build_hierpath(path, symbol.getParentScope());
	path << symbol.name;
	return RTLIL::escape_id(path.str());
}

static const RTLIL::IdString module_type_id(const ast::InstanceSymbol &sym)
{
	require(sym, sym.isModule());
	std::string instance;
	sym.body.getHierarchicalPath(instance);
	if (instance == sym.body.name)
		return RTLIL::escape_id(std::string(sym.body.name));
	else
		return RTLIL::escape_id(std::string(sym.body.name) + "$" + instance);
}

static const RTLIL::Const convert_svint(const slang::SVInt &svint)
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

static const RTLIL::Const convert_const(const slang::ConstantValue &constval)
{
	log_assert(!constval.isReal());
	log_assert(!constval.isShortReal());
	log_assert(!constval.isNullHandle());
	log_assert(!constval.isUnbounded());
	log_assert(!constval.isMap());
	log_assert(!constval.isQueue());
	log_assert(!constval.isUnion());

	if (constval.isInteger()) {
		return convert_svint(constval.integer());
	} else if (constval.isUnpacked()) {
		RTLIL::Const ret;
		// TODO: is this right?
		for (auto &el : constval.elements()) {
			auto piece = convert_const(el);
			ret.bits.insert(ret.bits.begin(), piece.bits.begin(), piece.bits.end());
		}
		log_assert(ret.size() == (int) constval.getBitstreamWidth());
		return ret;
	} else if (constval.isString()) {
		RTLIL::Const ret = convert_svint(constval.convertToInt().integer());
		ret.flags |= RTLIL::CONST_FLAG_STRING;
		return ret;
	}

	log_abort();
}

template<typename T>
void transfer_attrs(T &from, RTLIL::AttrObject *to)
{
	auto src = format_src(from);
	if (!src.empty())
		to->attributes[Yosys::ID::src] = src;

	for (auto attr : global_compilation->getAttributes(from)) {
		require(*attr, attr->getValue().isInteger());
		to->attributes[id(attr->name)] = convert_svint(attr->getValue().integer());
	}
}

static RTLIL::SigSpec evaluate_function(SignalEvalContext &eval, const ast::CallExpression &call);

void assert_nonstatic_free(RTLIL::SigSpec signal)
{
	for (auto bit : signal)
		log_assert(!(bit.wire && bit.wire->get_bool_attribute(ID($nonstatic))));
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

void crop_zero_mask(const RTLIL::SigSpec &mask, RTLIL::SigSpec &target)
{
	for (int i = mask.size() - 1; i >= 0; i--) {
		if (mask[i] == RTLIL::S0)
			target.remove(i, 1);
	}
}

static bool detect_full_case(RTLIL::SwitchRule *switch_)
{
	Yosys::BitPatternPool pool(switch_->signal);

	for (auto case_ : switch_->cases) {
		if (case_->compare.empty()) {
			// we have reached a default, by now we know this case is full
			pool.take_all();
			break; 
		} else {
			for (auto compare : case_->compare)
			if (compare.is_fully_const())
				pool.take(compare);
		}
	}

	return pool.empty();
}

static Yosys::pool<RTLIL::SigBit> detect_possibly_unassigned_subset(Yosys::pool<RTLIL::SigBit> &signals, RTLIL::CaseRule *rule)
{
	Yosys::pool<RTLIL::SigBit> remaining = signals;

	for (auto &action : rule->actions)
	for (auto bit : action.first)
		remaining.erase(bit);

	for (auto switch_ : rule->switches) {
		if (remaining.empty())
			break;

		if (switch_->get_bool_attribute(ID::full_case) || detect_full_case(switch_)) {
			Yosys::pool<RTLIL::SigBit> new_remaining;
			for (auto case_ : switch_->cases)
			for (auto bit : detect_possibly_unassigned_subset(remaining, case_))
				new_remaining.insert(bit);
			remaining.swap(new_remaining);
		}
	}

	return remaining;
}

static void insert_assign_enables(Yosys::dict<RTLIL::SigBit, RTLIL::SigBit> map, RTLIL::CaseRule *rule)
{
	RTLIL::SigSpec to_enable;

	for (auto &action : rule->actions)
	for (auto bit : action.first)
	if (map.count(bit))
		to_enable.append(map.at(bit));

	to_enable.sort_and_unify();
	if (!to_enable.empty())
		rule->actions.push_back({to_enable, RTLIL::SigSpec(RTLIL::S1, to_enable.size())});

	for (auto switch_ : rule->switches)
	for (auto case_ : switch_->cases)
		insert_assign_enables(map, case_);
}

struct UpdateTiming {
	RTLIL::SigBit background_enable;

	struct Sensitivity {
		RTLIL::SigBit signal;
		bool edge_polarity;
		const ast::TimingControl *ast_node;
	};
	std::vector<Sensitivity> triggers;

	bool implicit() const
	{
		return triggers.empty();
	}

	// extract trigger for side-effect cells like $print, $check
	void extract_trigger(NetlistContext &netlist, Yosys::Cell *cell, RTLIL::SigBit enable)
	{
		auto &params = cell->parameters;

		cell->setPort(ID::EN, netlist.LogicAnd(background_enable, enable));

		if (implicit()) {
			params[ID::TRG_ENABLE] = false;
			params[ID::TRG_WIDTH] = 0;
			params[ID::TRG_POLARITY] = {};
			cell->setPort(ID::TRG, {});
		} else {
			params[ID::TRG_ENABLE] = true;
			params[ID::TRG_WIDTH] = triggers.size();
			RTLIL::Const pol;
			RTLIL::SigSpec trg_signals;
			for (auto trigger : triggers) {
				pol.bits.push_back(trigger.edge_polarity ? RTLIL::S1 : RTLIL::S0);
				trg_signals.append(trigger.signal);
			}
			params[ID::TRG_POLARITY] = pol;
			cell->setPort(ID::TRG, trg_signals);
		}
	}
};

struct ProceduralVisitor : public ast::ASTVisitor<ProceduralVisitor, true, false> {
public:
	NetlistContext &netlist;
	SignalEvalContext eval;
	UpdateTiming &timing;	

	Yosys::SigPool assigned_blocking;
	Yosys::SigPool assigned_nonblocking;

	RTLIL::CaseRule *root_case;
	RTLIL::CaseRule *current_case;

	enum Mode { ALWAYS, FUNCTION } mode;

	// set if mode==FUNCTION
	const ast::SubroutineSymbol *subroutine;

	int effects_priority = 0;

	ProceduralVisitor(NetlistContext &netlist, UpdateTiming &timing, Mode mode)
			: netlist(netlist), eval(netlist), timing(timing), mode(mode) {
		eval.const_.pushEmptyFrame();
		
		root_case = new RTLIL::CaseRule;
		auto top_switch = new RTLIL::SwitchRule;
		root_case->switches.push_back(top_switch);
		current_case = new RTLIL::CaseRule;
		top_switch->cases.push_back(current_case);
	}

	~ProceduralVisitor()
	{
		delete root_case;
	}

	Yosys::dict<RTLIL::SigBit, RTLIL::SigBit> staging;

	void copy_case_tree_into(RTLIL::CaseRule &rule)
	{
		rule.actions.insert(rule.actions.end(),
							root_case->actions.begin(), root_case->actions.end());
		root_case->actions.clear();
		rule.switches.insert(rule.switches.end(),
							 root_case->switches.begin(), root_case->switches.end());
		root_case->switches.clear();
	}

	RTLIL::SigSpec all_driven()
	{
		RTLIL::SigSpec all_driven;
		for (auto pair : staging)
			all_driven.append(pair.first);
		all_driven.sort_and_unify();

		for (auto chunk : all_driven.chunks()) {
			log_assert(chunk.wire && !chunk.wire->get_bool_attribute(ID($nonstatic)));
		}

		return all_driven;		
	}

	void stage(RTLIL::SigSpec lvalue, RTLIL::SigSpec rvalue)
	{
		log_assert(lvalue.size() == rvalue.size());
		RTLIL::SigSpec to_create, lfiltered, rfiltered;

		for (int i = 0; i < lvalue.size(); i++) {
			RTLIL::SigBit lbit = lvalue[i];
			log_assert(lbit.wire);

			if (lbit.wire->get_bool_attribute(ID($nonstatic)))
				continue;

			if (!staging.count(lbit))
				to_create.append(lbit);

			lfiltered.append(lbit);
			rfiltered.append(rvalue[i]);
		}

		to_create.sort_and_unify();
		for (auto chunk : to_create.chunks()) {
			RTLIL::SigSpec w = netlist.canvas->addWire(NEW_ID_SUFFIX("staging"), chunk.size());
			for (int i = 0; i < chunk.size(); i++)
				staging[RTLIL::SigSpec(chunk)[i]] = w[i];
		}

		lfiltered.replace(staging);
		current_case->actions.push_back(RTLIL::SigSig(
			lfiltered,
			rfiltered
		));
	}

	// Return an enable signal for the current case node
	RTLIL::SigBit case_enable()
	{
		RTLIL::SigBit ret = netlist.canvas->addWire(NEW_ID, 1);
		root_case->actions.emplace_back(ret, RTLIL::State::S0);
		current_case->actions.emplace_back(ret, RTLIL::State::S1);
		return ret;
	}

	// For $check, $print cells
	void set_effects_trigger(RTLIL::Cell *cell)
	{
		timing.extract_trigger(netlist, cell, case_enable());
	}

	void do_simple_assign(RTLIL::SigSpec lvalue, RTLIL::SigSpec rvalue, bool blocking)
	{
		log_assert(lvalue.size() == rvalue.size());
		if (blocking) {
			eval.set(lvalue, rvalue);
			// TODO: proper message on blocking/nonblocking mixing
			log_assert(!assigned_nonblocking.check_any(lvalue));
			assigned_blocking.add(lvalue);
		} else {
			 // TODO: proper message on blocking/nonblocking mixing
			log_assert(!assigned_blocking.check_any(lvalue));
			assigned_nonblocking.add(lvalue);
		}

		stage(lvalue, rvalue);
	}

	void assign_rvalue(const ast::AssignmentExpression &assign, RTLIL::SigSpec rvalue)
	{
		bool blocking = !assign.isNonBlocking();
		const ast::Expression *raw_lexpr = &assign.left();
		RTLIL::SigSpec raw_mask = RTLIL::SigSpec(RTLIL::S1, rvalue.size()), raw_rvalue = rvalue;

		bool finished_etching = false;
		while (!finished_etching) {
			switch (raw_lexpr->kind) {
			case ast::ExpressionKind::RangeSelect:
				{
					auto &sel = raw_lexpr->as<ast::RangeSelectExpression>();
					Addressing addr(eval, sel);
					int stride = sel.value().type->getBitstreamWidth() / addr.range.width();
					int wider_size = sel.value().type->getBitstreamWidth();
					if (stride == 1) {
						raw_mask = addr.shift_up(raw_mask, false, wider_size);
						raw_rvalue = addr.shift_up(raw_rvalue, true, wider_size);
					} else {
						raw_mask = addr.embed(raw_mask, wider_size, stride, RTLIL::S0);
						raw_rvalue = addr.embed(raw_rvalue, wider_size, stride, RTLIL::Sx);
					}
					raw_lexpr = &sel.value();
				}
				break;
			case ast::ExpressionKind::ElementSelect:
				{
					auto &sel = raw_lexpr->as<ast::ElementSelectExpression>();
					Addressing addr(eval, sel);
					raw_mask = addr.demux(raw_mask, sel.value().type->getBitstreamWidth());
					raw_rvalue = raw_rvalue.repeat(addr.range.width());
					raw_lexpr = &sel.value();
				}
				break;
			case ast::ExpressionKind::MemberAccess:
				{
					const auto &acc = raw_lexpr->as<ast::MemberAccessExpression>();
					require(assign, acc.member.kind == ast::SymbolKind::Field);
					const auto &member = acc.member.as<ast::FieldSymbol>();
					require(acc, member.randMode == ast::RandMode::None);
					int pad = acc.value().type->getBitstreamWidth() - acc.type->getBitstreamWidth() - member.bitOffset;
					raw_mask = {RTLIL::SigSpec(RTLIL::S0, pad), raw_mask, RTLIL::SigSpec(RTLIL::S0, member.bitOffset)};
					raw_rvalue = {RTLIL::SigSpec(RTLIL::Sx, pad), raw_rvalue, RTLIL::SigSpec(RTLIL::Sx, member.bitOffset)};
					raw_lexpr = &acc.value();
				}
				break;
			default:
				finished_etching = true;
				break;
			}
			if (raw_mask.size() != (int) raw_lexpr->type->getBitstreamWidth())
				unimplemented(assign);
			log_assert(raw_mask.size() == (int) raw_lexpr->type->getBitstreamWidth());
			log_assert(raw_rvalue.size() == (int) raw_lexpr->type->getBitstreamWidth());
		}

		RTLIL::SigSpec lvalue = eval.lhs(*raw_lexpr);
		crop_zero_mask(raw_mask, lvalue);
		crop_zero_mask(raw_mask, raw_rvalue);
		crop_zero_mask(raw_mask, raw_mask);

		RTLIL::SigSpec masked_rvalue;
		if (raw_mask.is_fully_ones()) {
			masked_rvalue = raw_rvalue;
		} else {
			RTLIL::SigSpec raw_lvalue_sampled = lvalue;
			raw_lvalue_sampled.replace(eval.rvalue_subs);
			masked_rvalue = netlist.Bwmux(raw_lvalue_sampled, raw_rvalue, raw_mask);
		}

		do_simple_assign(lvalue, masked_rvalue, blocking);
	}

	void handle(const ast::ImmediateAssertionStatement &stmt)
	{
		auto cell = netlist.canvas->addCell(NEW_ID, ID($check));
		set_effects_trigger(cell);
		cell->setParam(ID::FLAVOR, std::string("assert"));
		cell->setParam(ID::FORMAT, std::string(""));
		cell->setParam(ID::ARGS_WIDTH, 0);
		cell->setParam(ID::PRIORITY, --effects_priority);
		cell->setPort(ID::ARGS, {});
		cell->setPort(ID::A, netlist.ReduceBool(eval(stmt.cond)));
	}

	void handle(const ast::ExpressionStatement &expr)
	{
		switch (expr.expr.kind) {
		case ast::ExpressionKind::Call:
			{
				auto &call = expr.expr.as<ast::CallExpression>();
				if (call.getSubroutineName() == "$display") {
					auto cell = netlist.canvas->addCell(NEW_ID, ID($print));
					transfer_attrs(expr, cell);
					set_effects_trigger(cell);
					cell->parameters[ID::PRIORITY] = --effects_priority;
					std::vector<Yosys::VerilogFmtArg> fmt_args;
					for (auto arg : call.arguments()) {
						log_assert(arg);
						Yosys::VerilogFmtArg fmt_arg = {};
						// TODO: location info in fmt_arg
						switch (arg->kind) {
						case ast::ExpressionKind::StringLiteral:
							fmt_arg.type = Yosys::VerilogFmtArg::STRING;
							fmt_arg.str = std::string{arg->as<ast::StringLiteral>().getValue()};
							fmt_arg.sig = {};
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
								[[fallthrough]];
							}
						default:
							fmt_arg.type = Yosys::VerilogFmtArg::INTEGER;
							fmt_arg.sig = eval(*arg);
							fmt_arg.signed_ = arg->type->isSigned();
							break;
						}
						fmt_args.push_back(fmt_arg);						
						
					}
					Yosys::Fmt fmt = {};
					// TODO: insert the actual module name
					fmt.parse_verilog(fmt_args, /* sformat_like */ false, /* default_base */ 10,
									  std::string{call.getSubroutineName()}, netlist.canvas->name);
					fmt.append_literal("\n");
					fmt.emit_rtlil(cell);
				} else if (!call.isSystemCall()) {
					auto subroutine = std::get<0>(call.subroutine);
					require(expr, subroutine->subroutineKind == ast::SubroutineKind::Task);
					log_assert(call.arguments().size() == subroutine->getArguments().size());
					for (int i = 0; i < (int) subroutine->getArguments().size(); i++) {
						auto arg = subroutine->getArguments()[i];
						auto dir = arg->direction;
						log_assert(dir == ast::ArgumentDirection::In || dir == ast::ArgumentDirection::Out);
						if (dir == ast::ArgumentDirection::In) {
							RTLIL::Wire *w = netlist.canvas->wire(scoped_id(*arg));
							log_assert(w);
							eval.set(w, eval(*call.arguments()[i]));
						}
					}
					subroutine->visit(*this);
					for (int i = 0; i < (int) subroutine->getArguments().size(); i++) {
						auto arg = subroutine->getArguments()[i];
						if (arg->direction == ast::ArgumentDirection::Out) {
							require(expr, call.arguments()[i]->kind == ast::ExpressionKind::Assignment);
							auto &assign = call.arguments()[i]->as<ast::AssignmentExpression>();
							require(expr, assign.right().kind == ast::ExpressionKind::EmptyArgument);
							RTLIL::Wire *w = netlist.wire(*arg);
							log_assert(w);
							RTLIL::SigSpec rvalue = w;
							rvalue.replace(eval.rvalue_subs);
							assert_nonstatic_free(rvalue);
							assign_rvalue(assign, rvalue);
						}
					}
				} else {
					unimplemented(expr);
				}
			}
			return;
		case ast::ExpressionKind::Assignment:
			{
				const auto &assign = expr.expr.as<ast::AssignmentExpression>();
				eval.lvalue = eval(assign.left());
				assign_rvalue(assign, eval(assign.right()));
				eval.lvalue = {};
			}
			break;
		default:
			unimplemented(expr);
		}
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
		RTLIL::SigSpec condition = netlist.ReduceBool(
			eval(*cond.conditions[0].expr)
		);
		SwitchBuilder b(current_case, &eval.rvalue_subs, condition);
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
		b.finish(netlist.canvas);

		current_case = case_save;
		// descend into an empty switch so we force action priority for follow up statements
		RTLIL::SwitchRule *dummy_switch = new RTLIL::SwitchRule;
		current_case->switches.push_back(dummy_switch);
		current_case = new RTLIL::CaseRule;
		dummy_switch->cases.push_back(current_case);
	}

	void handle(const ast::CaseStatement &stmt)
	{
		require(stmt, stmt.condition == ast::CaseStatementCondition::Normal ||
					  stmt.condition == ast::CaseStatementCondition::WildcardJustZ);
		bool match_z = stmt.condition == ast::CaseStatementCondition::WildcardJustZ;
		RTLIL::CaseRule *case_save = current_case;
		RTLIL::SigSpec dispatch = eval(stmt.expr);
		SwitchBuilder b(current_case, &eval.rvalue_subs, dispatch);

		switch (stmt.check) {
		case ast::UniquePriorityCheck::Priority: 
			b.sw->attributes[Yosys::ID::full_case] = true;
			break;
		case ast::UniquePriorityCheck::Unique:
			b.sw->attributes[Yosys::ID::full_case] = true;
			b.sw->attributes[Yosys::ID::parallel_case] = true;
			break;
		case ast::UniquePriorityCheck::Unique0:
			b.sw->attributes[Yosys::ID::parallel_case] = true;
			break;
		case ast::UniquePriorityCheck::None:
			break;
		}
		transfer_attrs(stmt, b.sw);

		for (auto item : stmt.items) {
			std::vector<RTLIL::SigSpec> compares;
			for (auto expr : item.expressions) {
				log_assert(expr);
				RTLIL::SigSpec compare = eval(*expr);
				log_assert(compare.size() == dispatch.size());
				require(stmt, !match_z || compare.is_fully_const());
				if (match_z)
					compare.replace(RTLIL::Sz, RTLIL::Sa);
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

		b.finish(netlist.canvas);

		current_case = case_save;
		// descend into an empty switch so we force action priority for follow up statements
		RTLIL::SwitchRule *dummy_switch = new RTLIL::SwitchRule;
		current_case->switches.push_back(dummy_switch);
		current_case = new RTLIL::CaseRule;
		dummy_switch->cases.push_back(current_case);
	}

	void handle(const ast::ForLoopStatement &stmt) {
		require(stmt, !stmt.steps.empty() && stmt.stopExpr);

		// TODO: `stmt.loopVars` vs. `stmt.initializers`
		// What do these two do, *exactly*? Which one should we handle first?
		for (auto var : stmt.loopVars) {
			require(stmt, var->getInitializer());
			auto initval = var->getInitializer()->eval(eval.const_);
			require(stmt, !initval.bad());
			eval.const_.createLocal(var, initval);
		}

		for (auto init : stmt.initializers) {
			require(*init, init->kind == ast::ExpressionKind::Assignment);
			const auto &assign = init->as<ast::AssignmentExpression>();
			require(*init, assign.left().kind == ast::ExpressionKind::NamedValue);
			const auto &lhs = assign.left().as<ast::NamedValueExpression>();
			auto initval = assign.right().eval(eval.const_);
			require(*init, !initval.bad());
			eval.const_.createLocal(&lhs.symbol, initval);
		}

		while (true) {
			auto cv = stmt.stopExpr->eval(eval.const_);
			require(stmt, (bool) cv);
			if (!cv.isTrue())
				break;
			stmt.body.visit(*this);
			for (auto step : stmt.steps)
				require(stmt, (bool) step->eval(eval.const_));
		}
	}

	void handle(const ast::InvalidStatement&) { log_abort(); }
	void handle(const ast::EmptyStatement&) {}
	void handle(const ast::VariableDeclStatement &stmt) {
		if (stmt.symbol.lifetime != ast::VariableLifetime::Static) {
			RTLIL::Wire *target = netlist.wire(stmt.symbol);
			log_assert(target);
			RTLIL::SigSpec initval;

			if (stmt.symbol.getInitializer())
				initval = eval(*stmt.symbol.getInitializer());
			else
				initval = convert_const(stmt.symbol.getType().getDefaultValue());

			do_simple_assign(
				target,
				initval,
				true
			);
		}
	}

	void handle(const ast::Statement &stmt)
	{
		unimplemented(stmt);
	}

	void handle(const ast::ReturnStatement &stmt)
	{
		require(stmt, mode == FUNCTION);
		log_assert(subroutine);
		do_simple_assign(netlist.canvas->wire(scoped_id(*subroutine->returnValVar)),
						   eval(*stmt.expr), true);
	}
};

#if 0
static RTLIL::SigSpec evaluate_function(SignalEvalContext &eval, const ast::CallExpression &call)
{
	const auto &subr = *std::get<0>(call.subroutine);
	log_assert(subr.subroutineKind == ast::SubroutineKind::Function);
	RTLIL::Module *mod = eval.netlist.canvas;
	RTLIL::Process *proc = eval.netlist.canvas->addProcess(NEW_ID);
	ProceduralVisitor visitor(eval.netlist, proc, ProceduralVisitor::FUNCTION);
	visitor.subroutine = &subr;
	log_assert(call.arguments().size() == subr.getArguments().size());

	for (int i = 0; i < (int) call.arguments().size(); i++) {
		RTLIL::Wire *w = mod->wire(scoped_id(*subr.getArguments()[i]));
		log_assert(w);
		eval.set(w, eval(*call.arguments()[i]));
	}
	subr.getBody().visit(visitor);

	// This is either a hack or brilliant: it just so happens that the WireAddingVisitor
	// has created a placeholder wire we can use here. That wire doesn't make sense as a
	// netlist element though.
	require(subr, subr.returnValVar->getType().isFixedSize());
	RTLIL::SigSpec ret = mod->wire(scoped_id(*subr.returnValVar));
	ret.replace(visitor.staging);
	return ret;
}
#endif

RTLIL::SigSpec SignalEvalContext::lhs(const ast::Expression &expr)
{
	require(expr, expr.type->isFixedSize());
	RTLIL::SigSpec ret;

	switch (expr.kind) {
	case ast::ExpressionKind::NamedValue:
		{
			const ast::Symbol &sym = expr.as<ast::NamedValueExpression>().symbol;
			RTLIL::Wire *wire = netlist.wire(sym);
			log_assert(wire);
			ret = wire;
		}
		break;
	case ast::ExpressionKind::RangeSelect:
		{
			const ast::RangeSelectExpression &sel = expr.as<ast::RangeSelectExpression>();
			Addressing addr(netlist.eval, sel);
			RTLIL::SigSpec inner = lhs(sel.value());
			ret = addr.extract(inner, sel.type->getBitstreamWidth());
		}
		break;
	case ast::ExpressionKind::Concatenation:
		{
			const ast::ConcatenationExpression &concat = expr.as<ast::ConcatenationExpression>();
			for (auto op : concat.operands())
				ret = {ret, lhs(*op)};
		}
		break;
	case ast::ExpressionKind::ElementSelect:
		{
			const ast::ElementSelectExpression &elemsel = expr.as<ast::ElementSelectExpression>();
			require(expr, elemsel.selector().constant);
			require(expr, elemsel.value().type->isArray() && elemsel.value().type->hasFixedRange());
			int idx = elemsel.selector().constant->integer().as<int>().value();
			int stride = elemsel.type->getBitstreamWidth();
			uint32_t raw_idx = elemsel.value().type->getFixedRange().translateIndex(idx);
			ret = lhs(elemsel.value()).extract(stride * raw_idx, stride);
		}
		break;
	case ast::ExpressionKind::MemberAccess:
		{
			const auto &acc = expr.as<ast::MemberAccessExpression>();
			require(expr, acc.member.kind == ast::SymbolKind::Field);
			const auto &member = acc.member.as<ast::FieldSymbol>();
			require(acc, member.randMode == ast::RandMode::None);
			return lhs(acc.value()).extract(member.bitOffset,
											expr.type->getBitstreamWidth());
		}
		break;
	default:
		unimplemented(expr);
		break;
	}

	log_assert(expr.type->isFixedSize());
	log_assert(ret.size() == (int) expr.type->getBitstreamWidth());
	return ret;
}


RTLIL::SigSpec SignalEvalContext::operator()(ast::Expression const &expr)
{
	if (expr.type->isVoid())
		return {};

	require(expr, expr.type->isFixedSize());
	RTLIL::Module *mod = netlist.canvas;
	RTLIL::SigSpec ret;
	size_t repl_count;

	{
		auto const_result = expr.eval(this->const_);
		if (const_result) {
			ret = convert_const(const_result);
			goto done;
		}
	}

	switch (expr.kind) {
	case ast::ExpressionKind::Inside:
		{
			auto &inside_expr = expr.as<ast::InsideExpression>();
			RTLIL::SigSpec left = (*this)(inside_expr.left());
			RTLIL::SigSpec hits;

			for (auto elem : inside_expr.rangeList()) {
				require(*elem, elem->kind != ast::ExpressionKind::ValueRange);
				require(*elem, !elem->type->isUnpackedArray());
				RTLIL::SigSpec elem_signal = (*this)(*elem);
				require(*elem, elem_signal.size() == left.size());
				require(*elem, elem_signal.is_fully_const());
				require(*elem, elem->type->isIntegral() && inside_expr.left().type->isIntegral());
				hits.append(netlist.EqWildcard(left, elem_signal));
			}

			ret = netlist.ReduceBool(hits);
			ret.extend_u0(expr.type->getBitstreamWidth());
			break;
		}
	case ast::ExpressionKind::NamedValue:
		{
			const ast::Symbol &sym = expr.as<ast::NamedValueExpression>().symbol;

			switch (sym.kind) {
			case ast::SymbolKind::Net:
			case ast::SymbolKind::Variable:
			case ast::SymbolKind::FormalArgument:
				{
					RTLIL::Wire *wire = netlist.wire(sym);
					log_assert(wire);
					ret = wire;
					ret.replace(rvalue_subs);
					assert_nonstatic_free(ret);
				}
				break;
			case ast::SymbolKind::Parameter:
				{
					auto &valsym = sym.as<ast::ValueSymbol>();
					require(valsym, valsym.getInitializer());
					auto exprconst = valsym.getInitializer()->constant;
					require(valsym, exprconst && exprconst->isInteger());
					ret = convert_svint(exprconst->integer());
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
			RTLIL::SigSpec left = (*this)(unop.operand());
			bool invert = false;

			RTLIL::IdString type;
			switch (unop.op) {
			case ast::UnaryOperator::Minus: type = ID($neg); break;
			case ast::UnaryOperator::LogicalNot: type = ID($logic_not); break;
			case ast::UnaryOperator::BitwiseNot: type = ID($not); break;
			case ast::UnaryOperator::BitwiseOr: type = ID($reduce_or); break;
			case ast::UnaryOperator::BitwiseAnd: type = ID($reduce_and); break;
			case ast::UnaryOperator::BitwiseNand: type = ID($reduce_and); invert = true; break;
			case ast::UnaryOperator::BitwiseNor: type = ID($reduce_or); invert = true; break;
			case ast::UnaryOperator::BitwiseXor: type = ID($reduce_xor); break;
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
			RTLIL::SigSpec left = (*this)(biop.left());
			RTLIL::SigSpec right = (*this)(biop.right());

			bool a_signed = biop.left().type->isSigned();
			bool b_signed = biop.right().type->isSigned();

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
			case ast::BinaryOperator::CaseInequality: type = ID($nex); break;
			case ast::BinaryOperator::CaseEquality: type = ID($eqx); break;
			case ast::BinaryOperator::GreaterThanEqual:	type = ID($ge); break;
			case ast::BinaryOperator::GreaterThan:		type = ID($gt); break;
			case ast::BinaryOperator::LessThanEqual:	type = ID($le); break;
			case ast::BinaryOperator::LessThan:			type = ID($lt); break;
			//case ast::BinaryOperator::WildcardEquality;
			//case ast::BinaryOperator::WildcardInequality;
			case ast::BinaryOperator::LogicalAnd:	type = ID($logic_and); break;
			case ast::BinaryOperator::LogicalOr:	type = ID($logic_or); break;
			case ast::BinaryOperator::LogicalImplication: type = ID($logic_or); left = mod->LogicNot(NEW_ID, left); a_signed = false; break;
			case ast::BinaryOperator::LogicalEquivalence: type = ID($eq); left = mod->ReduceBool(NEW_ID, left); right = mod->ReduceBool(NEW_ID, right); a_signed = b_signed = false; break;
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
			cell->setParam(RTLIL::ID::A_SIGNED, a_signed);
			cell->setParam(RTLIL::ID::B_SIGNED, b_signed);
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
			ret = (*this)(conv.operand());
			ret.extend_u0((int) to.getBitWidth(), to.isSigned());
		}
		break;
	case ast::ExpressionKind::IntegerLiteral:
		{
			const ast::IntegerLiteral &lit = expr.as<ast::IntegerLiteral>();
			ret = convert_svint(lit.getValue());
		}
		break;
	case ast::ExpressionKind::RangeSelect:
		{
			const ast::RangeSelectExpression &sel = expr.as<ast::RangeSelectExpression>();
			Addressing addr(*this, sel);
			ret = addr.shift_down((*this)(sel.value()), sel.type->getBitstreamWidth());
		}
		break;
	case ast::ExpressionKind::ElementSelect:
		{
			const ast::ElementSelectExpression &elemsel = expr.as<ast::ElementSelectExpression>();
			Addressing addr(*this, elemsel);
			ret = addr.mux((*this)(elemsel.value()), elemsel.type->getBitstreamWidth());
		}
		break;
	case ast::ExpressionKind::Concatenation:
		{
			const ast::ConcatenationExpression &concat = expr.as<ast::ConcatenationExpression>();
			for (auto op : concat.operands())
				ret = {ret, (*this)(*op)};
		}
		break;
	case ast::ExpressionKind::SimpleAssignmentPattern:
	case ast::ExpressionKind::StructuredAssignmentPattern:
		{
			repl_count = 1;

			if (0) {
	case ast::ExpressionKind::ReplicatedAssignmentPattern:
				repl_count = *expr.as<ast::ReplicatedAssignmentPatternExpression>()
                            	.count().eval(const_).integer().as<size_t>();
			}

			auto &pattern_expr = static_cast<const ast::AssignmentPatternExpressionBase&>(expr);
			require(expr, expr.type->isIntegral());

			ret = {};
			for (auto elem : pattern_expr.elements())
				ret.append((*this)(*elem));
			ret = ret.repeat(repl_count);				
		}
		break;
	case ast::ExpressionKind::ConditionalOp:
		{
			const auto &ternary = expr.as<ast::ConditionalExpression>();

			require(expr, ternary.conditions.size() == 1);
			require(expr, !ternary.conditions[0].pattern);

			ret = mod->Mux(NEW_ID,
				(*this)(ternary.right()),
				(*this)(ternary.left()),
				mod->ReduceBool(NEW_ID, (*this)(*(ternary.conditions[0].expr)))
			);
		}
		break;
	case ast::ExpressionKind::Replication:
		{
			const auto &repl = expr.as<ast::ReplicationExpression>();
			require(expr, repl.count().constant); // TODO: message
			int reps = repl.count().constant->integer().as<int>().value(); // TODO: checking
			RTLIL::SigSpec concat = (*this)(repl.concat());
			for (int i = 0; i < reps; i++)
				ret.append(concat);
		}
		break;
	case ast::ExpressionKind::MemberAccess:
		{
			const auto &acc = expr.as<ast::MemberAccessExpression>();
			require(expr, acc.member.kind == ast::SymbolKind::Field);
			const auto &member = acc.member.as<ast::FieldSymbol>();
			require(acc, member.randMode == ast::RandMode::None);
			return (*this)(acc.value()).extract(member.bitOffset,
								expr.type->getBitstreamWidth());
		}
		break;
	case ast::ExpressionKind::Call:
		{
			const auto &call = expr.as<ast::CallExpression>();
			if (call.isSystemCall()) {
				require(expr, call.getSubroutineName() == "$signed" || call.getSubroutineName() == "$unsigned");
				require(expr, call.arguments().size() == 1);
				ret = (*this)(*call.arguments()[0]);
			} else {
				const auto &subr = *std::get<0>(call.subroutine);
				require(subr, subr.subroutineKind == ast::SubroutineKind::Function);
				log_abort();
				//return evaluate_function(*this, call);
			}
		}
		break;
	case ast::ExpressionKind::LValueReference:
		ret = lvalue;
		break;
	default:
		unimplemented(expr);
	}

done:
	log_assert(expr.type->isFixedSize());
	log_assert(ret.size() == (int) expr.type->getBitstreamWidth());
	return ret;
}

RTLIL::SigSpec SignalEvalContext::eval_signed(ast::Expression const &expr)
{
	require(expr, expr.type);

	if (expr.type->isNumeric() && !expr.type->isSigned())
		return {RTLIL::S0, (*this)(expr)};
	else
		return (*this)(expr);
}

SignalEvalContext::SignalEvalContext(NetlistContext &netlist)
	: netlist(netlist), const_(ast::ASTContext(netlist.compilation.getRoot(),
											   ast::LookupLocation::max))
{
}

#include "diag.h"

struct PopulateNetlist : public ast::ASTVisitor<PopulateNetlist, true, false> {
public:
	NetlistContext &netlist;
	SynthesisSettings &settings;
	std::vector<const ast::InstanceSymbol *> deferred_modules;

	struct InitialEvalVisitor : SlangInitial::EvalVisitor {
		RTLIL::Module *mod;
		int print_priority;

		InitialEvalVisitor(ast::Compilation *compilation, RTLIL::Module *mod)
			: SlangInitial::EvalVisitor(compilation), mod(mod), print_priority(0) {}

		void handleDisplay(const slang::ast::CallExpression &call, const std::vector<slang::ConstantValue> &args) {
			auto cell = mod->addCell(NEW_ID, ID($print));
			cell->parameters[Yosys::ID::TRG_ENABLE] = true;
			cell->parameters[Yosys::ID::TRG_WIDTH] = 0;
			cell->parameters[Yosys::ID::TRG_POLARITY] = {};
			cell->parameters[Yosys::ID::PRIORITY] = print_priority--;
			cell->setPort(Yosys::ID::EN, RTLIL::S1);
			cell->setPort(Yosys::ID::TRG, {});
			std::vector<Yosys::VerilogFmtArg> fmt_args;
			for (int i = 0; i < (int) call.arguments().size(); i++) {
				const ast::Expression *arg_expr = call.arguments()[i];
				const auto &arg = args[i];
				Yosys::VerilogFmtArg fmt_arg = {};
				// TODO: location info in fmt_arg
				if (arg_expr->kind == ast::ExpressionKind::StringLiteral) {
					fmt_arg.type = Yosys::VerilogFmtArg::STRING;
					fmt_arg.str = std::string{arg_expr->as<ast::StringLiteral>().getValue()};
					fmt_arg.sig = RTLIL::Const(fmt_arg.str);
				} else if (arg.isString()) {
					fmt_arg.type = Yosys::VerilogFmtArg::STRING;
					fmt_arg.str = arg.str();
					fmt_arg.sig = RTLIL::Const(fmt_arg.str);
				} else if (arg.isInteger()) {
					fmt_arg.type = Yosys::VerilogFmtArg::INTEGER;
					fmt_arg.sig = convert_svint(arg.integer());
					fmt_arg.signed_ = arg.integer().isSigned();
				} else {
					unimplemented(*arg_expr);
				}
				fmt_args.push_back(fmt_arg);	
			}
			Yosys::Fmt fmt = {};
			// TODO: default_base is subroutine dependent, final newline is $display-only
			fmt.parse_verilog(fmt_args, /* sformat_like */ false, /* default_base */ 10,
							  std::string{call.getSubroutineName()}, mod->name);
			fmt.append_literal("\n");
			fmt.emit_rtlil(cell);
			transfer_attrs(call, cell);
		}
	} initial_eval;

	PopulateNetlist(NetlistContext &netlist, SynthesisSettings &settings)
		: netlist(netlist), settings(settings), initial_eval(&netlist.compilation, netlist.canvas) {}

	void synthesize_procedure_with_implicit_timing(const ast::ProceduralBlockSymbol &symbol, const ast::Statement &body)
	{
		const ast::Scope *scope = symbol.getParentScope();

		RTLIL::Process *proc = netlist.canvas->addProcess(NEW_ID);
		transfer_attrs(body, proc);

		UpdateTiming implicit_timing;
		ProceduralVisitor visitor(netlist, implicit_timing, ProceduralVisitor::ALWAYS);
		body.visit(visitor);
		visitor.copy_case_tree_into(proc->root_case);

		Yosys::pool<RTLIL::SigBit> all_staging_signals;
		for (auto pair : visitor.staging)
			all_staging_signals.insert(pair.second);

		Yosys::pool<RTLIL::SigBit> dangling =
				detect_possibly_unassigned_subset(all_staging_signals, &proc->root_case);

		// left-hand side and right-hand side of the connections to be made
		RTLIL::SigSpec cl, cr;

		// map from a driven signal to the corresponding latch enable
		Yosys::dict<RTLIL::SigBit, RTLIL::SigBit> latch_enables;
		RTLIL::SigSpec latch_driven;

		for (auto driven_bit : visitor.all_driven()) {
			RTLIL::SigBit staged_bit = visitor.staging.at(driven_bit);

			if (!dangling.count(staged_bit)) {
				// No latch inferred
				cl.append(driven_bit);
				cr.append(staged_bit);
			} else {
				// TODO: create latches in groups
				RTLIL::SigBit en = netlist.canvas->addWire(NEW_ID, 1);
				RTLIL::Cell *cell = netlist.canvas->addDlatchGate(NEW_ID, en,
														staged_bit, driven_bit, true);
				transfer_attrs(symbol, cell);
				latch_enables[staged_bit] = en;
				latch_driven.append(driven_bit);
				proc->root_case.actions.push_back({en, RTLIL::S0});
			}
		}

		if (symbol.procedureKind == ast::ProceduralBlockKind::AlwaysLatch && !cl.empty()) {
			for (auto chunk : cl.chunks()) {
				auto &diag = scope->addDiag(diag::LatchNotInferred, symbol.location);
				diag << std::string(log_signal(chunk));
			}
		}

		if (symbol.procedureKind == ast::ProceduralBlockKind::AlwaysComb && !latch_driven.empty()) {
			for (auto chunk : latch_driven.chunks()) {
				auto &diag = scope->addDiag(diag::LatchInferred, symbol.location);
				diag << std::string(log_signal(chunk));
			}
		}

		insert_assign_enables(latch_enables, &proc->root_case);
		netlist.GroupConnect(cl, cr);
	}

	void synthesize_procedure_with_edge_timing(const ast::ProceduralBlockSymbol &symbol, UpdateTiming &timing)
	{
		log_assert(symbol.getBody().kind == ast::StatementKind::Timed);
		const auto &timed = symbol.getBody().as<ast::TimedStatement>();
		const ast::Statement *stmt = &timed.stmt;
		const ast::Scope *scope = symbol.getParentScope();

		RTLIL::Process *proc = netlist.canvas->addProcess(NEW_ID);
		transfer_attrs(timed.stmt, proc);

		struct Aload {
			RTLIL::SigBit trigger;
			bool trigger_polarity;
			Yosys::dict<RTLIL::SigBit, RTLIL::SigBit> values;
			const ast::Statement *ast_node;
		};
		std::vector<Aload> aloads;
		RTLIL::SigSpec previous_async;

		// Keep inferring asynchronous loads until we get to a single remaining edge trigger
		while (timing.triggers.size() > 1) {
			while (stmt->kind == ast::StatementKind::Block
					&& stmt->as<ast::BlockStatement>().blockKind == ast::StatementBlockKind::Sequential)
				stmt = &stmt->as<ast::BlockStatement>().body;

			if (stmt->kind != ast::StatementKind::Conditional
					|| stmt->as<ast::ConditionalStatement>().check != ast::UniquePriorityCheck::None
					|| stmt->as<ast::ConditionalStatement>().conditions.size() != 1
					|| stmt->as<ast::ConditionalStatement>().conditions[0].pattern
					|| !stmt->as<ast::ConditionalStatement>().ifFalse) {
				auto &diag = symbol.getParentScope()->addDiag(diag::ExpectingIfElseAload, stmt->sourceRange);
				diag.addNote(diag::NoteDuplicateEdgeSense, timed.timing.sourceRange);
				break;
			}

			auto &cond_stmt = stmt->as<ast::ConditionalStatement>();
			const ast::Expression *condition = cond_stmt.conditions[0].expr;

			bool polarity = true;
			if (condition->kind == ast::ExpressionKind::UnaryOp
					&& (condition->as<ast::UnaryExpression>().op == ast::UnaryOperator::LogicalNot
						|| condition->as<ast::UnaryExpression>().op == ast::UnaryOperator::BitwiseNot)) {
				polarity = false;
				condition = &condition->as<ast::UnaryExpression>().operand();
			}

			if (condition->kind == ast::ExpressionKind::NamedValue) {
				RTLIL::SigSpec cond_signal = netlist.eval(*condition);

				auto found = std::find_if(timing.triggers.begin(), timing.triggers.end(),
									   [=](const UpdateTiming::Sensitivity &sense) {
					return RTLIL::SigSpec(sense.signal) == cond_signal;
				});

				if (found != timing.triggers.end()) {
					if (found->edge_polarity != polarity) {
						auto &diag = symbol.getParentScope()->addDiag(diag::IfElseAloadPolarity, cond_stmt.conditions[0].expr->sourceRange);
						diag.addNote(diag::NoteSignalEvent, found->ast_node->sourceRange);
						diag.addNote(diag::NoteDuplicateEdgeSense, timed.timing.sourceRange);
						// We raised an error. Do infer the async load anyway
					}

					UpdateTiming branch_timing;
					// copy in the single trigger for this branch
					branch_timing.triggers = {*found};
					// disable the effects if some of the priority async signals are raised
					branch_timing.background_enable = netlist.LogicNot(previous_async);

					ProceduralVisitor visitor(netlist, branch_timing, ProceduralVisitor::ALWAYS);
					cond_stmt.ifTrue.visit(visitor);

					visitor.copy_case_tree_into(proc->root_case);
					aloads.push_back({
						found->signal,
						found->edge_polarity,
						visitor.staging,
						&cond_stmt.ifTrue
					});

					// TODO: check for non-constant load values and warn about sim/synth mismatch

					// Prepare the stage for the inference of the next async load,
					// or for the final synchronous part.
					previous_async.append(polarity ? found->signal : RTLIL::SigBit(netlist.Not(found->signal)));
					timing.triggers.erase(found);
					stmt = cond_stmt.ifFalse;
					continue;
				}
			}

			auto &diag = scope->addDiag(diag::IfElseAloadMismatch, stmt->sourceRange);
			diag.addNote(diag::NoteDuplicateEdgeSense, timed.timing.sourceRange);
			break;
		}

		require(symbol, aloads.size() <= 1);
		{
			timing.background_enable = netlist.LogicNot(previous_async);
			ProceduralVisitor visitor(netlist, timing, ProceduralVisitor::ALWAYS);
			stmt->visit(visitor);
			visitor.copy_case_tree_into(proc->root_case);

			RTLIL::SigSpec driven = visitor.all_driven();
			for (auto driven_chunk : driven.chunks()) {
				RTLIL::SigSpec staging_chunk = driven_chunk;
				staging_chunk.replace(visitor.staging);

				proc->root_case.actions.push_back({staging_chunk, driven_chunk});

				RTLIL::Cell *cell;

				if (aloads.empty()) {
					cell = netlist.canvas->addDff(NEW_ID,
											timing.triggers[0].signal, staging_chunk, driven_chunk,
											timing.triggers[0].edge_polarity);
				} else if (aloads.size() == 1) {
					RTLIL::SigSpec aload_chunk = driven_chunk;
					aload_chunk.replace(aloads[0].values);

					for (int i = 0; i < aload_chunk.size(); i++) {
						if (aload_chunk[i] == RTLIL::SigSpec(driven_chunk)[i]) {
							auto &diag = scope->addDiag(diag::MissingAload, aloads[0].ast_node->sourceRange);
							diag << std::string(log_signal(RTLIL::SigSpec(driven_chunk)[i]));
							diag.addNote(diag::NoteProcessDriver, symbol.location);
							diag.addNote(diag::NoteDuplicateEdgeSense, timed.timing.sourceRange);
							aload_chunk[i] = RTLIL::Sx;
						}
					}

					cell = netlist.canvas->addAldff(NEW_ID,
											timing.triggers[0].signal, aloads[0].trigger,
											staging_chunk, driven_chunk, aload_chunk,
											timing.triggers[0].edge_polarity, aloads[0].trigger_polarity);
				} else {
					log_abort();
				}
				transfer_attrs(symbol, cell);
			}
		}
	}

	void handle(const ast::ProceduralBlockSymbol &symbol)
	{
		auto kind = symbol.procedureKind;
		switch (kind) {
		case ast::ProceduralBlockKind::Always:
		case ast::ProceduralBlockKind::AlwaysFF:
			handle_always(symbol);
			break;

		case ast::ProceduralBlockKind::AlwaysComb:
		case ast::ProceduralBlockKind::AlwaysLatch:
			synthesize_procedure_with_implicit_timing(symbol, symbol.getBody());
			break;

		case ast::ProceduralBlockKind::Initial:
			{
				auto result = symbol.getBody().visit(initial_eval);
				if (result != ast::Statement::EvalResult::Success) {
					for (auto& diag : initial_eval.context.getAllDiagnostics())
        				global_diagengine->issue(diag);
        			auto str = global_diagclient->getString();
					log_error("Failed to execute initial block\n%s\n",
							  str.c_str());
				}
			}
			break;
		case ast::ProceduralBlockKind::Final:
			{
				/* no-op */
			}
			break;
		default:
			unimplemented(symbol);
		}	
	}

	void handle_always(const ast::ProceduralBlockSymbol &symbol)
	{
		const ast::Scope *scope = symbol.getParentScope();
		log_assert(symbol.procedureKind == ast::ProceduralBlockKind::Always
				|| symbol.procedureKind == ast::ProceduralBlockKind::AlwaysFF);

		if (symbol.getBody().kind == ast::StatementKind::Invalid)
			return;

		require(symbol, symbol.getBody().kind == ast::StatementKind::Timed);
		const auto &timed = symbol.getBody().as<ast::TimedStatement>();
		const auto *top_ast_timing = &timed.timing;

		using TCKind = ast::TimingControlKind;
		std::span<const ast::TimingControl* const> events;
		const ast::TimingControl* const top_events[1] = {top_ast_timing};

		events = (top_ast_timing->kind == TCKind::EventList) ?
				top_ast_timing->as<ast::EventListControl>().events
				: std::span<const ast::TimingControl* const>(top_events);

		bool implicit = false;
		UpdateTiming timing;

		for (auto ev : events)
		switch (ev->kind) {
		case ast::TimingControlKind::SignalEvent:
			{
				const auto &sigev = ev->as<ast::SignalEventControl>();

				if (sigev.iffCondition)
					scope->addDiag(diag::IffUnsupported, sigev.iffCondition->sourceRange);

				switch (sigev.edge) {
				case ast::EdgeKind::None:
					{
						if (symbol.procedureKind == ast::ProceduralBlockKind::AlwaysFF) {
							scope->addDiag(diag::AlwaysFFBadTiming, ev->sourceRange);
							break;
						}

						// Report on the top timing node as that makes for nicer reports in case there
						// are many signals in the sensitivity list
						auto &diag = symbol.getParentScope()->addDiag(diag::SignalSensitivityAmbiguous, top_ast_timing->sourceRange);
						diag.addNote(diag::NoteSignalEvent, sigev.sourceRange);
						implicit = true;
					}
					break;

				case ast::EdgeKind::PosEdge:
				case ast::EdgeKind::NegEdge:
					{
						RTLIL::SigSpec sig = netlist.eval(sigev.expr);
						require(symbol, !sig.empty());

						// The LSB is the trigger; slang raises the 'multibit-edge' warning
						// to point this out to users
						timing.triggers.push_back(UpdateTiming::Sensitivity{
							sig.lsb(),
							(sigev.edge == ast::EdgeKind::PosEdge),
							&sigev
						});
					}
					break;

				case ast::EdgeKind::BothEdges:
					scope->addDiag(diag::BothEdgesUnsupported, sigev.sourceRange);
					break;
				}
			}
			break;

		case ast::TimingControlKind::ImplicitEvent:
			{
				if (symbol.procedureKind == ast::ProceduralBlockKind::AlwaysFF) {
					scope->addDiag(diag::AlwaysFFBadTiming, ev->sourceRange);
					break;
				}

				implicit = true;
			}
			break;

		case ast::TimingControlKind::EventList:
			log_abort();

		default:
			scope->addDiag(diag::GenericTimingUnsyn, ev->sourceRange);
			break;
		}

		if (implicit && !timing.triggers.empty())
			scope->addDiag(diag::EdgeImplicitMixing, top_ast_timing->sourceRange);

		if (implicit)
			synthesize_procedure_with_implicit_timing(symbol, timed.stmt);
		else if (!timing.triggers.empty())
			synthesize_procedure_with_edge_timing(symbol, timing);
	}

	void handle(const ast::NetSymbol &sym)
	{
		if (sym.getInitializer())
			netlist.canvas->connect(netlist.wire(sym), netlist.eval(*sym.getInitializer()));
	}

	void handle(const ast::PortSymbol &sym)
	{
		if (sym.getParentScope()->getContainingInstance() != &netlist.realm)
			return;

		RTLIL::Wire *wire = netlist.wire(*sym.internalSymbol);
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

	void handle(const ast::MultiPortSymbol &sym)
	{
		if (sym.getParentScope()->getContainingInstance() != &netlist.realm)
			return;

		unimplemented(sym);
	}

	void handle(const ast::InterfacePortSymbol &sym)
	{
		if (sym.getParentScope()->getContainingInstance() != &netlist.realm) {
			// If the port is on a module boundary which we are flattening within the
			// front end, then it doesn't need any special handling.
			return;
		}

		unimplemented(sym);
	}

	void inline_port_connection(const ast::PortSymbol &port, RTLIL::SigSpec signal)
	{
		require(port, !port.isNullPort);
		RTLIL::SigSpec internal_signal;

		if (auto expr = port.getInternalExpr()) 
			internal_signal = netlist.eval.lhs(*expr);
		else
			internal_signal = netlist.wire(*port.internalSymbol);

		log_assert(internal_signal.size() == signal.size());
		assert_nonstatic_free(internal_signal);

		require(port, port.direction == ast::ArgumentDirection::Out ||
					  port.direction == ast::ArgumentDirection::In);

		if (port.direction == ast::ArgumentDirection::Out)
			netlist.canvas->connect(signal, internal_signal);
		else
			netlist.canvas->connect(internal_signal, signal);
	}

	void handle(const ast::InstanceSymbol &sym)
	{
		if (/* should dissolve */ true) {
			sym.body.visit(*this);

			for (auto *conn : sym.getPortConnections()) {
				if (!conn->getExpression())
					continue;
				auto &expr = *conn->getExpression();

				RTLIL::SigSpec signal;
				if (expr.kind == ast::ExpressionKind::Assignment) {
					auto &assign = expr.as<ast::AssignmentExpression>();
					require(expr, assign.right().kind == ast::ExpressionKind::EmptyArgument ||
								(assign.right().kind == ast::ExpressionKind::Conversion &&
								 assign.right().as<ast::ConversionExpression>().operand().kind == ast::ExpressionKind::EmptyArgument));
					signal = netlist.eval.lhs(assign.left());
					assert_nonstatic_free(signal);
				} else {
					signal = netlist.eval(expr);
				}

				if (conn->port.kind == ast::SymbolKind::MultiPort) {
					int offset = 0;
					auto &multiport = conn->port.as<ast::MultiPortSymbol>();
					for (auto component : multiport.ports) {
						int width = component->getType().getBitstreamWidth();
						inline_port_connection(*component, signal.extract(offset, width));
						offset += width;
					}
					log_assert(offset == (int) multiport.getType().getBitstreamWidth());
				} else if (conn->port.kind == ast::SymbolKind::Port) {
					inline_port_connection(conn->port.as<ast::PortSymbol>(), signal);
				} else {
					log_abort();
				}
			}
		} else {
			require(sym, sym.isModule());
			RTLIL::Cell *cell = netlist.canvas->addCell(netlist.id(sym), module_type_id(sym));
			for (auto *conn : sym.getPortConnections()) {
				if (!conn->getExpression())
					continue;
				auto &expr = *conn->getExpression();
				RTLIL::SigSpec signal;
				if (expr.kind == ast::ExpressionKind::Assignment) {
					auto &assign = expr.as<ast::AssignmentExpression>();
					require(expr, assign.right().kind == ast::ExpressionKind::EmptyArgument);
					signal = netlist.eval.lhs(assign.left());
					assert_nonstatic_free(signal);
				} else {
					signal = netlist.eval(expr);
				}
				cell->setPort(id(conn->port.name), signal);
			}
			transfer_attrs(sym, cell);

			deferred_modules.push_back(&sym);
		}
	}

	void handle(const ast::ContinuousAssignSymbol &sym)
	{
		const ast::AssignmentExpression &expr = sym.getAssignment().as<ast::AssignmentExpression>();
		RTLIL::SigSpec lhs = netlist.eval.lhs(expr.left());
		assert_nonstatic_free(lhs);
		netlist.canvas->connect(lhs, netlist.eval(expr.right()));		
	}

	void handle(const ast::GenerateBlockSymbol &sym)
	{
		if (sym.isUninstantiated)
			return;
		visitDefault(sym);
	}

	void handle(const ast::GenerateBlockArraySymbol &sym)
	{
		visitDefault(sym);
	}

	void collect_flattened_trivia(std::vector<parsing::Trivia> &collect, parsing::Token token)
	{
		for (auto trivia : token.trivia()) {
			if (trivia.syntax())
				collect_flattened_trivia(collect, trivia.syntax()->getFirstToken());
			else
				collect.push_back(trivia);
		}
	}

	std::set<const syntax::SyntaxNode *> find_compat_pragma_masked_syntax(
			const ast::Symbol &symbol, const syntax::SyntaxListBase &list, syntax::ConstTokenOrSyntax final)
	{
		bool translating = true;
		std::set<const syntax::SyntaxNode *> disabled_set;

		for (size_t i = 0; i < list.getChildCount() + 1; i++) {
			parsing::Token token;
			const syntax::SyntaxNode *syntax;
			if (i < list.getChildCount()) {
				syntax = list.getChild(i).node();
				token = syntax->getFirstToken();
			} else {
				syntax = nullptr;
				token = final.isToken() ? final.token() : final.node()->getFirstToken();
			}

			std::vector<parsing::Trivia> flattened_trivia;
			collect_flattened_trivia(flattened_trivia, token);

			for (auto trivia : flattened_trivia) {
				if (trivia.kind == parsing::TriviaKind::LineComment) {
					std::string_view text = trivia.getRawText();
					log_assert(text.size() >= 2 && text[0] == '/' && text[1] == '/');
					text.remove_prefix(2);

					const char* whitespace = " \t";

					// trim start
					size_t p = text.find_first_not_of(whitespace);
					if (p == std::string_view::npos)
						continue;
					text.remove_prefix(p);

					std::string vendor_text = "synopsys";
					if (!text.starts_with(vendor_text))
						continue;
					text.remove_prefix(vendor_text.size());

					p = text.find_first_not_of(" \t");
					if (p == 0 || p == std::string_view::npos)
						continue;
					text.remove_prefix(p);

					// trim back
					p = text.find_last_not_of(" \t");
					if (p != std::string_view::npos)
						text.remove_suffix(text.size() - p - 1);

					if (text == "translate_off") {
						require(symbol, translating && "duplicate translate_off");
						translating = false;
					} else if (text == "translate_on") {
						require(symbol, !translating && "duplicate translate_on");
						translating = true;
					} else {
						std::string str{text};
						log_warning("Unknown vendor command: %s\n", str.c_str());
					}
				}
			}

			if (!translating && syntax)
				disabled_set.insert(syntax);
		}

		require(symbol, translating && "translating disabled at end of scope");
		return disabled_set;
	}

	void handle(const ast::InstanceBodySymbol &sym)
	{
		RTLIL::Module *mod = netlist.canvas;

		auto wadd = ast::makeVisitor([&](auto&, const ast::ValueSymbol &sym) {
			if (sym.getType().isFixedSize()) {
				if (sym.kind == ast::SymbolKind::Variable
						|| sym.kind == ast::SymbolKind::Net) {
					std::string kind{ast::toString(sym.kind)};
					auto w = mod->addWire(netlist.id(sym), sym.getType().getBitstreamWidth());
					transfer_attrs(sym, w);
					log_debug("Adding %s (%s)\n", log_id(netlist.id(sym)), kind.c_str());

					if (sym.kind == ast::SymbolKind::Variable
							&& sym.as<ast::VariableSymbol>().lifetime == ast::VariableLifetime::Automatic)
						w->attributes[ID($nonstatic)] = true;
				}
			}
		}, [&](auto&, const ast::InstanceSymbol&) {
			/* do not descend into other modules */
		}, [&](auto& visitor, const ast::GenerateBlockSymbol& sym) {
			/* stop at uninstantiated generate blocks */
			if (sym.isUninstantiated)
				return;
			visitor.visitDefault(sym);
		});
		sym.visit(wadd);

		auto varinit = ast::makeVisitor([&](auto&, const ast::VariableSymbol &sym) {
			slang::ConstantValue initval = nullptr;
			if (sym.getInitializer())
				initval = sym.getInitializer()->eval(initial_eval.context);
			initial_eval.context.createLocal(&sym, initval);
		}, [&](auto&, const ast::InstanceSymbol&) {
			/* do not descend into other modules */
		}, [&](auto&, const ast::ProceduralBlockSymbol&) {
			/* do not descend into procedural blocks */
		}, [&](auto& visitor, const ast::GenerateBlockSymbol& sym) {
			/* stop at uninstantiated generate blocks */
			if (sym.isUninstantiated)
				return;
			visitor.visitDefault(sym);
		});
		sym.visit(varinit);

		if (!settings.translate_on_off_compat.value_or(false)) {
			visitDefault(sym);
		} else {
			auto &syntax = sym.getSyntax()->as<syntax::ModuleDeclarationSyntax>();
			auto compad_disabled = find_compat_pragma_masked_syntax(
												sym, syntax.members, syntax.endmodule);

			for (auto& member : sym.members()) {
				if (compad_disabled.count(member.getSyntax()))
					continue;
				member.visit(*this);
			}
		}

		// now transfer the initializers from variables onto RTLIL wires
		auto inittransfer = ast::makeVisitor([&](auto&, const ast::VariableSymbol &sym) {
			if (sym.getType().isFixedSize() && sym.lifetime == ast::VariableLifetime::Static) {
				auto storage = initial_eval.context.findLocal(&sym);
				log_assert(storage);
				auto const_ = convert_const(*storage);
				if (!const_.is_fully_undef()) {
					auto wire = netlist.wire(sym);
					log_assert(wire);
					wire->attributes[RTLIL::ID::init] = const_;
				}
			}
		}, [&](auto&, const ast::InstanceSymbol&) {
			/* do not descend into other modules */
		}, [&](auto&, const ast::ProceduralBlockSymbol&) {
			/* do not descend into procedural blocks */
		}, [&](auto& visitor, const ast::GenerateBlockSymbol& sym) {
			/* stop at uninstantiated generate blocks */
			if (sym.isUninstantiated)
				return;
			visitor.visitDefault(sym);
		});
		sym.visit(inittransfer);

		for (auto& diag : initial_eval.context.getAllDiagnostics())
        	global_diagengine->issue(diag);
		auto str = global_diagclient->getString();
		if (global_diagengine->getNumErrors())
			log_error("%s", str.c_str());
		else
			log("%s", str.c_str());
		global_diagclient->clear();
	}

	void handle(const ast::UninstantiatedDefSymbol &sym)
	{
		require(sym, !sym.isChecker());
		require(sym, sym.paramExpressions.empty());

		RTLIL::Cell *cell = netlist.canvas->addCell(netlist.id(sym),
												id(sym.definitionName));

		auto port_names = sym.getPortNames();
		auto port_conns = sym.getPortConnections();

		log_assert(port_names.size() == port_conns.size());
		for (int i = 0; i < (int) port_names.size(); i++) {
			require(sym, !port_names[i].empty());
			auto &expr = port_conns[i]->as<ast::SimpleAssertionExpr>().expr;
			cell->setPort(RTLIL::escape_id(std::string{port_names[i]}), netlist.eval(expr));
		}
	}

	void handle(const ast::Type&) {}
	void handle(const ast::NetType&) {}
	void handle(const ast::ForwardingTypedefSymbol&) {}
	void handle(const ast::TransparentMemberSymbol&) {}
	void handle(const ast::SubroutineSymbol&) {}
	void handle(const ast::ParameterSymbol&) {}
	void handle(const ast::TypeParameterSymbol&) {}
	void handle(const ast::WildcardImportSymbol&) {}
	void handle(const ast::GenvarSymbol&) {}
	void handle(const ast::VariableSymbol&) {}
	void handle(const ast::EmptyMemberSymbol&) {}

	void handle(const ast::StatementBlockSymbol &sym)
	{
		visitDefault(sym);
	}

	void handle(const ast::InstanceArraySymbol &sym)
	{
		visitDefault(sym);
	}

	void handle(const ast::Symbol &sym)
	{
		unimplemented(sym);
	}
};

static void build_hierpath2(const ast::InstanceBodySymbol &realm,
							std::ostringstream &s, const ast::Scope *scope)
{
	if (!scope ||
		static_cast<const ast::Scope *>(&realm) == scope)
		return;

	const ast::Symbol *symbol = &scope->asSymbol();

	if (symbol->kind == ast::SymbolKind::InstanceBody)
		symbol = symbol->as<ast::InstanceBodySymbol>().parentInstance;
	if (symbol->kind == ast::SymbolKind::CheckerInstanceBody)
		symbol = symbol->as<ast::CheckerInstanceBodySymbol>().parentInstance;

	if (auto parent = symbol->getParentScope())
		build_hierpath2(realm, s, parent);

	if (symbol->kind == ast::SymbolKind::GenerateBlockArray) {
		auto &array = symbol->as<ast::GenerateBlockArraySymbol>();
		s << array.getExternalName();
	} else if (symbol->kind == ast::SymbolKind::GenerateBlock) {
		auto &block = symbol->as<ast::GenerateBlockSymbol>();
		if (auto index = block.arrayIndex) {
			s << "[" << index->toString(slang::LiteralBase::Decimal, false) << "]."; 
		} else {
			s << block.getExternalName() << ".";
		}
	} else if (symbol->kind == ast::SymbolKind::Instance ||
			   symbol->kind == ast::SymbolKind::CheckerInstance) {
		s << symbol->name;

		auto &inst = symbol->as<ast::InstanceSymbolBase>();
		if (!inst.arrayPath.empty()) {
            for (size_t i = 0; i < inst.arrayPath.size(); i++)
            	s << "[" << inst.arrayPath[i] << "]";
		}

		s << ".";
	} else if (!symbol->name.empty()) {
		s << symbol->name << ".";
	} else if (symbol->kind == ast::SymbolKind::StatementBlock) {
		s << "$" << (int) symbol->getIndex() << ".";
	}
}

RTLIL::IdString NetlistContext::id(const ast::Symbol &symbol)
{
	std::ostringstream path;
	build_hierpath2(realm, path, symbol.getParentScope());
	path << symbol.name;
	return RTLIL::escape_id(path.str());
}

RTLIL::Wire *NetlistContext::wire(const ast::Symbol &symbol)
{
	return canvas->wire(id(symbol));
}

NetlistContext::NetlistContext(
		RTLIL::Design *design,
		ast::Compilation &compilation,
		const ast::InstanceSymbol &instance)
	: compilation(compilation), realm(instance.body), eval(*this)
{
	canvas = design->addModule(module_type_id(instance));
	transfer_attrs(instance.body.getDefinition(), canvas);
}

NetlistContext::NetlistContext(
		NetlistContext &other,
		const ast::InstanceSymbol &instance)
	: NetlistContext(other.canvas->design, other.compilation, instance)
{
}

NetlistContext::~NetlistContext()
{
	canvas->fixup_ports();
	canvas->check();
}

USING_YOSYS_NAMESPACE

struct SlangFrontend : Frontend {
	SlangFrontend() : Frontend("slang", "read SystemVerilog (slang)") {}

	void help() override
	{
		slang::driver::Driver driver;
		driver.addStandardArgs();
		SynthesisSettings settings;
		settings.addOptions(driver.cmdLine);
		log("%s\n", driver.cmdLine.getHelpText("Slang-based SystemVerilog frontend").c_str());
	}

	void execute(std::istream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		(void) f;
		(void) filename;
		log_header(design, "Executing SLANG frontend.\n");

		slang::driver::Driver driver;
		driver.addStandardArgs();
		SynthesisSettings settings;
		settings.addOptions(driver.cmdLine);
		diag::setup_messages(driver.diagEngine);
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

			if (settings.dump_ast.value_or(false)) {
				slang::JsonWriter writer;
				writer.setPrettyPrint(true);
				ast::ASTSerializer serializer(*compilation, writer);
				serializer.serialize(compilation->getRoot());
				std::cout << writer.view() << std::endl;
			}

			global_compilation = &(*compilation);
			global_sourcemgr = compilation->getSourceManager();
			global_diagengine = &driver.diagEngine;
			global_diagclient = driver.diagClient.get();
			global_diagclient->clear();

			{
				for (auto instance : compilation->getRoot().topInstances) {
					NetlistContext netlist(design, *compilation, *instance);
					PopulateNetlist populate(netlist, settings);
					instance->body.visit(populate);
				}
			}

			if (!driver.reportCompilation(*compilation, /* quiet */ false))
				log_error("Compilation failed\n");
		} catch (const std::exception& e) {
			log_error("Exception: %s\n", e.what());
		}

		if (!settings.no_proc.value_or(false)) {
			log_push();
			call(design, "proc_clean");
			call(design, "proc_rmdead");
			call(design, "proc_prune");
			call(design, "proc_init");
			call(design, "proc_rom");
			call(design, "proc_mux");
			call(design, "proc_clean");
			call(design, "opt_expr -keepdc");
			log_pop();
		}
	}
} SlangFrontend;

};
