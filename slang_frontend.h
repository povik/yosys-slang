//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "slang/ast/Compilation.h"
#include "slang/ast/EvalContext.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "kernel/rtlil.h"

inline namespace slang_frontend {

namespace RTLIL = Yosys::RTLIL;
namespace ast = slang::ast;

struct NetlistContext;

struct SignalEvalContext {
	NetlistContext &netlist;

	ast::EvalContext const_;
	Yosys::dict<RTLIL::SigBit, RTLIL::SigBit> rvalue_subs;
	RTLIL::SigSpec lvalue;

	void set(RTLIL::SigSpec lhs, RTLIL::SigSpec value)
	{
		log_assert(lhs.size() == value.size());
		for (int i = 0; i < lhs.size(); i++)
			rvalue_subs[lhs[i]] = value[i];
	}

	RTLIL::SigSpec operator()(ast::Expression const &expr);
	RTLIL::SigSpec eval_signed(ast::Expression const &expr);

	std::pair<RTLIL::SigSpec, RTLIL::SigBit> translate_index(
		const ast::Expression &expr, slang::ConstantRange range);

	SignalEvalContext(NetlistContext &netlist);
};

struct RTLILBuilder {
	using SigSpec = RTLIL::SigSpec;

	RTLIL::Module *canvas;

	SigSpec ReduceBool(SigSpec a);

	SigSpec Sub(SigSpec a, SigSpec b, bool is_signed);
	SigSpec Demux(SigSpec a, SigSpec s);
	SigSpec Le(SigSpec a, SigSpec b, bool is_signed);
	SigSpec Ge(SigSpec a, SigSpec b, bool is_signed);
	SigSpec Lt(SigSpec a, SigSpec b, bool is_signed);
	SigSpec EqWildcard(RTLIL::SigSpec a, RTLIL::SigSpec b);
	SigSpec Eq(SigSpec a, SigSpec b);
	SigSpec LogicAnd(SigSpec a, SigSpec b);
	SigSpec LogicNot(SigSpec a);
	SigSpec Mux(SigSpec a, SigSpec b, SigSpec s);
	SigSpec Bwmux(SigSpec a, SigSpec b, SigSpec s);
	SigSpec Bmux(SigSpec a, SigSpec s);

	SigSpec Shift(SigSpec a, bool a_signed, SigSpec s, bool s_signed, int result_width);
	SigSpec Shiftx(SigSpec a, SigSpec s, bool s_signed, int result_width);
	SigSpec Neg(SigSpec a, bool signed_);
	SigSpec Not(SigSpec a);

	SigSpec Biop(RTLIL::IdString op, SigSpec a, SigSpec b,
				 bool a_signed, bool b_signed, int y_width);

	void GroupConnect(SigSpec lhs, SigSpec rhs)
	{
		int done = 0;
		for (auto chunk : lhs.chunks()) {
			canvas->connect(chunk, rhs.extract(done, chunk.size()));
			done += chunk.size();
		}
	}
};

struct NetlistContext : RTLILBuilder {
	ast::Compilation &compilation;
	const slang::SourceManager &source_mgr();

	// The instance body to which the netlist under construction corresponds.
	//
	// This instance body will be upstream of all the AST nodes we are processing
	// and it may or may not be the direct containing body.
	const ast::InstanceBodySymbol &realm;

	// The background evaluation context. For procedures we will be constructing
	// other specialized contexts.
	SignalEvalContext eval;

	// Returns an ID string to use in the netlist to represent the given symbol.
	RTLIL::IdString id(const ast::Symbol &sym);

	RTLIL::Wire *wire(const ast::Symbol &sym);

	NetlistContext(RTLIL::Design *design,
		ast::Compilation &compilation,
		const ast::InstanceSymbol &instance);

	NetlistContext(NetlistContext &other,
		const ast::InstanceSymbol &instance);

	~NetlistContext();
};

};
