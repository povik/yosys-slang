//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#pragma once
#include "slang/ast/EvalContext.h"
#include "kernel/rtlil.h"

// work around yosys PR #4524 changing the way you ask for pointer hashing
#if YS_HASHING_VERSION <= 0
#define YS_HASH_PTR_OPS ,Yosys::hashlib::hash_ptr_ops
#else
#define YS_HASH_PTR_OPS
#endif

template<> struct Yosys::hashlib::hash_ops<const slang::ast::Symbol*> : Yosys::hashlib::hash_ptr_ops {};

namespace slang {
	struct ConstantRange;
	class SourceManager;
	class DiagnosticEngine;
	namespace ast {
		class Compilation;
		class Symbol;
		class Expression;
		class SubroutineSymbol;
		class InstanceSymbol;
		class InstanceBodySymbol;
		class Statement;
		class SignalEventControl;
		class ProceduralBlockSymbol;
		class StreamingConcatenationExpression;
		class ConversionExpression;
		class AssignmentExpression;
	};
};

namespace slang_frontend {

using Yosys::log;
using Yosys::log_error;
using Yosys::log_warning;
using Yosys::log_id;
using Yosys::log_signal;
using Yosys::ys_debug;
using Yosys::ceil_log2;
namespace RTLIL = ::Yosys::RTLIL;
namespace ast = ::slang::ast;

struct NetlistContext;
struct ProceduralVisitor;

struct EvalContext {
	NetlistContext &netlist;
	ProceduralVisitor *procedural;

	ast::EvalContext const_;
	const ast::Expression *lvalue = nullptr;

	struct Frame {
		Yosys::dict<const ast::Symbol *, RTLIL::Wire *> locals;
		const ast::SubroutineSymbol *subroutine;
		RTLIL::Wire* disable = nullptr;
		RTLIL::Wire* break_ = nullptr; // for kind==LoopBody
		enum {
			Implicit,
			LoopBody,
			FunctionBody
		} kind;
	};

	std::vector<Frame> frames;

	Frame &push_frame(const ast::SubroutineSymbol *subroutine=nullptr);
	void create_local(const ast::Symbol *symbol);
	void pop_frame();
	RTLIL::Wire *wire(const ast::Symbol &symbol);

	RTLIL::SigSpec apply_conversion(const ast::ConversionExpression &conv, RTLIL::SigSpec op);
	RTLIL::SigSpec apply_nested_conversion(const ast::Expression &expr, RTLIL::SigSpec val);
	RTLIL::SigSpec streaming(ast::StreamingConcatenationExpression const &expr, bool in_lhs);

	// Evaluates the given symbols/expressions to their value in this context
	RTLIL::SigSpec operator()(ast::Expression const &expr);
	RTLIL::SigSpec operator()(ast::Symbol const &symbol);

	// Evaluates the given expression, inserts an extra sign bit if need
	// be so that the result can be interpreted as a signed value
	RTLIL::SigSpec eval_signed(ast::Expression const &expr);

	// Describes the given LHS expression as a sequence of wirebits
	//
	// This method is a helper used to evaluate both procedural and non-procedural
	// assignments. Not all expressions (not even all LHS-viable expressions)
	// are in simple correspondence to wirebits, and as such they cannot be
	// processed by this method and require special handling elsewhere.
	RTLIL::SigSpec lhs(ast::Expression const &expr);

	// Evaluate non-procedural connection LHS for connections expressed in
	// terms of an assignment of `EmptyArgument`. This is a pattern found in
	// the AST in module instance connections or for pattern assignments.
	RTLIL::SigSpec connection_lhs(ast::AssignmentExpression const &assign);

	EvalContext(NetlistContext &netlist);
	EvalContext(NetlistContext &netlist, ProceduralVisitor &procedural);

	// for testing
	bool ignore_ast_constants = false;
};

struct RTLILBuilder {
	using SigSpec = RTLIL::SigSpec;

	RTLIL::Module *canvas;

	unsigned next_id = 0;
	std::string new_id(std::string base = std::string());

	SigSpec ReduceBool(SigSpec a);

	SigSpec Sub(SigSpec a, SigSpec b, bool is_signed);
	SigSpec Demux(SigSpec a, SigSpec s);
	SigSpec Le(SigSpec a, SigSpec b, bool is_signed);
	SigSpec Ge(SigSpec a, SigSpec b, bool is_signed);
	SigSpec Lt(SigSpec a, SigSpec b, bool is_signed);
	SigSpec EqWildcard(RTLIL::SigSpec a, RTLIL::SigSpec b);
	SigSpec Eq(SigSpec a, SigSpec b);
	SigSpec LogicAnd(SigSpec a, SigSpec b);
	SigSpec LogicOr(SigSpec a, SigSpec b);
	SigSpec LogicNot(SigSpec a);
	SigSpec Mux(SigSpec a, SigSpec b, SigSpec s);
	SigSpec Bwmux(SigSpec a, SigSpec b, SigSpec s);
	SigSpec Bmux(SigSpec a, SigSpec s);

	SigSpec Shift(SigSpec a, bool a_signed, SigSpec s, bool s_signed, int result_width);
	SigSpec Shiftx(SigSpec a, SigSpec s, bool s_signed, int result_width);
	SigSpec Neg(SigSpec a, bool signed_);
	SigSpec Not(SigSpec a);

	SigSpec Unop(RTLIL::IdString op, SigSpec a, bool a_signed, int y_width);
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

class DiagnosticIssuer {
	using DiagCode = slang::DiagCode;
	using Diagnostic = slang::Diagnostic;
	using Diagnostics = slang::Diagnostics;
	using SourceRange = slang::SourceRange;
	using SourceLocation = slang::SourceLocation;
public:
	Diagnostic& add_diag(DiagCode code, SourceLocation location);
	Diagnostic& add_diag(DiagCode code, SourceRange sourceRange);
	void add_diag(Diagnostic diag);
	void add_diagnostics(const Diagnostics &diags);
	void report_into(slang::DiagnosticEngine &engine);
	std::vector<Diagnostic> issued_diagnostics;
};

struct SynthesisSettings;
struct NetlistContext : RTLILBuilder, public DiagnosticIssuer {
	SynthesisSettings &settings;
	ast::Compilation &compilation;
	const slang::SourceManager &source_mgr();

	// The instance body to which the netlist under construction corresponds.
	//
	// This instance body will be upstream of all the AST nodes we are processing
	// and it may or may not be the direct containing body.
	const ast::InstanceBodySymbol &realm;

	// The background evaluation context. For procedures we will be constructing
	// other specialized contexts.
	EvalContext eval;

	// Returns an ID string to use in the netlist to represent the given symbol.
	RTLIL::IdString id(const ast::Symbol &sym);

	RTLIL::Wire *add_wire(const ast::ValueSymbol &sym);
	RTLIL::Wire *wire(const ast::Symbol &sym);

	struct Memory {
		int num_wr_ports = 0;
	};
	Yosys::dict<RTLIL::IdString, Memory> emitted_mems;

	// Used to implement modports on uncollapsed levels of hierarchy
	Yosys::dict<const ast::Scope*, std::string YS_HASH_PTR_OPS> scopes_remap;

	Yosys::dict<RTLIL::Wire *, const ast::Type * YS_HASH_PTR_OPS> wire_hdl_types;

	// With this flag set we will not elaborate this netlist; we set this when
	// `scopes_remap` is incomplete due to errors in processing the instantiation
	// of `realm` somewhere in the input.
	bool disabled = false;

	NetlistContext(RTLIL::Design *design,
		SynthesisSettings &settings,
		ast::Compilation &compilation,
		const ast::InstanceSymbol &instance);

	NetlistContext(NetlistContext &other,
		const ast::InstanceSymbol &instance);

	~NetlistContext();

	NetlistContext(const NetlistContext&) = delete;
	NetlistContext& operator=(const NetlistContext&) = delete;
	NetlistContext(NetlistContext&& other)
		: settings(other.settings), compilation(other.compilation),
		  realm(other.realm), eval(*this)
	{
		log_assert(other.eval.procedural == nullptr);
		log_assert(other.eval.lvalue == nullptr);
		log_assert(other.eval.frames.empty());

		emitted_mems.swap(other.emitted_mems);
		scopes_remap.swap(other.scopes_remap);
		wire_hdl_types.swap(other.wire_hdl_types);
		detected_memories.swap(other.detected_memories);
		canvas = other.canvas;
		other.canvas = nullptr;
		disabled = other.disabled;
	}

	Yosys::pool<const ast::Symbol *> detected_memories;
	bool is_inferred_memory(const ast::Symbol &symbol);
	bool is_inferred_memory(const ast::Expression &expr);
};

// slang_frontend.cc
extern std::string hierpath_relative_to(const ast::Scope *relative_to, const ast::Scope *scope);
template<typename T> void transfer_attrs(T &from, RTLIL::AttrObject *to);

// blackboxes.cc
extern void import_blackboxes_from_rtlil(slang::SourceManager &mgr, ast::Compilation &target, RTLIL::Design *source);
extern bool is_decl_empty_module(const slang::syntax::SyntaxNode &syntax);
extern void export_blackbox_to_rtlil(ast::Compilation &comp, const ast::InstanceSymbol &inst, RTLIL::Design *target);

// abort_helpers.cc
[[noreturn]] void unimplemented_(const ast::Symbol &obj, const char *file, int line, const char *condition);
[[noreturn]] void unimplemented_(const ast::Expression &obj, const char *file, int line, const char *condition);
[[noreturn]] void unimplemented_(const ast::Statement &obj, const char *file, int line, const char *condition);
[[noreturn]] void unimplemented_(const ast::TimingControl &obj, const char *file, int line, const char *condition);
#define require(obj, property) { if (!(property)) unimplemented_(obj, __FILE__, __LINE__, #property); }
#define unimplemented(obj) { slang_frontend::unimplemented_(obj, __FILE__, __LINE__, NULL); }
#define ast_invariant(obj, property) require(obj, property)
#define ast_unreachable(obj) unimplemented(obj)

[[noreturn]] void wire_missing_(NetlistContext &netlist, const ast::Symbol &symbol, const char *file, int line);
#define wire_missing(netlist, symbol) { wire_missing_(netlist, symbol, __FILE__, __LINE__); }

// naming.cc
typedef std::pair<RTLIL::SigChunk, std::string> NamedChunk;
std::vector<NamedChunk> generate_subfield_names(RTLIL::SigChunk chunk, const ast::Type *type);

};
