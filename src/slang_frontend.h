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
template<> struct Yosys::hashlib::hash_ops<const slang::ast::Scope*> : Yosys::hashlib::hash_ptr_ops {};
template<> struct Yosys::hashlib::hash_ops<void*> : Yosys::hashlib::hash_ptr_ops {};

namespace slang {
	struct ConstantRange;
	class SourceManager;
	class DiagnosticEngine;
	class CommandLine;
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
using Yosys::log_flush;
using Yosys::log_error;
using Yosys::log_warning;
using Yosys::log_id;
using Yosys::log_signal;
using Yosys::ys_debug;
using Yosys::ceil_log2;
#ifndef log_debug
using Yosys::log_debug;
#endif
namespace RTLIL = ::Yosys::RTLIL;
namespace ast = ::slang::ast;
namespace ID = ::Yosys::RTLIL::ID;

struct NetlistContext;
class ProceduralContext;
class RegisterEscapeConstructGuard;
class EnterAutomaticScopeGuard;
class VariableBits;
class VariableBit;
class VariableChunk;
struct ProcessTiming;
class Case;

class Variable {
public:
	enum Kind {
		Static,
		Local,
		Disable,
		Break,
		Dummy,
		Invalid
	} kind;

	static Variable from_symbol(const ast::ValueSymbol *symbol, int depth=-1);
	static Variable disable_for_scope(const ast::Statement *statement, int depth);
	static Variable break_for_scope(const ast::Statement *statement, int depth);
	static Variable dummy(int width);

	Variable();
	const ast::ValueSymbol *get_symbol() const;
	const ast::Statement *get_statement() const;
	int bitwidth() const;
	explicit operator bool() const;

	bool operator==(const Variable &other) const { return sort_label() == other.sort_label(); }
	bool operator<(const Variable &other) const { return sort_label() < other.sort_label(); }

#if YS_HASHING_VERSION >= 1
	[[nodiscard]] Yosys::Hasher hash_into(Yosys::Hasher h) const { h.eat(sort_label()); return h; }
#else
	int hash() const { return Yosys::hash_ops<SortLabel>::hash(sort_label()); }
#endif
	std::string text() const;

private:
	union {
		const ast::ValueSymbol *symbol;
		const ast::Statement *statement;
		int width;
	};
	int depth = 0;

	Variable(enum Kind kind, const ast::ValueSymbol *symbol, int depth);
	Variable(enum Kind kind, const ast::Statement *statement, int depth);
	Variable(enum Kind kind, int width);

	typedef std::tuple<int, void *, int> SortLabel;
	SortLabel sort_label() const;
};

struct EvalContext {
	NetlistContext &netlist;
	ProceduralContext *procedural;

	ast::EvalContext const_;
	const ast::Expression *lvalue = nullptr;

	// Scope nest level tracking to isolate automatic variables of reentrant
	// scopes (i.e. functions)
	Yosys::dict<const ast::Scope *, int> scope_nest_level;
	int current_scope_nest_level;

	int find_nest_level(const ast::Scope *scope);
	Variable variable(const ast::ValueSymbol &symbol);

	RTLIL::SigSpec apply_conversion(const ast::ConversionExpression &conv, RTLIL::SigSpec op);
	RTLIL::SigSpec apply_nested_conversion(const ast::Expression &expr, RTLIL::SigSpec val);
	VariableBits streaming_lhs(ast::StreamingConcatenationExpression const &expr);
	RTLIL::SigSpec streaming(ast::StreamingConcatenationExpression const &expr);

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
	VariableBits lhs(ast::Expression const &expr);

	// Evaluate non-procedural connection LHS for connections expressed in
	// terms of an assignment to `EmptyArgument`. This is a pattern found in
	// the AST in module instance connections or for pattern assignments.
	RTLIL::SigSpec connection_lhs(ast::AssignmentExpression const &assign);

	EvalContext(NetlistContext &netlist);
	EvalContext(NetlistContext &netlist, ProceduralContext &procedural);

	// for testing
	bool ignore_ast_constants = false;

	friend class EnterAutomaticScopeGuard;
};

// guard for entering scopes with automatic variables
class EnterAutomaticScopeGuard {
public:
	EnterAutomaticScopeGuard(EvalContext &context, const ast::Scope *scope);
	~EnterAutomaticScopeGuard();
private:
	EvalContext &context;
	const ast::Scope *scope;
	int save_scope_nest_level;
};

class UnrollLimitTracking {
public:
	UnrollLimitTracking(NetlistContext &netlist, int limit);
	~UnrollLimitTracking();
	void enter_unrolling();
	void exit_unrolling();
	bool unroll_tick(const ast::Statement *symbol);

private:
	NetlistContext &netlist;
	int limit;
	int unrolling = 0;
	int unroll_counter = 0;
	Yosys::pool<const ast::Statement * YS_HASH_PTR_OPS> loops;
	bool error_issued = false;
};

struct ProcessTiming {
	RTLIL::SigBit background_enable = RTLIL::S1;

	struct Sensitivity {
		RTLIL::SigBit signal;
		bool edge_polarity;
		const ast::TimingControl *ast_node;
	};
	std::vector<Sensitivity> triggers;

	bool implicit() const;
	void extract_trigger(NetlistContext &netlist, Yosys::Cell *cell, RTLIL::SigBit enable);
};

class ProceduralContext {
public:
	UnrollLimitTracking unroll_limit;
	NetlistContext &netlist;
	ProcessTiming &timing;
	EvalContext eval;
	int effects_priority = 0;

	Case *root_case;
	Case *current_case;

private:
	Yosys::pool<Variable> seen_blocking_assignment;
	Yosys::pool<Variable> seen_nonblocking_assignment;
	std::vector<RTLIL::Cell *> preceding_memwr;

public:
	ProceduralContext(NetlistContext &netlist, ProcessTiming &timing);
	~ProceduralContext();

	// used to inherit the variable state and effect sequencing of another
	// ProceduralContext without inheriting the ProcessTiming
	void inherit_state(ProceduralContext &other);
	void copy_case_tree_into(RTLIL::CaseRule &rule);
	VariableBits all_driven();

	// Return an enable signal for the current case node
	RTLIL::SigBit case_enable();

	// For $check, $print cells
	void set_effects_trigger(RTLIL::Cell *cell);
	void do_assign(slang::SourceLocation loc, VariableBits lvalue, RTLIL::SigSpec unmasked_rvalue, RTLIL::SigSpec mask, bool blocking);
	void do_simple_assign(slang::SourceLocation loc, VariableBits lvalue, RTLIL::SigSpec rvalue, bool blocking);
	RTLIL::SigSpec substitute_rvalue(VariableBits bits);
	void assign_rvalue(const ast::AssignmentExpression &assign, RTLIL::SigSpec rvalue);

private:
	void assign_rvalue_inner(const ast::AssignmentExpression &assign, const ast::Expression *raw_lexpr,
							 RTLIL::SigSpec raw_rvalue, RTLIL::SigSpec raw_mask, bool blocking);

public:
	struct EscapeFrame {
		// A virtual variable: initialized to zero but assigned one once
		// we are escaping via this or an upper level escape construct
		Variable flag;

		// Non-zero if this is a function
		const ast::SubroutineSymbol *subroutine = nullptr;

		enum EscapeConstructKind {
			Loop, // we escape via this for `break`
			LoopBody, // via this for `continue`
			FunctionBody,
		} kind;
	};

	using EscapeConstructKind = EscapeFrame::EscapeConstructKind;

	Variable get_disable_flag();
	const ast::SubroutineSymbol *get_current_subroutine();
	void signal_escape(slang::SourceLocation loc, EscapeConstructKind kind);

private:
	std::vector<EscapeFrame> escape_stack;

public:
	struct VariableState {
		using Map = Yosys::dict<VariableBit, RTLIL::SigBit>;

		Map visible_assignments;
		Map revert;

		void set(VariableBits lhs, RTLIL::SigSpec value);
		RTLIL::SigSpec evaluate(NetlistContext &netlist, VariableBits vbits);
		RTLIL::SigSpec evaluate(NetlistContext &netlist, VariableChunk vchunk);
		void save(Map &save);
		std::pair<VariableBits, RTLIL::SigSpec> restore(Map &save);
	};

	VariableState vstate;

	friend class RegisterEscapeConstructGuard;
};

using EscapeConstructKind = ProceduralContext::EscapeFrame::EscapeConstructKind;

// guard for registering "escape constructs", i.e. loops and functions
// which are escapable via `break`, `continue` and `return`
class RegisterEscapeConstructGuard {
public:
	RegisterEscapeConstructGuard(ProceduralContext &context,
								 EscapeConstructKind kind,
								 const ast::SubroutineSymbol *subroutine);
	RegisterEscapeConstructGuard(ProceduralContext &context,
								 EscapeConstructKind kind,
								 const ast::Statement *statement);
	~RegisterEscapeConstructGuard();

	// Variable which signals we are escaping
	const Variable flag;

private:
	ProceduralContext &context;
	const ast::Scope *scope;
};

struct RTLILBuilder {
	using SigSpec = RTLIL::SigSpec;

	RTLIL::Module *canvas;
	Yosys::dict<RTLIL::IdString, RTLIL::Const> staged_attributes;

	unsigned next_id = 0;
	std::string new_id(std::string base = std::string());

	SigSpec ReduceBool(SigSpec a);

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

private:
	std::pair<std::string, SigSpec> add_y_wire(int width);
	// apply attributes to newly created cell
	void bless_cell(RTLIL::Cell *cell);
};

class AttributeGuard {
public:
	AttributeGuard(RTLILBuilder &builder)
		: builder(builder)
	{
		save.swap(builder.staged_attributes);
	}

	~AttributeGuard()
	{
		save.swap(builder.staged_attributes);
	}

	void set(RTLIL::IdString id, RTLIL::Const value)
	{
		builder.staged_attributes[id] = value;
	}

private:
	RTLILBuilder &builder;
	Yosys::dict<RTLIL::IdString, RTLIL::Const> save;
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

struct SynthesisSettings {
	std::optional<bool> dump_ast;
	std::optional<bool> no_proc;
	std::optional<bool> compat_mode;
	std::optional<bool> keep_hierarchy;
	std::optional<bool> best_effort_hierarchy;
	std::optional<bool> ignore_timing;
	std::optional<bool> ignore_initial;
	std::optional<bool> ignore_assertions;
	std::optional<int> unroll_limit_;
	std::optional<bool> extern_modules;
	std::optional<bool> no_implicit_memories;
	std::optional<bool> empty_blackboxes;
	std::optional<bool> ast_compilation_only;
	std::optional<bool> no_default_translate_off;
	bool disable_instance_caching = false;

	enum HierMode {
		NONE,
		BEST_EFFORT,
		ALL
	};

	HierMode hierarchy_mode()
	{
		if (keep_hierarchy.value_or(false))
			return ALL;
		if (best_effort_hierarchy.value_or(false))
			return BEST_EFFORT;
		return NONE;
	}

	int unroll_limit() {
		return unroll_limit_.value_or(4000);
	}

	void addOptions(slang::CommandLine &cmdLine);
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
	RTLIL::SigSpec convert_static(VariableBits bits);

	struct Memory {
		int num_wr_ports = 0;
	};
	Yosys::dict<RTLIL::IdString, Memory> emitted_mems;

	// Used to implement modports on uncollapsed levels of hierarchy
	Yosys::dict<const ast::Scope*, std::string YS_HASH_PTR_OPS> scopes_remap;

	// Cache per-symbol Wire* pointers
	Yosys::dict<const ast::Symbol*, RTLIL::Wire *> wire_cache;

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

		emitted_mems.swap(other.emitted_mems);
		scopes_remap.swap(other.scopes_remap);
		wire_cache.swap(other.wire_cache);
		detected_memories.swap(other.detected_memories);
		canvas = other.canvas;
		other.canvas = nullptr;
		disabled = other.disabled;
	}

	Yosys::pool<const ast::Symbol *> detected_memories;
	bool is_inferred_memory(const ast::Symbol &symbol);
	bool is_inferred_memory(const ast::Expression &expr);

	bool is_blackbox(const ast::DefinitionSymbol &sym, slang::Diagnostic *why_blackbox=nullptr);
	bool should_dissolve(const ast::InstanceSymbol &sym, slang::Diagnostic *why_not_dissolved=nullptr);

	// Find the "realm" for given symbol, i.e. the containing instance body which is not
	// getting dissolved (if we are flattening this will be the top body)
	const ast::InstanceBodySymbol &find_symbol_realm(const ast::Symbol &symbol);
	const ast::InstanceBodySymbol &find_common_ancestor(const ast::InstanceBodySymbol &a, const ast::InstanceBodySymbol &b);
	bool check_hier_ref(const ast::ValueSymbol &symbol, slang::SourceRange range);

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
typedef std::pair<VariableChunk, std::string> NamedChunk;
std::vector<NamedChunk> generate_subfield_names(VariableChunk chunk, const ast::Type *type);

};
