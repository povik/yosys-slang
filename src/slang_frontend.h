//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
// clang-format off
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
		class FieldSymbol;
		class NetSymbol;
		class ElementSelectExpression;
		class RangeSelectExpression;
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
class LValue;

class Variable {
public:
	enum Kind {
		Static,
		Local,
		EscapeFlag,
		Dummy,
		Invalid
	} kind;

	static Variable from_symbol(const ast::ValueSymbol *symbol, int depth=-1);
	static Variable escape_flag(int id);
	static Variable dummy(uint64_t width);

	Variable();
	const ast::ValueSymbol *get_symbol() const;
	uint64_t bitwidth() const;
	explicit operator bool() const;

	bool operator==(const Variable &other) const { return hash_label() == other.hash_label(); }
	bool operator<(const Variable &other) const;

#if YS_HASHING_VERSION >= 1
	[[nodiscard]] Yosys::Hasher hash_into(Yosys::Hasher h) const { h.eat(hash_label()); return h; }
#else
	int hash() const { return Yosys::hash_ops<HashLabel>::hash(hash_label()); }
#endif
	std::string text() const;

private:
	union {
		const ast::ValueSymbol *symbol;
		uint64_t width;
		int id;
	};
	int depth = 0;

	Variable(enum Kind kind, const ast::ValueSymbol *symbol, int depth);
	Variable(enum Kind kind, const ast::Statement *statement, int depth);
	Variable(enum Kind kind, uint64_t width);

	typedef std::tuple<int, void *, uint64_t> HashLabel;
	HashLabel hash_label() const;

public:
	bool is_special_net();
};

struct EvalContext {
	NetlistContext &netlist;
	ProceduralContext *procedural;

	ast::EvalContext const_;
	const ast::Expression *lvalue = nullptr;

	// Scope nest level tracking to isolate automatic variables of reentrant
	// scopes (i.e. functions)
	Yosys::dict<const ast::Scope *, int> scope_nest_level;

	int find_nest_level(const ast::Scope *scope);
	Variable variable(const ast::ValueSymbol &symbol);

	RTLIL::SigSpec apply_conversion(const ast::ConversionExpression &conv, RTLIL::SigSpec op);
	RTLIL::SigSpec apply_nested_conversion(const ast::Expression &expr, RTLIL::SigSpec val);
	VariableBits streaming_lhs(ast::StreamingConcatenationExpression const &expr);
	RTLIL::SigSpec streaming(ast::StreamingConcatenationExpression const &expr);

	// Evaluates the given symbols/expressions to their value in this context
	RTLIL::SigSpec operator()(ast::Expression const &expr);

	// Evaluates the given expression, inserts an extra sign bit if need
	// be so that the result can always be interpreted as a signed value
	RTLIL::SigSpec eval_signed(ast::Expression const &expr);

	// Describes the given LHS expression in terms of `VariableBits`, if possible.
	//
	// This doesn't handle dynamic addressing and streaming expressions,
	// the caller needs to handle those separately.
	VariableBits lhs(ast::Expression const &expr, bool silent=false);

	// Helper for cases where the AST uses `EmptyArgument` on the RHS of
	// an assignment as a stand-in for a value implied by the context
	// (instance output connection or inside pattern assignments)
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
	enum Kind {
		Initial,
		Implicit,
		EdgeTriggered
	} kind = Implicit;

	RTLIL::SigBit background_enable = RTLIL::S1;
	struct Sensitivity {
		RTLIL::SigBit signal;
		bool edge_polarity;
		const ast::TimingControl *ast_node;
	};
	std::vector<Sensitivity> triggers;

	void extract_trigger(NetlistContext &netlist, Yosys::Cell *cell, RTLIL::SigBit enable);

	static ProcessTiming implicit;
	static ProcessTiming initial;

	ProcessTiming(Kind kind);
};

class ProceduralContext {
public:
	UnrollLimitTracking unroll_limit;
	NetlistContext &netlist;
	ProcessTiming &timing;
	EvalContext eval;
	int effects_priority = 0;

	std::unique_ptr<Case> root_case;
	Case *current_case;

	// only used when timing.kind==ProcessTiming::Initial
	Yosys::dict<VariableBit, RTLIL::State> initial_locals_state;

	std::vector<RTLIL::Cell *> preceding_memwr;

private:
	int flag_counter = 0;
	Yosys::dict<Variable, slang::SourceLocation> seen_blocking_assignment;
	Yosys::dict<Variable, slang::SourceLocation> seen_nonblocking_assignment;

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
	void update_variable_state(slang::SourceLocation loc, VariableBits lvalue, RTLIL::SigSpec unmasked_rvalue, RTLIL::SigSpec mask, bool blocking);
	void do_simple_assign(slang::SourceLocation loc, VariableBits lvalue, RTLIL::SigSpec rvalue, bool blocking);
	RTLIL::SigSpec substitute_rvalue(VariableBits bits);
	void assign_rvalue(const ast::AssignmentExpression &assign, RTLIL::SigSpec rvalue);

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
	SigSpec EqWildcard(SigSpec a, SigSpec b);
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

	SigSpec CountOnes(SigSpec sig, int result_width);

	void add_dual_edge_aldff(const std::string &base_name, RTLIL::SigSpec clk,
							 RTLIL::SigSpec aload, RTLIL::SigSpec d, RTLIL::SigSpec q,
							 RTLIL::SigSpec ad, bool aload_polarity);
	void add_dff(std::string_view name, const RTLIL::SigSpec &clk, const RTLIL::SigSpec &d,
				 const RTLIL::SigSpec &q, bool clk_polarity=true);
	void add_dffe(std::string_view name, const RTLIL::SigSpec &clk, const RTLIL::SigSpec &en,
				 const RTLIL::SigSpec &d, const RTLIL::SigSpec &q, bool clk_polarity=true,
				 bool en_polarity=true);
	void add_aldff(std::string_view name, const RTLIL::SigSpec &clk, const RTLIL::SigSpec &aload,
				   const RTLIL::SigSpec &d, const RTLIL::SigSpec &q, const RTLIL::SigSpec &ad,
				   bool clk_polarity = true, bool aload_polarity = true);

    // Create a placeholder signal which will be connected to a driver using `connect` later
	SigSpec add_placeholder_signal(uint64_t width, std::string_view name_suggestion=""sv, bool public_name=false);

    // `target` must be composed solely of signal bits created using add_placeholder_signal
	void connect(SigSpec target, SigSpec source);

	// Add initialization data on the given memory. The data starts
	// at bit position `base` which doesn't need to be on a word boundary
	void add_memory_init(std::string_view name, uint64_t bit_offset,
						 bool big_endian, RTLIL::Const data);

private:
	int meminit_prio_counter = 0;
	void emit_meminit_cell(RTLIL::Memory *mem, uint64_t word_offset,
						   bool big_endian, RTLIL::Const data,
						   RTLIL::Const mask);

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

#define UDP_HANDL(x) x(error) x(blackboxes)
SLANG_ENUM(UdpHandleMode, UDP_HANDL)
#undef UDP_HANDL

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
	std::optional<bool> allow_dual_edge_ff;
	std::optional<bool> no_synthesis_define;
	std::optional<UdpHandleMode> udp_handling;
	std::optional<std::string> ff_naming;
	std::optional<std::string> ff_prefix;
	std::optional<std::string> ff_suffix;
	// pass std::less<> to enable transparent lookup
	std::set<std::string, std::less<>> blackboxed_modules;
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

	std::string ff_naming_mode() {
		return ff_naming.value_or("legacy");
	}

	std::string ff_naming_prefix() {
		if (ff_prefix.has_value())
			return ff_prefix.value();
		if (ff_naming_mode() == "legacy")
			return "$driver$";
		return "";
	}

	std::string ff_naming_suffix() {
		if (ff_suffix.has_value())
			return ff_suffix.value();
		if (ff_naming_mode() == "legacy")
			return "";
		return "_reg";
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
	std::string id(const ast::Symbol &sym);
	std::string id(const ast::ValueSymbol &sym);
	std::string hdlname(const ast::Symbol &sym);

	RTLIL::SigSpec add_wire(const ast::ValueSymbol &sym);
	RTLIL::SigSpec wire(const ast::Symbol &sym);
	RTLIL::SigSpec convert_static(VariableBits bits);

	struct Memory {
		int num_wr_ports = 0;
	};
	Yosys::dict<RTLIL::IdString, Memory> emitted_mems;

	// Used to implement modports on `realm`
	Yosys::dict<const ast::Scope*, std::string YS_HASH_PTR_OPS> scopes_remap;

	// Cache per-symbol SigSpec
	Yosys::dict<const ast::Symbol*, RTLIL::SigSpec> wire_cache;

	Yosys::pool<VariableBit> driven_variables;

	// Driven by a register, including a latch
	Yosys::pool<VariableBit> register_driven_variables;

	// wor/wand support
	Yosys::dict<VariableBit, RTLIL::SigSpec> special_net_drivers;
	std::vector<const ast::NetSymbol *> special_net_symbols;

	// Initial variable state
	Yosys::dict<VariableBit, RTLIL::State> initial_state;

	// Flag to disable elaboration; we set this when `scopes_remap` is
	// incomplete due to prior errors
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

	Yosys::pool<const ast::Symbol *> detected_memories;
	bool is_inferred_memory(const ast::Symbol &symbol);
	bool is_inferred_memory(const ast::Expression &expr);

	bool is_blackbox(const ast::DefinitionSymbol &sym, slang::Diagnostic *why_blackbox=nullptr);
	bool should_dissolve(const ast::InstanceSymbol &sym, slang::Diagnostic *why_not_dissolved=nullptr);

	// Find the "realm" for the given symbol, i.e. the containing instance body
	// which is not getting dissolved during netlist emission. If we are fully flattening
	// this will be the top module.
	const ast::InstanceBodySymbol &find_symbol_realm(const ast::Symbol &symbol);
	const ast::InstanceBodySymbol &find_common_ancestor(const ast::InstanceBodySymbol &a, const ast::InstanceBodySymbol &b);
	bool check_hier_ref(const ast::ValueSymbol &symbol, slang::SourceRange range, bool silent=false);

	void register_driven(const VariableBits &vbits);
	void register_driven(const ast::Symbol &symbol);
	void add_continuous_driver(VariableBits lhs, RTLIL::SigSpec rhs);

	const std::optional<RTLIL::Const> convert_const(const slang::ConstantValue &constval, slang::SourceLocation loc);
};

// slang_frontend.cc
RTLIL::SigBit inside_comparison(EvalContext &eval, RTLIL::SigSpec left, const ast::Expression &expr);
extern std::string hierpath_relative_to(const ast::Scope *relative_to, const ast::Scope *scope);
template<typename T> void transfer_attrs(NetlistContext &netlist, T &from, RTLIL::AttrObject *to);
template<typename T> void transfer_attrs(NetlistContext &netlist, T &from, AttributeGuard &guard);
template<typename T> void transfer_attrs(T &from, RTLIL::AttrObject *to);
uint64_t bitstream_member_offset(const ast::FieldSymbol &member);
bool is_special_net_type(const ast::NetType &type);
bool is_special_net(const ast::Symbol &symbol);
void finalize_special_nets(NetlistContext &netlist);

// blackboxes.cc
extern void import_blackboxes_from_rtlil(slang::SourceManager &mgr, ast::Compilation &target, RTLIL::Design *source);
extern bool is_decl_empty_module(const slang::syntax::SyntaxNode &syntax);
extern void export_blackbox_to_rtlil(NetlistContext &netlist, const ast::InstanceSymbol &inst, RTLIL::Design *target);

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
std::string format_scope_name_fragment(const ast::Scope *relative_to, const ast::Scope *scope);
std::string format_signal_name_fragment(const ast::Scope *relative_to, const ast::ValueSymbol &symbol,
		std::string_view suffix);

// initialization.cc
void evaluate_decl_initializers(NetlistContext &netlist);
void finalize_variable_initialization(NetlistContext &netlist);

// addressing.cc
class AddressingResolver {
public:
	AddressingResolver(EvalContext &eval, const ast::ElementSelectExpression &sel);
	AddressingResolver(EvalContext &eval, const ast::RangeSelectExpression &sel);

	RTLIL::SigSpec shift_up(RTLIL::SigSpec val, bool oor_undef, int output_len);
	RTLIL::SigSpec demux(RTLIL::SigSpec val, int output_len);
	RTLIL::SigSpec mux(RTLIL::SigSpec val, int output_len);
	RTLIL::SigSpec shift_down(RTLIL::SigSpec val, int output_len);
	template <typename Bundle> Bundle extract(Bundle val, uint64_t width);

	bool is_static();

	slang::ConstantRange range;
	int stride = 1;
private:
	void interpret_index(RTLIL::SigSpec signal, int width_down = 1, int width_up = 1);

	RTLIL::SigSpec shift_up_bitwise(RTLIL::SigSpec val, bool oor_undef, int output_len);
	RTLIL::SigSpec shift_down_bitwise(RTLIL::SigSpec val, int output_len);
	RTLIL::SigSpec raw_demux(RTLIL::SigSpec val, int from, int to);
	RTLIL::SigSpec raw_mux(RTLIL::SigSpec val, int from, int to, int stride);
	RTLIL::SigSpec embed(RTLIL::SigSpec val, int output_len, int stride, RTLIL::State padding);

	// these summed together are the zero-based index of the bottom item
	// of the selection
	RTLIL::SigSpec raw_signal;
	int base_offset;

	const ast::Expression &expr;
	EvalContext &eval;
	NetlistContext &netlist;
};

// procedural.cc
void assign_to_lvalue_with_masking(const ast::AssignmentExpression &assign,
								   ProceduralContext &context, LValue &lvalue,
								   RTLIL::SigSpec rvalue, RTLIL::SigSpec mask, bool blocking);

// lvalue.cc
class LValue {
public:
	~LValue() = default;
	LValue(LValue &&) = default;
	LValue &operator=(LValue &&) = default;

	static std::optional<LValue> analyze(EvalContext &context, const ast::Expression &expr, bool silent=false);

	static LValue variable(Variable variable);
	static LValue concatenation(std::vector<LValue> elements);
	static LValue rangeSelect(LValue inner, AddressingResolver resolver, uint64_t bitsize);
	static LValue memberAccess(LValue inner, uint64_t base_offset, uint64_t bitsize);
	static LValue memoryWrite(Variable variable, RTLIL::SigSpec address, uint64_t bitsize);

	bool is_static();
	bool is_contiguous_slice();

	// Only available if is_static() true
	VariableBits evaluate_vbits();

private:
	struct Concatenation {
		std::vector<LValue> elements;
	};

	struct RangeSelect {
		std::unique_ptr<AddressingResolver> resolver;
		std::unique_ptr<LValue> inner;
	};

	struct MemberAccess {
		uint64_t base_offset;
		std::unique_ptr<LValue> inner;
	};

	struct MemoryWrite {
		Variable target;
		RTLIL::SigSpec address;
	};

	std::variant<Variable, Concatenation, RangeSelect, MemberAccess, MemoryWrite> descriptor;
	bool contiguous_slice_;
	bool static_;
	uint64_t bitsize;

	LValue(decltype(descriptor) descriptor, uint64_t bitsize, bool static_, bool contiguous_slice_)
		: descriptor(std::move(descriptor)), bitsize(bitsize), static_(static_), contiguous_slice_(contiguous_slice_) {}

	friend void assign_to_lvalue_with_masking(const ast::AssignmentExpression &assign,
								   ProceduralContext &context, LValue &lvalue,
								   RTLIL::SigSpec rvalue, RTLIL::SigSpec mask, bool blocking);
};

};
