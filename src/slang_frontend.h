//
// Yosys slang frontend
//
// Copyright Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
// clang-format off
#pragma once
#include "slang/ast/EvalContext.h"
#include "slang/ast/expressions/Operator.h"
#include "ir.h"

#ifdef SLANG_NO_YOSYS
#include <set>
#include <unordered_set>
#include "yosys_hashlib.h"
#include "log_stubs.h"
#define YS_HASH_PTR_OPS
#else
// work around yosys PR #4524 changing the way you ask for pointer hashing
#if YS_HASHING_VERSION <= 0
#define YS_HASH_PTR_OPS ,Yosys::hashlib::hash_ptr_ops
#else
#define YS_HASH_PTR_OPS
#endif
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
	namespace driver {
		class Driver;
	}
};

namespace slang_frontend {

using Yosys::log;
using Yosys::log_flush;
using Yosys::log_error;
using Yosys::log_warning;
using Yosys::log_id;
using Yosys::log_signal;
using Yosys::log_abort;
using Yosys::ys_debug;
using Yosys::ceil_log2;
using Yosys::stringf;
#ifndef log_debug
using Yosys::log_debug;
#endif
#ifndef SLANG_NO_YOSYS
namespace RTLIL = ::Yosys::RTLIL;
namespace ID = ::Yosys::RTLIL::ID;
#endif
namespace ast = ::slang::ast;

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
struct HierarchyQueue;
class AttributeGuard;

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

	ir::Value apply_conversion(const ast::ConversionExpression &conv, ir::Value op);
	ir::Value apply_nested_conversion(const ast::Expression &expr, ir::Value val);
	VariableBits streaming_lhs(ast::StreamingConcatenationExpression const &expr);
	ir::Value streaming(ast::StreamingConcatenationExpression const &expr);

	// Evaluates the given symbols/expressions to their value in this context
	ir::Value operator()(ast::Expression const &expr);

	// Evaluates the given expression, inserts an extra sign bit if need
	// be so that the result can always be interpreted as a signed value
	ir::Value eval_signed(ast::Expression const &expr);

	// Describes the given LHS expression in terms of `VariableBits`, if possible.
	//
	// This doesn't handle dynamic addressing and streaming expressions,
	// the caller needs to handle those separately.
	VariableBits lhs(ast::Expression const &expr, bool silent=false);

	// Helper for cases where the AST uses `EmptyArgument` on the RHS of
	// an assignment as a stand-in for a value implied by the context
	// (instance output connection or inside pattern assignments)
	ir::Value connection_lhs(ast::AssignmentExpression const &assign);

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

	ir::Net background_enable = ir::S1;
	struct Sensitivity {
		ir::Net signal;
		bool edge_polarity;
		const ast::TimingControl *ast_node;
	};
	std::vector<Sensitivity> triggers;

#ifndef SLANG_NO_YOSYS
	void extract_trigger(NetlistContext &netlist, Yosys::Cell *cell, ir::Net enable);
#endif

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

#ifndef SLANG_MUX_LOWERING
	std::unique_ptr<Case> root_case;
	Case *current_case;
#else
	ir::Net enabled = ir::S1;
#endif

	// only used when timing.kind==ProcessTiming::Initial
	Yosys::dict<VariableBit, ir::Trit> initial_locals_state;

#ifndef SLANG_NO_YOSYS
	std::vector<RTLIL::Cell *> preceding_memwr;
#endif

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
#ifndef SLANG_MUX_LOWERING
	void copy_case_tree_into(RTLIL::CaseRule &rule);
#endif
	VariableBits all_driven();

	// Return an enable signal for the current case node
	ir::Net case_enable();

	// Action priority barrier: creates a trivial empty switch/case
	void descend_into_empty_case();

#ifndef SLANG_NO_YOSYS
	// For $check, $print cells
	void set_effects_trigger(RTLIL::Cell *cell);
#endif
	void update_variable_state(slang::SourceLocation loc, VariableBits lvalue, ir::Value unmasked_rvalue, ir::Value mask, bool blocking);
	void do_simple_assign(slang::SourceLocation loc, VariableBits lvalue, ir::Value rvalue, bool blocking);
	ir::Value substitute_rvalue(VariableBits bits);
	void assign_rvalue(const ast::AssignmentExpression &assign, ir::Value rvalue);

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
		using Map = Yosys::dict<VariableBit, ir::Net>;

		Map visible_assignments;

		void set(VariableBits lhs, ir::Value value);
		ir::Value evaluate(NetlistContext &netlist, VariableBits vbits);
		ir::Value evaluate(NetlistContext &netlist, VariableChunk vchunk);

		struct Snapshot {
			Map revert;
			Yosys::pool<VariableBit> revert_erase;
		};

		void save(Snapshot &snap);
		std::pair<VariableBits, ir::Value> restore(Snapshot &snap);

	private:
		Snapshot pending;
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

struct BackendGraphBuilderBase {
	// Emits a node for SystemVerilog unary operator
	virtual ir::Value Unop(ast::UnaryOperator op, ir::Value a, bool a_signed, uint64_t y_width) = 0;

	// Emits a node for SystemVerilog binary operator
	virtual ir::Value Biop(ast::BinaryOperator op, ir::Value a, ir::Value b,
				   bool a_signed, bool b_signed, uint64_t y_width) = 0;

	// Demux the operand `a`, i.e. return a value of width `a.width() << s.width()`
	// where each `a`-sized slot is either zeroed out when inactive, or fed through
	// the value of `a` when active, and where the operand `s` selects the active slot.
	virtual ir::Value Demux(ir::Value a, ir::Value s) = 0;

	// Bitwise mux between `a` and `b` controlled by `s`. All operands and the return value
	// have the same width.
	virtual ir::Value Bwmux(ir::Value a, ir::Value b, ir::Value s) = 0;

	// Mux with addressing input `s`. Width of `a` must be a multiple of `1 << s.width()`
	// and the return value has width `a.width() / (1 << s.width())`
	virtual ir::Value Bmux(ir::Value a, ir::Value s) = 0;

	// Return value `a` shifted to the right by amount `s`. Shiftx pads the output with X
	// while Shift pads with zeroes.
	virtual ir::Value Shift(ir::Value a, ir::Value s, bool s_signed, uint64_t result_width) = 0;
	virtual ir::Value Shiftx(ir::Value a, ir::Value s, bool s_signed, uint64_t result_width) = 0;

	virtual ir::Value Mux(ir::Value a, ir::Value b, ir::Net s) = 0;

    // Create a placeholder signal which will be connected to a driver using `connect` later
	virtual ir::Value add_placeholder_signal(uint64_t width, std::string_view name_suggestion=""sv, bool public_name=false) = 0;

    // `target` must be composed solely of signal bits created using add_placeholder_signal
	virtual void connect(ir::Value target, ir::Value source) = 0;

	// Set initialization on the driver of `signal`
	//
	// `signal` is exactly as returned from an earlier call to `add_placeholder_signal`
	virtual void set_initialization(ir::Value signal, ir::Const init_value) = 0;

	// Add initialization data on the given memory. The data starts
	// at bit position `base` which does not need be a word boundary
	virtual void add_memory_init(std::string_view name, uint64_t bit_offset,
						 		 bool big_endian, ir::Const data) = 0;

	// Mark a placeholder signal as a module input port.
	virtual void add_input(std::string_view name, ir::Value signal) { (void)name; (void)signal; }

	// Create a module output port driven by the given signal.
	virtual void add_output(std::string_view name, ir::Value signal) { (void)name; (void)signal; }

	// Instantiate a blackbox cell with named port connections.
	struct PortConnection {
		std::string name;
		enum Direction { kInput, kOutput, kInOut } direction;
		ir::Value value;
	};
	virtual void add_instance(std::string_view cell_type,
	                          std::vector<PortConnection> ports) {
		(void)cell_type; (void)ports;
	}

	virtual void add_dual_edge_aldff(const std::string &base_name, ir::Value clk,
							 		 ir::Value aload, ir::Value d, ir::Value q,
							 		 ir::Value ad, bool aload_polarity) = 0;
	virtual void add_dff(std::string_view name, const ir::Value &clk, const ir::Value &d,
		 		 const ir::Value &q, bool clk_polarity=true) = 0;
	virtual void add_dffe(std::string_view name, const ir::Value &clk, const ir::Value &en,
		 		  const ir::Value &d, const ir::Value &q, bool clk_polarity=true,
				  bool en_polarity=true) = 0;
	virtual void add_aldff(std::string_view name, const ir::Value &clk, const ir::Value &aload,
		   		   const ir::Value &d, const ir::Value &q, const ir::Value &ad,
				   bool clk_polarity = true, bool aload_polarity = true) = 0;
};

class BackendGraphBuilder;

struct GraphBuilder {
	std::unique_ptr<BackendGraphBuilder> backend;

	ir::Value Demux(ir::Value a, ir::Value s);
	ir::Value Bwmux(ir::Value a, ir::Value b, ir::Value s);
	ir::Value Bmux(ir::Value a, ir::Value s);
	ir::Value Shift(ir::Value a, ir::Value s, bool s_signed, uint64_t result_width);
	ir::Value Shiftx(ir::Value a, ir::Value s, bool s_signed, uint64_t result_width);
	ir::Net ReduceBool(ir::Value a);
	ir::Net Le(ir::Value a, ir::Value b, bool is_signed);
	ir::Net Ge(ir::Value a, ir::Value b, bool is_signed);
	ir::Net Lt(ir::Value a, ir::Value b, bool is_signed);
	ir::Net Eq(ir::Value a, ir::Value b);
	ir::Net LogicAnd(ir::Value a, ir::Value b);
	ir::Net LogicOr(ir::Value a, ir::Value b);
	ir::Net LogicNot(ir::Value a);
	ir::Value Mux(ir::Value a, ir::Value b, ir::Net s);
	ir::Value Neg(ir::Value a, bool signed_);
	ir::Value Not(ir::Value a);
	ir::Value Unop(ast::UnaryOperator op, ir::Value a, bool a_signed, uint64_t y_width);
	ir::Value Biop(ast::BinaryOperator op, ir::Value a, ir::Value b,
				 bool a_signed, bool b_signed, uint64_t y_width);
	ir::Value CountOnes(ir::Value sig, int result_width);

	ir::Value add_placeholder_signal(uint64_t width, std::string_view name_suggestion=""sv, bool public_name=false);
	void connect(ir::Value target, ir::Value source);
	void set_initialization(ir::Value signal, ir::Const init_value);
	void add_memory_init(std::string_view name, uint64_t bit_offset,
						 bool big_endian, ir::Const data);
	void add_input(std::string_view name, ir::Value signal);
	void add_output(std::string_view name, ir::Value signal);
	void add_instance(std::string_view cell_type, std::vector<BackendGraphBuilderBase::PortConnection> ports);
	void add_dual_edge_aldff(const std::string &base_name, ir::Value clk,
							 ir::Value aload, ir::Value d, ir::Value q,
							 ir::Value ad, bool aload_polarity);
	void add_dff(std::string_view name, const ir::Value &clk, const ir::Value &d,
				 const ir::Value &q, bool clk_polarity=true);
	void add_dffe(std::string_view name, const ir::Value &clk, const ir::Value &en,
				 const ir::Value &d, const ir::Value &q, bool clk_polarity=true,
				 bool en_polarity=true);
	void add_aldff(std::string_view name, const ir::Value &clk, const ir::Value &aload,
				   const ir::Value &d, const ir::Value &q, const ir::Value &ad,
				   bool clk_polarity = true, bool aload_polarity = true);
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

	void addOptions(slang::CommandLine &cmdLine);
};

struct SynthesisSettings;
struct NetlistContext : GraphBuilder, public DiagnosticIssuer {
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
	std::string unescaped_id(const ast::Symbol &sym);
	std::string hdlname(const ast::Symbol &sym);

	ir::Value add_wire(const ast::ValueSymbol &sym);
	ir::Value wire(const ast::Symbol &sym);
	ir::Value convert_static(VariableBits bits);

#ifndef SLANG_NO_YOSYS
	struct Memory {
		int num_wr_ports = 0;
	};
	Yosys::dict<RTLIL::IdString, Memory> emitted_mems;
#endif

	// Used to implement modports on `realm`
	Yosys::dict<const ast::Scope*, std::string YS_HASH_PTR_OPS> scopes_remap;

	// Cache per-symbol signal
	Yosys::dict<const ast::Symbol*, ir::Value> wire_cache;

	Yosys::pool<VariableBit> driven_variables;

	// Driven by a register, including a latch
	Yosys::pool<VariableBit> register_driven_variables;

	// wor/wand support
	Yosys::dict<VariableBit, ir::Value> special_net_drivers;
	std::vector<const ast::NetSymbol *> special_net_symbols;

	// Initial variable state
	Yosys::dict<VariableBit, ir::Trit> initial_state;

	// Flag to disable elaboration; we set this when `scopes_remap` is
	// incomplete due to prior errors
	bool disabled = false;

	NetlistContext(std::unique_ptr<BackendGraphBuilder> backend,
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
	void add_continuous_driver(VariableBits lhs, ir::Value rhs);

	ir::Const convert_svint(const slang::SVInt &svint, slang::SourceLocation loc);
	const std::optional<ir::Const> convert_const(const slang::ConstantValue &constval, slang::SourceLocation loc);
};

// A single bit position in a match pattern: either a concrete net or a wildcard
struct PatternBit
{
	enum Kind { Concrete, Wildcard } kind;
	ir::Net net; // meaningful only when kind == Concrete

	PatternBit() : kind(Wildcard) {}
	PatternBit(ir::Net n) : kind(Concrete), net(n) {}
	static PatternBit wildcard() { return {}; }
	bool is_wildcard() const { return kind == Wildcard; }
	bool is_const() const { return kind == Wildcard || net.is_const(); }
	bool operator==(const PatternBit &o) const
	{
		if (kind != o.kind)
			return false;
		return kind == Wildcard || net == o.net;
	}
	bool operator!=(const PatternBit &o) const { return !(*this == o); }
};

// A match pattern: sequence of PatternBit, used in case compare expressions and `inside` operators
struct ValuePattern
{
	std::vector<PatternBit> bits;

	ValuePattern() {}
	ValuePattern(ir::Net n) : bits{PatternBit(n)} {}
	ValuePattern(ir::Trit t) : bits{PatternBit(ir::Net(t))} {}

	// All-concrete pattern from an ir::Value (no wildcards)
	ValuePattern(ir::Value v)
	{
		bits.reserve(v.size());
		for (int i = 0; i < v.size(); i++)
			bits.push_back(PatternBit(v[i]));
	}

	int size() const { return (int)bits.size(); }
	bool empty() const { return bits.empty(); }

	bool is_fully_concrete() const
	{
		for (auto &b : bits)
			if (b.is_wildcard())
				return false;
		return true;
	}

	bool is_fully_def() const
	{
		for (auto &b : bits)
			if (b.is_wildcard() || !b.net.is_def())
				return false;
		return true;
	}

	bool is_fully_const() const
	{
		for (auto &b : bits)
			if (!b.is_const())
				return false;
		return true;
	}

	// Convert to ir::Value. Only valid when is_fully_concrete().
	ir::Value to_value() const
	{
		ir::Value v;
		v.reserve(bits.size());
		for (auto &b : bits)
			v.append(b.net);
		return v;
	}
};

// slang_frontend.cc
ir::Net matches_pattern(NetlistContext &builder, const ValuePattern &pattern, ir::Value &value);
ir::Value inside_comparison(EvalContext &eval, ir::Value left, const ast::Expression &expr);
extern std::string hierpath_relative_to(const ast::Scope *relative_to, const ast::Scope *scope);
#ifndef SLANG_NO_YOSYS
void transfer_attrs(NetlistContext &netlist, const ast::Symbol &from, RTLIL::AttrObject *to);
void transfer_attrs(NetlistContext &netlist, const ast::Statement &from, RTLIL::AttrObject *to);
void transfer_attrs(NetlistContext &netlist, const ast::Expression &from, RTLIL::AttrObject *to);
#endif
void transfer_attrs(NetlistContext &netlist, const ast::Symbol &from, AttributeGuard &guard);
void transfer_attrs(NetlistContext &netlist, const ast::Statement &from, AttributeGuard &guard);
void transfer_attrs(NetlistContext &netlist, const ast::Expression &from, AttributeGuard &guard);
uint64_t bitstream_member_offset(const ast::FieldSymbol &member);
bool is_special_net_type(const ast::NetType &type);
bool is_special_net(const ast::Symbol &symbol);
void finalize_special_nets(NetlistContext &netlist);

#ifndef SLANG_NO_YOSYS
// blackboxes.cc
extern void import_blackboxes_from_rtlil(slang::SourceManager &mgr, ast::Compilation &target, RTLIL::Design *source);
extern bool is_decl_empty_module(const slang::syntax::SyntaxNode &syntax);
extern void export_blackbox_to_rtlil(NetlistContext &netlist, const ast::InstanceSymbol &inst, RTLIL::Design *target);
#endif

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

// initialization.cc
void evaluate_decl_initializers(NetlistContext &netlist);
void finalize_variable_initialization(NetlistContext &netlist);

// addressing.cc
class AddressingResolver {
public:
	AddressingResolver(EvalContext &eval, const ast::ElementSelectExpression &sel);
	AddressingResolver(EvalContext &eval, const ast::RangeSelectExpression &sel);

	ir::Value shift_up(ir::Value val, bool oor_undef, uint64_t output_len);
	ir::Value demux(ir::Value val, uint64_t output_len);
	ir::Value mux(ir::Value val, uint64_t output_len);
	ir::Value shift_down(ir::Value val, uint64_t output_len);
	template <typename Bundle> Bundle extract(Bundle val, uint64_t width);

	bool is_static();

	slang::ConstantRange range;
	int64_t stride = 1;
private:
	void interpret_index(ir::Value signal, int64_t width_down = 1, int64_t width_up = 1);

	ir::Value shift_up_bitwise(ir::Value val, bool oor_undef, uint64_t output_len);
	ir::Value shift_down_bitwise(ir::Value val, uint64_t output_len);
	ir::Value raw_demux(ir::Value val, int64_t from, int64_t to);
	ir::Value raw_mux(ir::Value val, int64_t from, int64_t to, uint64_t stride);
	ir::Value embed(ir::Value val, uint64_t output_len, int64_t stride, ir::Trit padding);

	// these summed together are the zero-based index of the bottom item
	// of the selection
	ir::Value raw_signal;
	int64_t base_offset;

	const ast::Expression &expr;
	EvalContext &eval;
	NetlistContext &netlist;
};

// procedural.cc
void assign_to_lvalue_with_masking(const ast::AssignmentExpression &assign,
								   ProceduralContext &context, LValue &lvalue,
								   ir::Value rvalue, ir::Value mask, bool blocking);

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
	static LValue memoryWrite(Variable variable, ir::Value address, uint64_t bitsize);

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
		ir::Value address;
	};

	std::variant<Variable, Concatenation, RangeSelect, MemberAccess, MemoryWrite> descriptor;
	bool contiguous_slice_;
	bool static_;
	uint64_t bitsize;

	LValue(decltype(descriptor) descriptor, uint64_t bitsize, bool static_, bool contiguous_slice_)
		: descriptor(std::move(descriptor)), bitsize(bitsize), static_(static_), contiguous_slice_(contiguous_slice_) {}

	friend void assign_to_lvalue_with_masking(const ast::AssignmentExpression &assign,
								   ProceduralContext &context, LValue &lvalue,
								   ir::Value rvalue, ir::Value mask, bool blocking);
};

// slang_frontend.cc
const std::string module_type_id(const ast::InstanceBodySymbol &sym);
void catch_forbidden_options(slang::driver::Driver &driver);
void fixup_options(SynthesisSettings &settings, slang::driver::Driver &driver);
const ast::InstanceBodySymbol &get_instance_body(SynthesisSettings &settings, const ast::InstanceSymbol &instance);
void populate_netlist(HierarchyQueue &hqueue, NetlistContext &netlist);
void add_internal_symbols(NetlistContext &netlist, const ast::InstanceBodySymbol &body);

struct HierarchyQueue {
	template<class... Args>
	std::pair<NetlistContext&, bool> get_or_emplace(const ast::InstanceBodySymbol *symbol, Args&&... args)
	{
		if (netlists.count(symbol)) {
			return {*netlists.at(symbol), false};
		} else {
			NetlistContext *ref = new NetlistContext(std::forward<Args>(args)...);
			netlists[symbol] = ref;
			queue.push_back(ref);
			return {*ref, true};
		}
	}

	~HierarchyQueue()
	{
		for (auto netlist : queue)
			delete netlist;
	}

	std::map<const ast::InstanceBodySymbol *, NetlistContext *> netlists;
	std::vector<NetlistContext *> queue;
};

};
