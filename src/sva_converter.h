//
// Yosys slang frontend
//
// Copyright 2025 Chaitanya Sharma <chaitanya@cognichip.ai>
// Distributed under the terms of the ISC license, see LICENSE
//
#pragma once

#include "slang_frontend.h"
#include "slang/ast/expressions/AssertionExpr.h"
#include "slang/ast/statements/MiscStatements.h"

namespace slang_frontend {

// Forward declarations
namespace ast = slang::ast;

// Non-deterministic FSM node (NFSM)
// Edges consume clock cycles, links don't (epsilon transitions)
struct SvaNFsmNode {
    std::vector<std::pair<int, RTLIL::SigBit>> edges;  // (target_node, ctrl_signal)
    std::vector<std::pair<int, RTLIL::SigBit>> links;  // (target_node, ctrl_signal)
    bool is_cond_node = false;  // For intersect/within operations
};

// Unlinked FSM node (UFSM) - NFSM after resolving links
struct SvaUFsmNode {
    std::vector<std::pair<int, RTLIL::SigSpec>> edges;  // (target_node, ctrl_signals)
    std::vector<RTLIL::SigSpec> accept;  // Accept conditions
    std::vector<RTLIL::SigSpec> cond;    // Conditional accept (for intersect/within)
    bool reachable = false;
};

// Deterministic FSM node (DFSM)
struct SvaDFsmNode {
    RTLIL::SigSpec ctrl;  // Control signal for this state
    std::vector<std::pair<std::vector<int>, RTLIL::Const>> edges;  // (next_state, ctrl_value)
    std::vector<RTLIL::Const> accept;   // Accept conditions
    std::vector<RTLIL::Const> reject;   // Reject conditions
    
    // Temp data for circuit generation
    RTLIL::Wire *ffoutwire = nullptr;
    RTLIL::SigBit statesig;
    RTLIL::SigSpec nextstate;
    int outnode = -1;  // For getDFsm composition
};

class SVAConverter {
public:
    SVAConverter(NetlistContext &netlist, EvalContext &eval);

    // Main entry point: convert a concurrent assertion statement
    void convert(const ast::ConcurrentAssertionStatement &stmt);

private:
    NetlistContext &netlist;
    EvalContext &eval;

    // Current assertion being processed
    RTLIL::IdString assertion_name;
    RTLIL::SigSpec clk;
    RTLIL::SigSpec rst;
    bool has_reset = false;
    bool uses_past = false;  // Track if assertion uses $past/$changed/$stable

    // Counter for generating unique names
    int counter = 0;

    // Storage for property/sequence definitions
    Yosys::dict<std::string, const ast::AssertionExpr*> property_defs;
    Yosys::dict<std::string, const ast::AssertionExpr*> sequence_defs;

    // Local variables in current property
    Yosys::dict<const ast::Symbol*, RTLIL::Wire*> local_vars;

    // History registers for SVA functions ($past, $rose, $fell)
    Yosys::dict<RTLIL::SigSpec, RTLIL::Wire*> history_regs;

    // Init done signal for each clock (to prevent checking before $past is valid)
    Yosys::dict<RTLIL::SigSpec, RTLIL::Wire*> init_done_regs;
    
    // Condition equality cache (like Verific's cond_eq_cache)
    Yosys::dict<std::pair<RTLIL::SigSpec, RTLIL::SigSpec>, RTLIL::SigBit> cond_eq_cache;
    
    // FSM state explosion limit
    static const int sva_fsm_limit = 64;
    
    RTLIL::SigBit trigger_sig = RTLIL::S1;
    RTLIL::SigBit disable_sig = RTLIL::S0;
    RTLIL::SigBit throughout_sig = RTLIL::S1;
    bool in_cond_mode = false;
    bool materialized = false;
    
    std::vector<RTLIL::SigBit> disable_stack;
    std::vector<RTLIL::SigBit> throughout_stack;
    
    int startNode = -1;
    int acceptNode = -1;
    int condNode = -1;
    std::vector<SvaNFsmNode> nodes;
    
    std::vector<SvaUFsmNode> unodes;
    Yosys::dict<std::vector<int>, SvaDFsmNode> dnodes;
    
    RTLIL::SigBit final_accept_sig = RTLIL::Sx;
    RTLIL::SigBit final_reject_sig = RTLIL::Sx;

    // Generate unique ID
    RTLIL::IdString gen_id(const std::string &prefix = "");

    // Extract clocking from assertion
    void extract_clocking(const ast::AssertionExpr &expr);

    // ===================================================================
    // Sequence/Property parsing (Verific-style: builds NFSM then materializes)
    // ===================================================================
    
    int parse_assertion(const ast::AssertionExpr &expr);
    int parse_sequence(const ast::AssertionExpr &expr, int start_node);
    int parse_simple(const ast::SimpleAssertionExpr &expr, int start_node);
    
    // SVA system functions
    RTLIL::SigBit eval_rose(const ast::CallExpression &call);
    RTLIL::SigBit eval_fell(const ast::CallExpression &call);
    RTLIL::SigBit eval_stable(const ast::CallExpression &call);
    RTLIL::SigBit eval_changed(const ast::CallExpression &call);
    RTLIL::SigSpec eval_past(const ast::CallExpression &call);  // Returns SigSpec to preserve width
    RTLIL::SigSpec create_past_register(RTLIL::SigSpec sig, int depth);

    // Helper: create a D flip-flop with optional reset
    RTLIL::SigSpec create_dff(RTLIL::SigSpec d, RTLIL::IdString name_hint = RTLIL::IdString());

    // Helper: get or create init_done signal for a clock
    RTLIL::SigBit get_init_done(RTLIL::SigSpec clk_sig);

    // Helper: create counter for ranged delays/repetitions
    struct Counter {
        RTLIL::Wire *count_wire;
        RTLIL::SigSpec increment;
        RTLIL::SigSpec reset;
        RTLIL::SigSpec reached_min;
        RTLIL::SigSpec reached_max;
    };

    Counter create_counter(int min_val, int max_val, const std::string &name_hint);

    // Helper: evaluate expression from design
    RTLIL::SigSpec eval_expr(const ast::Expression &expr);
    
    // Helper: create cached condition equality check (like Verific's make_cond_eq)
    RTLIL::SigBit make_cond_eq(const RTLIL::SigSpec &ctrl, RTLIL::SigBit enable = RTLIL::S1);
    
    // Helper: check for state explosion in ctrl signal width
    void check_state_explosion(const RTLIL::SigSpec &ctrl, const std::string &context);
    
    // ========================================================================
    // NFSM/UFSM/DFSM Architecture Methods (like Verific's SvaFsm)
    // ========================================================================
    
    // NFSM construction
    int createNode(int link_node = -1);
    int createStartNode();
    void createEdge(int from_node, int to_node, RTLIL::SigBit ctrl = RTLIL::S1);
    void createLink(int from_node, int to_node, RTLIL::SigBit ctrl = RTLIL::S1);
    
    // Stack management for disable/throughout
    void pushDisable(RTLIL::SigBit sig);
    void popDisable();
    void pushThroughout(RTLIL::SigBit sig);
    void popThroughout();
    
    // NFSM -> UFSM transformation
    void node_to_unode(int node, int unode, RTLIL::SigSpec ctrl);
    void mark_reachable_unode(int unode);
    
    // UFSM -> DFSM transformation
    void create_dnode(const std::vector<int> &state, bool firstmatch, bool condaccept);
    bool cmp_ctrl(const Yosys::pool<RTLIL::SigBit> &ctrl_bits, const RTLIL::SigSpec &ctrl);
    void usortint(std::vector<int> &vec);
    
    // Condition optimization
    void optimize_cond(std::vector<RTLIL::Const> &values);
    RTLIL::SigBit make_cond_eq_dfsm(const RTLIL::SigSpec &ctrl, const RTLIL::Const &value, RTLIL::SigBit enable = RTLIL::S1);
    
    // FSM materialization methods
    RTLIL::SigBit getAccept();
    RTLIL::SigBit getReject();
    void getFirstAcceptReject(RTLIL::SigBit *accept_p, RTLIL::SigBit *reject_p);
    
    // Reset FSM state (for reuse)
    void reset_fsm();
};

} // namespace slang_frontend
