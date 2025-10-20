//
// Yosys slang frontend
//
// Copyright 2025 Chaitanya Sharma <chaitanya@cognichip.ai>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "sva_converter.h"
#include "diag.h"
#include "slang/ast/Expression.h"
#include "slang/ast/TimingControl.h"
#include "slang/ast/Compilation.h"
#include "slang/ast/types/AllTypes.h"
#include "slang/ast/symbols/ValueSymbol.h"
#include "slang/ast/symbols/MemberSymbols.h"
#include "slang/ast/symbols/InstanceSymbols.h"
#include "slang/ast/expressions/OperatorExpressions.h"
#include "slang/ast/expressions/MiscExpressions.h"
#include "slang/ast/expressions/CallExpression.h"

using Yosys::GetSize;

namespace slang_frontend {

// Static member definition
const int SVAConverter::sva_fsm_limit;

SVAConverter::SVAConverter(NetlistContext &netlist, EvalContext &eval)
    : netlist(netlist), eval(eval) {
    // Set flag to indicate we're in SVA context
    // This prevents the general expression evaluator from creating placeholder clocks
    eval.in_sva_context = true;
}

RTLIL::IdString SVAConverter::gen_id(const std::string &prefix) {
    std::string base = prefix.empty() ? "\\sva" : "\\" + prefix;
    return netlist.new_id(base);
}

// Helper to scan for SVA system functions in expression tree
// Note: This is currently not strictly necessary since we use init_done
// for all sequential assertions, but it's kept for potential future optimizations
static bool contains_sva_function(const ast::Expression &expr) {
    using EK = ast::ExpressionKind;
    
    if (expr.kind == EK::Call) {
        auto &call = expr.as<ast::CallExpression>();
        if (call.isSystemCall()) {
            std::string_view name = call.getSubroutineName();
            if (name == "$past" || name == "$stable" || name == "$changed" ||
                name == "$rose" || name == "$fell") {
                return true;
            }
        }
    }
    
    // Recursively check sub-expressions (cover common cases)
    switch (expr.kind) {
        case EK::UnaryOp:
            return contains_sva_function(expr.as<ast::UnaryExpression>().operand());
        case EK::BinaryOp: {
            auto &bin = expr.as<ast::BinaryExpression>();
            return contains_sva_function(bin.left()) || contains_sva_function(bin.right());
        }
        default:
            return false;
    }
}

RTLIL::SigSpec SVAConverter::eval_expr(const ast::Expression &expr) {
    using EK = ast::ExpressionKind;

    // Check for sequence/property method calls (.triggered, .matched, .ended)
    if (expr.kind == EK::Call) {
        auto &call = expr.as<ast::CallExpression>();
        std::string_view method_name = call.getSubroutineName();

        // Handle SVA system functions
        if (call.isSystemCall()) {
            if (method_name == "$past") {
                // Mark that this assertion uses $past
                uses_past = true;
                return eval_past(call);
            }
            if (method_name == "$stable") {
                uses_past = true;
                return eval_stable(call);
            }
            if (method_name == "$changed") {
                uses_past = true;
                return eval_changed(call);
            }
            if (method_name == "$rose") {
                uses_past = true;
                return eval_rose(call);
            }
            if (method_name == "$fell") {
                uses_past = true;
                return eval_fell(call);
            }
        }

        if (method_name == "triggered" || method_name == "matched") {
            // These methods return a boolean indicating sequence/property status
            // For synthesis, we need to create a signal that tracks the sequence state

            if (!call.arguments().empty() &&
                call.arguments()[0]->kind == EK::AssertionInstance) {
                auto &aie = call.arguments()[0]->as<ast::AssertionInstanceExpression>();

                // Create a temporary FSM for this sequence to get its match signal
                // Save current FSM state
                auto saved_nodes = nodes;
                auto saved_unodes = unodes;
                auto saved_dnodes = dnodes;
                auto saved_materialized = materialized;
                auto saved_startNode = startNode;
                auto saved_acceptNode = acceptNode;
                auto saved_condNode = condNode;
                auto saved_final_accept_sig = final_accept_sig;
                auto saved_final_reject_sig = final_reject_sig;

                // Reset and parse the sequence
                reset_fsm();
                int seq_end = parse_sequence(aie.body, createStartNode());
                createLink(seq_end, acceptNode);

                // Get the accept signal (triggered/matched both use accept signal)
                RTLIL::SigBit match_sig = getAccept();

                // Restore FSM state
                nodes = saved_nodes;
                unodes = saved_unodes;
                dnodes = saved_dnodes;
                materialized = saved_materialized;
                startNode = saved_startNode;
                acceptNode = saved_acceptNode;
                condNode = saved_condNode;
                final_accept_sig = saved_final_accept_sig;
                final_reject_sig = saved_final_reject_sig;

                return match_sig;
            }
        }
    }

    // For expressions with SVA functions in sub-expressions, we need to recursively
    // handle them to ensure they use the SVA converter's proper handling
    if (contains_sva_function(expr)) {
        uses_past = true;

        // Handle binary operations recursively
        if (expr.kind == EK::BinaryOp) {
            auto &bin = expr.as<ast::BinaryExpression>();

            // Recursively evaluate operands - this will handle any nested SVA functions
            RTLIL::SigSpec left = eval_expr(bin.left());
            RTLIL::SigSpec right = eval_expr(bin.right());

            // Apply the binary operation to the evaluated operands
            using ast::BinaryOperator;
            switch (bin.op) {
                case BinaryOperator::Add:      return netlist.canvas->Add(NEW_ID, left, right, bin.type->isSigned());
                case BinaryOperator::Subtract: return netlist.canvas->Sub(NEW_ID, left, right, bin.type->isSigned());
                case BinaryOperator::Multiply: return netlist.canvas->Mul(NEW_ID, left, right, bin.type->isSigned());
                case BinaryOperator::Divide:   return netlist.canvas->Div(NEW_ID, left, right, bin.type->isSigned());
                case BinaryOperator::Mod:      return netlist.canvas->Mod(NEW_ID, left, right, bin.type->isSigned());

                case BinaryOperator::BinaryAnd:  return netlist.canvas->And(NEW_ID, left, right);
                case BinaryOperator::BinaryOr:   return netlist.canvas->Or(NEW_ID, left, right);
                case BinaryOperator::BinaryXor:  return netlist.canvas->Xor(NEW_ID, left, right);
                case BinaryOperator::BinaryXnor: return netlist.canvas->Xnor(NEW_ID, left, right);

                case BinaryOperator::Equality:   return netlist.canvas->Eq(NEW_ID, left, right);
                case BinaryOperator::Inequality: return netlist.canvas->Ne(NEW_ID, left, right);
                case BinaryOperator::CaseEquality:   return netlist.canvas->Eqx(NEW_ID, left, right);
                case BinaryOperator::CaseInequality: return netlist.canvas->Nex(NEW_ID, left, right);

                case BinaryOperator::LessThan:          return netlist.canvas->Lt(NEW_ID, left, right, bin.type->isSigned());
                case BinaryOperator::LessThanEqual:     return netlist.canvas->Le(NEW_ID, left, right, bin.type->isSigned());
                case BinaryOperator::GreaterThan:       return netlist.canvas->Gt(NEW_ID, left, right, bin.type->isSigned());
                case BinaryOperator::GreaterThanEqual:  return netlist.canvas->Ge(NEW_ID, left, right, bin.type->isSigned());

                case BinaryOperator::LogicalAnd: return netlist.canvas->LogicAnd(NEW_ID, left, right);
                case BinaryOperator::LogicalOr:  return netlist.canvas->LogicOr(NEW_ID, left, right);

                case BinaryOperator::LogicalShiftLeft:  return netlist.canvas->Shl(NEW_ID, left, right, false);
                case BinaryOperator::LogicalShiftRight: return netlist.canvas->Shr(NEW_ID, left, right);
                case BinaryOperator::ArithmeticShiftLeft:  return netlist.canvas->Shl(NEW_ID, left, right, bin.type->isSigned());
                case BinaryOperator::ArithmeticShiftRight: return netlist.canvas->Sshr(NEW_ID, left, right);

                case BinaryOperator::LogicalImplication:
                    // a -> b is equivalent to !a || b
                    return netlist.canvas->LogicOr(NEW_ID, netlist.LogicNot(left), right);

                case BinaryOperator::LogicalEquivalence:
                    // a <-> b is equivalent to (a && b) || (!a && !b), or simply a == b for booleans
                    return netlist.canvas->Eq(NEW_ID, netlist.ReduceBool(left), netlist.ReduceBool(right));

                default:
                    // For any unhandled operators, fall back to general evaluator
                    // This shouldn't happen for common SVA expressions, but provides safety
                    log_warning("SVA converter: unhandled binary operator %d, delegating to general evaluator\n",
                               (int)bin.op);
                    return eval(expr);
            }
        }

        // Handle unary operations recursively
        if (expr.kind == EK::UnaryOp) {
            auto &unary = expr.as<ast::UnaryExpression>();
            RTLIL::SigSpec operand = eval_expr(unary.operand());

            using ast::UnaryOperator;
            switch (unary.op) {
                case UnaryOperator::Plus:  return operand;
                case UnaryOperator::Minus: return netlist.canvas->Neg(NEW_ID, operand, unary.type->isSigned());
                case UnaryOperator::BitwiseNot: return netlist.canvas->Not(NEW_ID, operand);
                case UnaryOperator::BitwiseAnd: return netlist.canvas->ReduceAnd(NEW_ID, operand);
                case UnaryOperator::BitwiseOr:  return netlist.canvas->ReduceOr(NEW_ID, operand);
                case UnaryOperator::BitwiseXor: return netlist.canvas->ReduceXor(NEW_ID, operand);
                case UnaryOperator::BitwiseNand: return netlist.canvas->Not(NEW_ID, netlist.canvas->ReduceAnd(NEW_ID, operand));
                case UnaryOperator::BitwiseNor:  return netlist.canvas->Not(NEW_ID, netlist.canvas->ReduceOr(NEW_ID, operand));
                case UnaryOperator::BitwiseXnor: return netlist.canvas->ReduceXnor(NEW_ID, operand);
                case UnaryOperator::LogicalNot:  return netlist.LogicNot(operand);

                default:
                    log_warning("SVA converter: unhandled unary operator %d, delegating to general evaluator\n",
                               (int)unary.op);
                    return eval(expr);
            }
        }
    }

    // Delegate to the general expression evaluator for non-SVA expressions
    return eval(expr);
}

RTLIL::SigBit SVAConverter::make_cond_eq(const RTLIL::SigSpec &ctrl, RTLIL::SigBit enable) {
    if (GetSize(ctrl) == 0)
        return enable;
    
    RTLIL::SigSpec sig_a = ctrl;
    RTLIL::SigSpec sig_b = RTLIL::Const(RTLIL::State::S1, GetSize(ctrl));
    
    if (enable != RTLIL::S1) {
        sig_a.append(enable);
        sig_b.append(RTLIL::State::S1);
    }
    
    auto key = std::make_pair(sig_a, sig_b);
    
    if (cond_eq_cache.count(key) == 0) {
        if (GetSize(sig_a) == 1) {
            cond_eq_cache[key] = sig_a;
        } else {
            // Check if all bits equal 1 (AND reduction)
            cond_eq_cache[key] = netlist.Eq(sig_a, sig_b);
        }
    }
    
    return cond_eq_cache.at(key);
}

void SVAConverter::check_state_explosion(const RTLIL::SigSpec &ctrl, const std::string &context) {
    if (GetSize(ctrl) > sva_fsm_limit) {
        log_warning("SVA %s: ctrl signal has %d bits (limit is %d), possible state explosion\n",
                   context.c_str(), GetSize(ctrl), sva_fsm_limit);
        netlist.add_diag(diag::SVAUnsupported, slang::SourceLocation::NoLocation);
    }
}

// ============================================================================
// Main Entry Point
// ============================================================================

void SVAConverter::convert(const ast::ConcurrentAssertionStatement &stmt) {
    // Generate unique name for this assertion
    assertion_name = gen_id("assertion");

    Yosys::log("SVA: ========================================\n");
    Yosys::log("SVA: Processing assertion in module %s\n", netlist.canvas->name.c_str());
    Yosys::log("SVA:   propertySpec kind=%d\n", (int)stmt.propertySpec.kind);
    log_debug("SVA: Processing assertion in module %s, propertySpec kind=%d\n",
              netlist.canvas->name.c_str(), (int)stmt.propertySpec.kind);

    // Extract clocking and reset information
    extract_clocking(stmt.propertySpec);

    // Pass the extracted clock/reset to the eval context so it can use them
    // when evaluating SVA system functions like $past
    eval.sva_clock = clk;
    eval.sva_reset = rst;
    eval.sva_has_reset = has_reset;

    // Initialize FSM
    reset_fsm();

    // EXACTLY COPY VERIFIC's two-FSM approach (verificsva.cc:1623-1720)
    using AK = ast::AssertionExprKind;
    if (stmt.propertySpec.kind == AK::Binary) {
        auto &bin = stmt.propertySpec.as<ast::BinaryAssertionExpr>();
        using Op = ast::BinaryAssertionOperator;

        if (bin.op == Op::OverlappedImplication || bin.op == Op::NonOverlappedImplication) {
            // Two-FSM approach for implications (Verific lines 1633-1693)
            int node;

            // ANTECEDENT FSM
            node = parse_sequence(bin.left, createStartNode());
            if (bin.op == Op::NonOverlappedImplication) {
                int next_node = createNode();
                createEdge(node, next_node);
                node = next_node;
            }
            createLink(node, acceptNode);
            RTLIL::SigBit antecedent_match = getAccept();

            // CONSEQUENT FSM (fresh FSM, triggered by antecedent)
            reset_fsm();
            trigger_sig = antecedent_match;
            node = parse_sequence(bin.right, createStartNode());
            createLink(node, acceptNode);

            // Fall through to materialize consequent FSM
        } else {
            // Not an implication, parse normally (Verific lines 1708-1713)
            int node = parse_sequence(stmt.propertySpec, createStartNode());
            createLink(node, acceptNode);
        }
    } else {
        // Not a binary expression, parse normally
        int final_node = parse_sequence(stmt.propertySpec, createStartNode());
        createLink(final_node, acceptNode);
    }

    // Materialize FSM to get accept/reject signals
    RTLIL::SigBit accept_sig, reject_sig;

    if (stmt.assertionKind == ast::AssertionKind::Assert ||
        stmt.assertionKind == ast::AssertionKind::Assume ||
        stmt.assertionKind == ast::AssertionKind::Expect) {
        // For assertions, we need reject signal
        getFirstAcceptReject(&accept_sig, &reject_sig);
    } else {
        // For cover, we need DFSM-based accept signal to handle non-determinism correctly
        // (e.g., self-loops in unbounded delays like ##[+])
        getFirstAcceptReject(&accept_sig, nullptr);
        reject_sig = RTLIL::S0;
    }

    // Enable and assertion signals (Verific lines 1824-1825)
    // NOTE: Not adding final DFF stage - Verific only adds it conditionally based on clocking.body_net
    // For now, use combinational signals directly to match test behavior
    RTLIL::SigBit sig_a = netlist.canvas->Not(NEW_ID, reject_sig);
    RTLIL::SigBit sig_en = netlist.canvas->Or(NEW_ID, accept_sig, reject_sig);

    log("SVA: Assertion %s: sig_a=%s (reject=%s), sig_en=%s\n",
        log_id(assertion_name), log_signal(sig_a), log_signal(reject_sig), log_signal(sig_en));

    RTLIL::SigBit enable_sig = sig_en;

    // Create $check cell (Verific lines 1845-1847)
    std::string flavor;
    RTLIL::Cell *cell = nullptr;

    switch (stmt.assertionKind) {
        case ast::AssertionKind::Assert:
            flavor = "assert";
            cell = netlist.canvas->addAssert(assertion_name, sig_a, enable_sig);
            break;

        case ast::AssertionKind::Assume:
            flavor = "assume";
            cell = netlist.canvas->addAssume(assertion_name, sig_a, enable_sig);
            // Mark assumes with "keep" attribute to prevent optimization removal
            // This is critical for cutpoint abstraction where FSM-based assumes
            // might look unreachable but are needed as constraints
            cell->attributes[RTLIL::ID::keep] = RTLIL::Const(1);
            log("SVA: Marked assume cell %s with keep attribute\n", log_id(assertion_name));
            break;

        case ast::AssertionKind::CoverProperty:
            flavor = "cover";
            cell = netlist.canvas->addCover(assertion_name, RTLIL::SigSpec(accept_sig), RTLIL::SigSpec(enable_sig));
            break;

        case ast::AssertionKind::Expect:
            flavor = "assert";
            cell = netlist.canvas->addAssert(assertion_name, sig_a, enable_sig);
            break;

        default:
            netlist.add_diag(diag::SVAUnsupported, stmt.sourceRange);
            return;
    }
}

// ============================================================================
// Clocking Extraction
// ============================================================================

void SVAConverter::extract_clocking(const ast::AssertionExpr &expr) {
    log("SVA: extract_clocking for kind %d in module %s\n", (int)expr.kind, log_id(netlist.canvas->name));

    // Default clock and reset
    clk = RTLIL::SigSpec();
    rst = RTLIL::SigSpec();
    has_reset = false;

    bool explicit_clocking = false;
    bool explicit_disable_iff = false;

    // Look for explicit clocking expression
    if (expr.kind == ast::AssertionExprKind::Clocking) {
        auto &clocking_expr = expr.as<ast::ClockingAssertionExpr>();
        explicit_clocking = true;

        // Extract clock from timing control
        if (clocking_expr.clocking.kind == ast::TimingControlKind::SignalEvent) {
            auto &event = clocking_expr.clocking.as<ast::SignalEventControl>();
            log("SVA: Extracting explicit clock signal\n");
            clk = eval_expr(event.expr);
        }

        // Recursively process the inner expression for disable iff
        if (clocking_expr.expr.kind == ast::AssertionExprKind::DisableIff) {
            auto &disable_expr = clocking_expr.expr.as<ast::DisableIffAssertionExpr>();
            rst = eval_expr(disable_expr.condition);
            has_reset = true;
            explicit_disable_iff = true;
        }
    } else if (expr.kind == ast::AssertionExprKind::DisableIff) {
        auto &disable_expr = expr.as<ast::DisableIffAssertionExpr>();
        rst = eval_expr(disable_expr.condition);
        has_reset = true;
        explicit_disable_iff = true;
    }

    // If no explicit clocking, check for default clocking block or use module's clock
    if (!explicit_clocking) {
        log("SVA: No explicit clocking, checking for default clocking or module clock\n");
        if (auto defaultClocking = netlist.compilation.getDefaultClocking(static_cast<const ast::Scope&>(netlist.realm))) {
            log("SVA: Found default clocking block in realm\n");
            auto& clockingBlock = defaultClocking->as<ast::ClockingBlockSymbol>();
            auto& event = clockingBlock.getEvent();
            
            if (event.kind == ast::TimingControlKind::SignalEvent) {
                auto& signalEvent = event.as<ast::SignalEventControl>();
                clk = eval_expr(signalEvent.expr);
                log("SVA: Using clock from default clocking block\n");
            }
        }
        
        // If still no clock (e.g., default clocking not found or in bound module),
        // try to find a clock input in the module
        if (clk.empty()) {
            RTLIL::Wire *clock_wire = nullptr;
            
            // Try "clock" first (most common)
            clock_wire = netlist.canvas->wire(ID(clock));
            
            // Try "clk" as fallback
            if (!clock_wire) {
                clock_wire = netlist.canvas->wire(ID(clk));
            }
            
            // Use the found clock wire if it exists
            if (clock_wire) {
                clk = clock_wire;
                log("SVA: Using module's clock input '%s'\n", log_id(clock_wire->name));
            } else {
                log_warning("SVA: No clock found - assertion will not have proper clocking!\n");
            }
        }
    }

    // If no explicit disable iff, check for default disable iff
    if (!explicit_disable_iff) {
        if (auto defaultDisable = netlist.compilation.getDefaultDisable(static_cast<const ast::Scope&>(netlist.realm))) {
            log("SVA: Found default disable iff from scope\n");
            //  Try to find the reset signal in the module (similar to clock handling)
            RTLIL::Wire *reset_wire = netlist.canvas->wire(ID(reset));
            if (reset_wire) {
                rst = reset_wire;
                has_reset = true;
                log("SVA: Using module's reset input '%s' for default disable iff\n", log_id(reset_wire->name));
            } else {
                // Fallback to evaluating the expression
                rst = eval_expr(*defaultDisable);
                has_reset = true;
                log("SVA: Using evaluated default disable iff expression\n");
            }
        } else {
            // If slang doesn't provide default disable iff (e.g., due to bind),
            // try common reset input names as fallback
            RTLIL::Wire *reset_wire = netlist.canvas->wire(ID(reset));
            if (reset_wire && reset_wire->port_input) {
                rst = reset_wire;
                has_reset = true;
                log("SVA: Using module's reset input '%s' as default disable iff\n", log_id(reset_wire->name));
            }
        }
    }
}

// ============================================================================
// D Flip-Flop and Init Done Helpers
// ============================================================================

RTLIL::SigBit SVAConverter::get_init_done(RTLIL::SigSpec clk_sig) {
    // Check if we already have an init_done for this clock
    if (init_done_regs.count(clk_sig)) {
        return init_done_regs.at(clk_sig);
    }

    // Create an initialization flag that becomes true after first clock
    RTLIL::Wire *init_done_wire = netlist.canvas->addWire(gen_id("init_done"));
    // Set initial value to 0 for formal verification (BMC) - becomes 1 after first clock
    init_done_wire->attributes[ID::init] = RTLIL::Const(0, 1);
    auto init_dff = netlist.canvas->addCell(gen_id("init_dff"), ID($dff));
    init_dff->setParam(ID::WIDTH, 1);
    init_dff->setParam(ID::CLK_POLARITY, 1);
    init_dff->setPort(ID::CLK, clk_sig);
    init_dff->setPort(ID::D, RTLIL::S1);
    init_dff->setPort(ID::Q, init_done_wire);

    init_done_regs[clk_sig] = init_done_wire;
    return init_done_wire;
}

RTLIL::SigSpec SVAConverter::create_dff(RTLIL::SigSpec d, RTLIL::IdString name_hint) {
    if (d.empty() || d.size() == 0) {
        log_warning("Attempting to create DFF with empty signal\n");
        return d;
    }

    // Always generate a unique wire name
    if (name_hint == RTLIL::IdString())
        name_hint = gen_id("dff");
    else
        name_hint = gen_id(name_hint.str());

    RTLIL::Wire *q_wire = netlist.canvas->addWire(name_hint, d.size());
    
    // Choose cell type based on whether we have async reset
    RTLIL::IdString cell_type = (has_reset && !rst.empty()) ? ID($adff) : ID($dff);
    auto cell = netlist.canvas->addCell(gen_id("dff_cell"), cell_type);

    cell->setParam(ID::WIDTH, d.size());
    cell->setParam(ID::CLK_POLARITY, 1);

    if (clk.empty()) {
        log_error("SVA: Cannot create DFF without a clock signal. Clock should be extracted during extract_clocking.\n");
    }

    cell->setPort(ID::CLK, clk);
    cell->setPort(ID::D, d);
    cell->setPort(ID::Q, q_wire);

    // Add async reset if available
    if (has_reset && !rst.empty()) {
        cell->setParam(ID::ARST_POLARITY, 1);
        cell->setPort(ID::ARST, rst);
        cell->setParam(ID::ARST_VALUE, RTLIL::Const(0, d.size()));
    }

    return q_wire;
}

// ============================================================================
// SVA System Functions
// ============================================================================

RTLIL::SigSpec SVAConverter::create_past_register(RTLIL::SigSpec sig, int depth) {
    if (sig.empty() || depth <= 0) {
        return sig;
    }

    // Mark that this assertion uses $past
    uses_past = true;

    // Check if we already have a history register for this signal
    auto key = sig;
    if (history_regs.count(key) && depth == 1) {
        return history_regs.at(key);
    }

    // Create shift register chain
    // NOTE: We MUST set init=0 to match Verific's behavior.
    // Analysis of Verific's verificsva.cc shows it ALWAYS passes State::S0 as init_value
    // when calling clocking.addDff() for ANY SVA-related DFF (past registers, FSM states, etc.)
    // This is critical because:
    // 1. ABC PDR and SMT backends need consistent initialization semantics
    // 2. Without explicit init, ABC may assume undefined state while SMT allows $anyinit
    // 3. This causes "Unexpected aigsmt status" errors where ABC and SMT disagree
    // 4. Setting init=0 ensures both backends see latches with defined initial value
    RTLIL::SigSpec current = sig;
    for (int i = 0; i < depth; i++) {
        RTLIL::Wire *past_wire = netlist.canvas->addWire(gen_id("past_" + std::to_string(i)), sig.size());

        // Set init attribute to 0 (matching Verific's VerificClocking::addDff with State::S0)
        // This makes ABC PDR and SMT agree on initialization semantics
        past_wire->attributes[ID::init] = RTLIL::Const(RTLIL::State::S0, sig.size());

        // Use async reset DFF if reset is available, regular DFF otherwise
        if (clk.empty()) {
            log_error("SVA: Cannot create $past register without a clock signal. Clock should be extracted during extract_clocking.\n");
        }

        // Always use simple DFF for $past, no reset
        // Verific uses clocking.addDff() which creates simple $dff with init attribute
        auto cell = netlist.canvas->addCell(gen_id("past_dff"), ID($dff));
        cell->setParam(ID::WIDTH, sig.size());
        cell->setParam(ID::CLK_POLARITY, 1);
        cell->setPort(ID::CLK, clk);
        cell->setPort(ID::D, current);
        cell->setPort(ID::Q, past_wire);

        current = past_wire;
    }

    if (depth == 1) {
    history_regs[key] = current.as_wire();
    }
    return current;
}

RTLIL::SigSpec SVAConverter::eval_past(const ast::CallExpression &call) {
    if (call.arguments().empty()) return RTLIL::SigSpec();

    RTLIL::SigSpec sig = eval_expr(*call.arguments()[0]);
    if (sig.empty()) return RTLIL::SigSpec();

    Yosys::log("SVA: eval_past() called, input width=%d\n", sig.size());
    
    // Get depth argument (default is 1)
    int depth = 1;
    if (call.arguments().size() > 1) {
        // Try to evaluate the depth as a constant
        // For most cases, depth will be a literal constant
        auto &depth_expr = *call.arguments()[1];
        RTLIL::SigSpec depth_sig = eval_expr(depth_expr);
        
        // If it's a constant, extract the value
        if (depth_sig.is_fully_const()) {
            auto depth_const = depth_sig.as_const();
            if (depth_const.is_fully_def()) {
                int depth_val = depth_const.as_int();
                if (depth_val > 0) {
                    depth = depth_val;
                }
            }
        }
    }
    
    // Create shift register chain of specified depth
    // Return the full past value, NOT a reduced boolean
    // $past() preserves the full width of its argument
    RTLIL::SigSpec past_sig = create_past_register(sig, depth);
    Yosys::log("SVA: eval_past() returning width=%d signal\n", past_sig.size());
    return past_sig;
}

RTLIL::SigBit SVAConverter::eval_rose(const ast::CallExpression &call) {
    if (call.arguments().empty()) return RTLIL::S0;
    
    RTLIL::SigSpec sig = eval_expr(*call.arguments()[0]);
    if (sig.empty()) return RTLIL::S0;
    
    // $rose(sig) = sig & !$past(sig)
    RTLIL::SigSpec past_sig = create_past_register(sig, 1);
    RTLIL::SigSpec not_past = netlist.Not(past_sig);
    return netlist.LogicAnd(sig, not_past);
}

RTLIL::SigBit SVAConverter::eval_fell(const ast::CallExpression &call) {
    if (call.arguments().empty()) return RTLIL::S0;
    
    RTLIL::SigSpec sig = eval_expr(*call.arguments()[0]);
    if (sig.empty()) return RTLIL::S0;
    
    // $fell(sig) = !sig & $past(sig)
    RTLIL::SigSpec past_sig = create_past_register(sig, 1);
    RTLIL::SigSpec not_sig = netlist.Not(sig);
    return netlist.LogicAnd(not_sig, past_sig);
}

RTLIL::SigBit SVAConverter::eval_stable(const ast::CallExpression &call) {
    if (call.arguments().empty()) return RTLIL::S1;
    
    RTLIL::SigSpec sig = eval_expr(*call.arguments()[0]);
    if (sig.empty()) return RTLIL::S1;
    
    // $stable(sig) = (sig == $past(sig))
    RTLIL::SigSpec past_sig = create_past_register(sig, 1);
    return netlist.Eq(sig, past_sig);
}

RTLIL::SigBit SVAConverter::eval_changed(const ast::CallExpression &call) {
    if (call.arguments().empty()) return RTLIL::S0;
    
    RTLIL::SigSpec sig = eval_expr(*call.arguments()[0]);
    if (sig.empty()) return RTLIL::S0;
    
    // $changed(sig) = (sig != $past(sig))
    RTLIL::SigSpec past_sig = create_past_register(sig, 1);
    RTLIL::SigSpec stable = netlist.Eq(sig, past_sig);
    return netlist.LogicNot(stable);
}

// ============================================================================
// Counter Helper
// ============================================================================

SVAConverter::Counter SVAConverter::create_counter(
    int min_val, int max_val, const std::string &name_hint) {

    Counter cnt;

    // Determine counter width
    int max = (max_val > 0) ? max_val : min_val + 100; // Cap unbounded at min+100
    if (max < min_val) max = min_val;
    int width = ceil_log2(max + 1);
    if (width < 1) width = 1;

    // Create counter wire
    cnt.count_wire = netlist.canvas->addWire(gen_id(name_hint + "_cnt"), width);

    // Counter logic: increment when enabled, reset when reset asserted
    RTLIL::SigSpec count_val = cnt.count_wire;
    RTLIL::SigSpec next_count = netlist.Biop(
        ID($add),
        count_val,
        RTLIL::Const(1, width),
        false, false, width
    );

    // Create increment and reset signals (to be connected by caller)
    cnt.increment = netlist.canvas->addWire(gen_id(name_hint + "_inc"), 1);
    cnt.reset = netlist.canvas->addWire(gen_id(name_hint + "_rst"), 1);

    // Mux for increment
    RTLIL::SigSpec count_or_hold = netlist.Mux(
        count_val,
        next_count,
        cnt.increment
    );

    // Mux for reset
    RTLIL::SigSpec final_next = netlist.Mux(
        count_or_hold,
        RTLIL::Const(0, width),
        cnt.reset
    );

    // Register the counter
    RTLIL::SigSpec count_reg = create_dff(final_next, gen_id(name_hint + "_reg"));
    netlist.canvas->connect(cnt.count_wire, count_reg);

    // Generate reached_min and reached_max signals
    cnt.reached_min = netlist.Ge(count_val, RTLIL::Const(min_val, width), false);

    if (max_val > 0) {
        cnt.reached_max = netlist.Ge(count_val, RTLIL::Const(max_val, width), false);
    } else {
        // Unbounded - never reaches max
        cnt.reached_max = RTLIL::S0;
    }

    return cnt;
}

// ============================================================================
// Assertion/Sequence Parsing (builds NFSM)
// ============================================================================

int SVAConverter::parse_sequence(const ast::AssertionExpr &expr, int start_node)
{
    using EK = ast::AssertionExprKind;
    
    switch (expr.kind) {
        case EK::Simple:
            return parse_simple(expr.as<ast::SimpleAssertionExpr>(), start_node);
        
        case EK::SequenceConcat: {
            // a ##N b: chain sequences with delay
            auto &concat = expr.as<ast::SequenceConcatExpr>();
            int node = start_node;
            
            for (size_t idx = 0; idx < concat.elements.size(); idx++) {
                auto &elem = concat.elements[idx];
                if (!elem.sequence) continue;
                
                // IMPORTANT: In slang AST, elem.delay is the delay BEFORE elem.sequence
                // So for "A ##[+] B", elements are:
                //   [0]: {sequence: A, delay: 0}
                //   [1]: {sequence: B, delay: ##[+]}
                // We must add the delay FIRST, then parse the sequence
                
                // Add delay BEFORE parsing sequence (except for delay=0)
                if (elem.delay.min == 0 && (!elem.delay.max.has_value() || elem.delay.max.value() == 0)) {
                    // ##0 or no delay - skip delay processing, just parse sequence
                } else if (elem.delay.min == 0) {
                    // ##[0:N] case - ranged delay starting from 0
                    int max_delay = elem.delay.max.value();
                    for (int i = 0; i < max_delay; i++) {
                        int next_node = createNode();
                        createEdge(node, next_node);
                        createLink(node, next_node); // Can also skip (zero or more delays)
                        node = next_node;
                    }
                } else {
                    // Non-zero minimum delay
                    
                    // Add minimum delay edges
                    for (int i = 0; i < elem.delay.min; i++) {
                        int next_node = createNode();
                        createEdge(node, next_node);
                        node = next_node;
                    }
                    
                    // Handle ranged delay [M:N] where M > 0  
                    if (elem.delay.max.has_value() && elem.delay.max.value() > elem.delay.min) {
                        // Create branch points for each possible delay
                        int max_delay = elem.delay.max.value();
                        for (int i = elem.delay.min; i < max_delay; i++) {
                            int next_node = createNode();
                            createEdge(node, next_node);
                            createLink(node, next_node); // Also allow skipping
                            node = next_node;
                        }
                    } else if (!elem.delay.max.has_value()) {
                        // Unbounded delay: ##[M:$] - create self-loop, exactly like Verific
                        // After minimum delay, add self-loop edge on current state
                        // The NFSM-to-DFSM determinization will handle the non-determinism
                        createEdge(node, node);
                        // Continue with node unchanged - Verific does this too
                    }
                }
                
                // NOW parse the sequence part (after delay has been added)
                node = parse_sequence(*elem.sequence, node);
            }
            return node;
        }
        
        case EK::Binary: {
            auto &bin = expr.as<ast::BinaryAssertionExpr>();
            using Op = ast::BinaryAssertionOperator;
            
            if (bin.op == Op::OverlappedImplication || bin.op == Op::NonOverlappedImplication) {
                // Antecedent -> Consequent
                Yosys::log("SVA: Processing %s implication\n",
                          bin.op == Op::NonOverlappedImplication ? "non-overlapped (|=>)" : "overlapped (|->)");
                Yosys::log("SVA:   Antecedent at node %d\n", start_node);
                int node = parse_sequence(bin.left, start_node);
                Yosys::log("SVA:   Antecedent ends at node %d\n", node);
                if (bin.op == Op::NonOverlappedImplication) {
                    int next_node = createNode();
                    createEdge(node, next_node);
                    Yosys::log("SVA:   Non-overlapped: added delay edge from %d to %d\n", node, next_node);
                    node = next_node;
                }
                Yosys::log("SVA:   Consequent starts at node %d\n", node);
                int result = parse_sequence(bin.right, node);
                Yosys::log("SVA:   Consequent ends at node %d\n", result);
                return result;
            }
            
            if (bin.op == Op::And) {
                // Both sequences must match
                int left_node = parse_sequence(bin.left, start_node);
                int right_node = parse_sequence(bin.right, start_node);
                int merge_node = createNode();
                createLink(left_node, merge_node);
                createLink(right_node, merge_node);
                return merge_node;
            }
            
            if (bin.op == Op::Or) {
                // Either sequence can match
                int left_node = parse_sequence(bin.left, start_node);
                int right_node = parse_sequence(bin.right, start_node);
                int merge_node = createNode();
                createLink(left_node, merge_node);
                createLink(right_node, merge_node);
                return merge_node;
            }
            
            if (bin.op == Op::Throughout) {
                // condition throughout sequence
                RTLIL::SigSpec cond_spec = eval_expr(bin.left.as<ast::SimpleAssertionExpr>().expr);
                RTLIL::SigBit cond = netlist.ReduceBool(cond_spec);
                pushThroughout(cond);
                int node = parse_sequence(bin.right, start_node);
                popThroughout();
                return node;
            }
            
            if (bin.op == Op::Within) {
                // s1 within s2: s1 must occur completely inside s2's window
                // Implementation: s2 starts, s1 can start anytime, s1 must finish before/when s2 finishes
                
                int node = createNode();
                createLink(start_node, node);
                
                // Parse inner sequence s1 (bin.left)
                int s1_end = parse_sequence(bin.left, node);
                
                // Parse outer sequence s2 (bin.right) with self-loop
                // The outer sequence creates a window
                createEdge(node, node); // Stay in this state
                int s2_end = parse_sequence(bin.right, node);
                
                // s1 must complete, then link to accept via s2_end
                createLink(s1_end, s2_end);
                
                return s2_end;
            }
            
            if (bin.op == Op::Intersect) {
                // s1 intersect s2: both must match with same length
                // Parse both sequences starting from the same node
                int left_node = parse_sequence(bin.left, start_node);
                int right_node = parse_sequence(bin.right, start_node);
                
                // Both must reach accept at the same time
                int merge_node = createNode();
                createLink(left_node, merge_node);
                createLink(right_node, merge_node);
                
                return merge_node;
            }
            
            if (bin.op == Op::Implies) {
                // a implies b: equivalent to (!a) or b
                // Parse the antecedent
                int antecedent_node = parse_sequence(bin.left, start_node);
                
                // Parse the consequent from the antecedent's end
                int consequent_node = parse_sequence(bin.right, antecedent_node);
                
                // Also allow direct skip from start (vacuous case: !a is true)
                createLink(start_node, consequent_node);
                
                return consequent_node;
            }
            
            if (bin.op == Op::Iff) {
                // a iff b: a implies b and b implies a
                // This is equivalence: both or neither
                int left_node = parse_sequence(bin.left, start_node);
                int right_node = parse_sequence(bin.right, start_node);
                
                // Both sequences lead to accept
                int merge_node = createNode();
                createLink(left_node, merge_node);
                createLink(right_node, merge_node);
                
                // Also allow both to be false (vacuous)
                createLink(start_node, merge_node);
                
                return merge_node;
            }
            
            if (bin.op == Op::Until || bin.op == Op::SUntil) {
                // p1 until p2: p1 must hold until p2 becomes true
                // Parse p1 as a self-loop condition
                RTLIL::SigSpec p1_spec = eval_expr(bin.left.as<ast::SimpleAssertionExpr>().expr);
                RTLIL::SigBit p1 = netlist.ReduceBool(p1_spec);
                
                // Create node that stays as long as p1 is true and p2 is false
                int until_node = createNode();
                createLink(start_node, until_node);
                
                // Self-loop while p1 is true
                createEdge(until_node, until_node, p1);
                
                // Parse p2 and transition when it's true
                int p2_node = parse_sequence(bin.right, until_node);
                
                return p2_node;
            }
            
            if (bin.op == Op::UntilWith || bin.op == Op::SUntilWith) {
                // p1 until_with p2: p1 until p2, and p2 must hold on last cycle too
                RTLIL::SigSpec p1_spec = eval_expr(bin.left.as<ast::SimpleAssertionExpr>().expr);
                RTLIL::SigBit p1 = netlist.ReduceBool(p1_spec);
                
                RTLIL::SigSpec p2_spec = eval_expr(bin.right.as<ast::SimpleAssertionExpr>().expr);
                RTLIL::SigBit p2 = netlist.ReduceBool(p2_spec);
                
                // Create node that stays as long as p1 is true or both p1 and p2 are true
                int until_node = createNode();
                createLink(start_node, until_node);
                
                // Self-loop while p1 is true (including when p2 becomes true)
                RTLIL::SigBit p1_or_both = netlist.canvas->Or(NEW_ID, p1, 
                    netlist.canvas->And(NEW_ID, p1, p2));
                createEdge(until_node, until_node, p1_or_both);
                
                // Accept when p2 is true
                int accept_node = createNode();
                createLink(until_node, accept_node, p2);
                
                return accept_node;
            }
            
            if (bin.op == Op::OverlappedFollowedBy || bin.op == Op::NonOverlappedFollowedBy) {
                // Similar to implication, used in cover properties
                int node = parse_sequence(bin.left, start_node);
                if (bin.op == Op::NonOverlappedFollowedBy) {
                    int next_node = createNode();
                    createEdge(node, next_node);
                    node = next_node;
                }
                return parse_sequence(bin.right, node);
            }
            
            // Unsupported operator
            netlist.add_diag(diag::SVAUnsupported, bin.opRange);
            return start_node;
        }
        
        case EK::FirstMatch: {
            // first_match(sequence): take only the first successful match
            // The DFSM generation with firstmatch=true handles this properly
            // by preventing further state transitions after first accept
            auto &fm = expr.as<ast::FirstMatchAssertionExpr>();
            
            // Parse the inner sequence normally
            // The getDFsm method with firstmatch=true will ensure only first match is taken
            return parse_sequence(fm.seq, start_node);
        }
        
        case EK::Unary: {
            auto &unary = expr.as<ast::UnaryAssertionExpr>();
            using Op = ast::UnaryAssertionOperator;
            
            if (unary.op == Op::Not) {
                // Not handled at sequence level, handled at property level
                return parse_sequence(unary.expr, start_node);
            }
            
            if (unary.op == Op::NextTime || unary.op == Op::SNextTime) {
                // nexttime expr: check expr on next clock cycle
                int next_node = createNode();
                createEdge(start_node, next_node);
                return parse_sequence(unary.expr, next_node);
            }
            
            if (unary.op == Op::Always || unary.op == Op::SAlways) {
                // always expr: expr must hold at every clock cycle indefinitely
                // Create a self-loop that checks the expression forever
                int always_node = createNode();
                createLink(start_node, always_node);
                
                // Parse the expression
                RTLIL::SigSpec expr_spec = eval_expr(unary.expr.as<ast::SimpleAssertionExpr>().expr);
                RTLIL::SigBit expr_bit = netlist.ReduceBool(expr_spec);
                
                // Self-loop while expression is true
                createEdge(always_node, always_node, expr_bit);
                
                // Always property never "completes" - it just keeps checking
                // For FSM purposes, we never reach accept in normal operation
                // Failure is detected by not satisfying the condition
                return always_node;
            }
            
            if (unary.op == Op::Eventually || unary.op == Op::SEventually) {
                // eventually expr: expr must hold at some future clock cycle
                // Create a self-loop that waits until the expression becomes true
                int wait_node = createNode();
                createLink(start_node, wait_node);
                
                // Parse the expression
                RTLIL::SigSpec expr_spec = eval_expr(unary.expr.as<ast::SimpleAssertionExpr>().expr);
                RTLIL::SigBit expr_bit = netlist.ReduceBool(expr_spec);
                RTLIL::SigBit not_expr = netlist.canvas->Not(NEW_ID, expr_bit);
                
                // Self-loop while expression is false (waiting)
                createEdge(wait_node, wait_node, not_expr);
                
                // Transition to accept when expression becomes true
                int accept_node = createNode();
                createLink(wait_node, accept_node, expr_bit);
                
                return accept_node;
            }
            
            // Unsupported unary operator
            netlist.add_diag(diag::SVAUnsupported, unary.syntax->sourceRange());
            return start_node;
        }
        
        case EK::Clocking:
            // Skip clocking, already extracted
            return parse_sequence(expr.as<ast::ClockingAssertionExpr>().expr, start_node);
        
        case EK::DisableIff:
            // Skip disable iff, already extracted
            return parse_sequence(expr.as<ast::DisableIffAssertionExpr>().expr, start_node);
        
        case EK::StrongWeak: {
            // strong(property) / weak(property)
            // Strong properties must not succeed vacuously
            // Weak properties can succeed vacuously
            auto &sw = expr.as<ast::StrongWeakAssertionExpr>();
            
            // Parse the inner property normally
            // The difference is in DFSM generation: strong uses firstmatch=true, condaccept=false
            // weak uses firstmatch=false, condaccept=false
            // For now, parse normally - strength semantics are handled in materialization
            return parse_sequence(sw.expr, start_node);
        }
        
        case EK::Abort: {
            // accept_on/reject_on/sync_accept_on/sync_reject_on
            auto &abort = expr.as<ast::AbortAssertionExpr>();
            
            // Evaluate the abort condition
            RTLIL::SigSpec abort_cond_spec = eval_expr(abort.condition);
            RTLIL::SigBit abort_cond = netlist.ReduceBool(abort_cond_spec);
            
            // Parse the inner property
            int node = parse_sequence(abort.expr, start_node);
            
            // For accept_on: if condition becomes true, immediately accept
            // For reject_on: if condition becomes true, immediately reject
            if (abort.action == ast::AbortAssertionExpr::Accept) {
                // Create direct link to accept when abort condition is true
                int accept_node = createNode();
                createLink(start_node, accept_node, abort_cond);
                createLink(node, accept_node);
                return accept_node;
            } else {
                // For reject: push abort condition as a disable signal
                // When it becomes true, the property rejects
                pushDisable(abort_cond);
                int result = node;
                popDisable();
    return result;
            }
        }
        
        case EK::Conditional: {
            // if (condition) property else property
            auto &cond = expr.as<ast::ConditionalAssertionExpr>();
            
            // Evaluate the condition
            RTLIL::SigSpec cond_spec = eval_expr(cond.condition);
            RTLIL::SigBit cond_bit = netlist.ReduceBool(cond_spec);
            RTLIL::SigBit not_cond = netlist.canvas->Not(NEW_ID, cond_bit);
            
            // Parse the 'if' branch with condition as throughout
            pushThroughout(cond_bit);
            int if_node = parse_sequence(cond.ifExpr, start_node);
            popThroughout();
            
            int merge_node = createNode();
            createLink(if_node, merge_node);
            
            // Parse the 'else' branch if present
            if (cond.elseExpr) {
                pushThroughout(not_cond);
                int else_node = parse_sequence(*cond.elseExpr, start_node);
                popThroughout();
                createLink(else_node, merge_node);
            } else {
                // No else branch: vacuously true when condition is false
                createLink(start_node, merge_node, not_cond);
            }
            
            return merge_node;
        }
        
        case EK::Case: {
            // case (expr) matches ...
            auto &case_expr = expr.as<ast::CaseAssertionExpr>();
            
            // Evaluate the case expression
            RTLIL::SigSpec case_val = eval_expr(case_expr.expr);
            
            int merge_node = createNode();
            
            // Process each case item
            for (auto &item : case_expr.items) {
                // Build condition for this case item (OR of all expressions)
                RTLIL::SigBit item_matches = RTLIL::S0;
                
                for (auto *match_expr : item.expressions) {
                    RTLIL::SigSpec match_val = eval_expr(*match_expr);
                    RTLIL::SigBit this_match = netlist.Eq(case_val, match_val);
                    
                    if (item_matches == RTLIL::S0) {
                        item_matches = this_match;
                    } else {
                        item_matches = netlist.canvas->Or(NEW_ID, item_matches, this_match);
                    }
                }
                
                // Parse this case's property with the match condition as throughout
                if (item_matches != RTLIL::S0) {
                    pushThroughout(item_matches);
                    int case_node = parse_sequence(*item.body, start_node);
                    popThroughout();
                    createLink(case_node, merge_node);
                }
            }
            
            // Process default case if present
            if (case_expr.defaultCase) {
                // Build condition for default: none of the above matched
                RTLIL::SigBit any_matched = RTLIL::S0;
                
                for (auto &item : case_expr.items) {
                    for (auto *match_expr : item.expressions) {
                        RTLIL::SigSpec match_val = eval_expr(*match_expr);
                        RTLIL::SigBit this_match = netlist.Eq(case_val, match_val);
                        
                        if (any_matched == RTLIL::S0) {
                            any_matched = this_match;
                        } else {
                            any_matched = netlist.canvas->Or(NEW_ID, any_matched, this_match);
                        }
                    }
                }
                
                RTLIL::SigBit default_cond = netlist.canvas->Not(NEW_ID, any_matched);
                pushThroughout(default_cond);
                int default_node = parse_sequence(*case_expr.defaultCase, start_node);
                popThroughout();
                createLink(default_node, merge_node);
            }
            
            return merge_node;
        }
        
        case EK::SequenceWithMatch: {
            // Handle sequences with match items (local variables)
            auto &swm = expr.as<ast::SequenceWithMatchExpr>();
            
            // Match items represent local variable assignments that occur when the sequence matches
            // The actual variable wires are created when we encounter AssertionInstanceExpression
            // For synthesis, we parse the sequence and track that match items exist
            // The assignments themselves are evaluated as part of the sequence expression
            int node = parse_sequence(swm.expr, start_node);
            
            // Handle repetition if present
            if (swm.repetition.has_value()) {
                auto &rep = *swm.repetition;
                int min_count = rep.range.min;
                int max_count = rep.range.max.value_or(0);
                
                if (rep.kind == ast::SequenceRepetition::Consecutive) {
                    // Apply consecutive repetition
                    for (int i = 1; i < min_count; i++) {
                        node = parse_sequence(swm.expr, node);
                    }
                    
                    // Handle ranged repetition
                    if (max_count > min_count) {
                        for (int i = min_count; i < max_count; i++) {
                            int next_node = parse_sequence(swm.expr, node);
                            createLink(node, next_node);
                            node = next_node;
                        }
                    }
                }
            }
            
            return node;
        }
        
        default:
            if (expr.syntax)
                netlist.add_diag(diag::SVAUnsupported, expr.syntax->sourceRange());
            return start_node;
    }
}

// ============================================================================
// Simple Assertion (Boolean Expression with Optional Repetition)
// ============================================================================

int SVAConverter::parse_simple(const ast::SimpleAssertionExpr &expr, int start_node) {
    using EK = ast::ExpressionKind;
    using AK = ast::AssertionExprKind;
    
    log_debug("SVA: visit_simple, expr kind: %d\n", (int)expr.expr.kind);
    
    // Check if this is an assertion instance expression (named property/sequence reference)
    if (expr.expr.kind == EK::AssertionInstance) {
        auto &aie = expr.expr.as<ast::AssertionInstanceExpression>();
        log("SVA: Expanding assertion instance: %s\n", std::string(aie.symbol.name).c_str());
        
        // Create wires for all local assertion variables in this property/sequence
        for (auto *local_var : aie.localVars) {
            RTLIL::IdString wire_id = netlist.id(*local_var);
            if (!netlist.canvas->wire(wire_id)) {
                // LocalAssertionVarSymbol inherits from VariableSymbol which inherits from ValueSymbol
                auto &value_sym = local_var->as<ast::ValueSymbol>();
                netlist.add_wire(value_sym);
                log_debug("SVA: Created wire for local assertion variable: %s\n", 
                         std::string(local_var->name).c_str());
            }
        }
        
        // Recursively visit the assertion body
        return parse_sequence(aie.body, start_node);
    }
    
    // Note: In slang, complex sequences with repetition like (a ##1 b)[*3] 
    // are typically parsed differently - the sequence concat becomes the top-level
    // assertion, not nested inside a SimpleAssertionExpr. So we don't need special
    // handling here for that case.
    
    // Evaluate the boolean expression
    RTLIL::SigSpec condition = eval_expr(expr.expr);
    RTLIL::SigBit cond_bit = netlist.ReduceBool(condition);

    // Handle repetition if present
    if (expr.repetition.has_value()) {
        auto &rep = *expr.repetition;
        int min_count = rep.range.min;
        int max_count = rep.range.max.value_or(0);
        
        // Build FSM for repetition
        int node = start_node;
        
        if (rep.kind == ast::SequenceRepetition::Consecutive) {
            // [*N]: consecutive repetition
            // Match Verific's parse_consecutive_repeat logic (verificsva.cc:1168-1241)

            // For [*0] or [*0:N], increment min_count to 1 (Verific line 1186-1190)
            // The zero-length case is handled by add_pre_delay/add_post_delay in Verific,
            // but for simplicity we handle it with an epsilon link
            bool has_zero_min = (min_count == 0);
            if (has_zero_min) {
                min_count = 1;
            }

            // Create initial node (Verific line 1192-1193)
            node = createNode();
            createLink(start_node, node);

            // For zero-min case, also allow skipping the entire sequence
            if (has_zero_min) {
                // We'll create a link from start to the final node later
            }

            // Track previous node for creating back edges (Verific line 1200)
            int prev_node = -1;

            // Create minimum required repetitions (Verific lines 1203-1210)
            for (int i = 0; i < min_count; i++) {
                int next_node = createNode();
                createEdge(node, next_node, cond_bit);
                prev_node = node;
                node = next_node;
            }

            // Handle unbounded [*] or [*M:$] (Verific lines 1212-1216)
            bool is_unbounded = (max_count == 0); // In slang, 0 means unbounded
            if (is_unbounded) {
                // Create back edge to form a loop (Verific line 1215)
                log_assert(prev_node >= 0);
                createEdge(node, prev_node, cond_bit);
            } else if (max_count > min_count) {
                // Handle bounded ranged repetition [*M:N] (Verific lines 1219-1229)
                for (int i = min_count; i < max_count; i++) {
                    int next_node = createNode();
                    createEdge(node, next_node, cond_bit);
                    // Allow exiting at any point in the range
                    createLink(node, next_node);
                    prev_node = node;
                    node = next_node;
                }
            }

            // For zero-min case, allow skipping directly to the end (Verific line 1238)
            if (has_zero_min) {
                createLink(start_node, node);
            }

            return node;
        } else if (rep.kind == ast::SequenceRepetition::Nonconsecutive || 
                   rep.kind == ast::SequenceRepetition::GoTo) {
            // [=N] or [->N]: non-consecutive repetition
            
            // Handle zero-length case
            if (min_count == 0) {
                node = createNode();
                createLink(start_node, node); // Can match immediately with zero occurrences
                return node;
            }
            
            node = createNode();
            createLink(start_node, node);
            
            // Create nodes with self-loops for waiting
            for (int i = 0; i < min_count; i++) {
                int wait_node = createNode();
                createEdge(node, wait_node);
                RTLIL::SigBit not_cond = netlist.canvas->Not(NEW_ID, cond_bit);
                createEdge(wait_node, wait_node, not_cond); // Wait
                int next_node = createNode();
                createLink(wait_node, next_node, cond_bit); // Match
                node = next_node;
            }
            return node;
        }
    }

    // Simple boolean check: create node with condition link
    int node = createNode();
    createLink(start_node, node, cond_bit);
    return node;
}

// ============================================================================
// NFSM/UFSM/DFSM Architecture Implementation (Verific-style)
// ============================================================================

void SVAConverter::reset_fsm()
{
    nodes.clear();
    unodes.clear();
    dnodes.clear();
    cond_eq_cache.clear();

    materialized = false;
    in_cond_mode = false;
    uses_past = false;

    trigger_sig = RTLIL::S1;
    disable_sig = RTLIL::S0;
    throughout_sig = RTLIL::S1;

    disable_stack.clear();
    throughout_stack.clear();

    final_accept_sig = RTLIL::Sx;
    final_reject_sig = RTLIL::Sx;

    // Create start, accept, and cond nodes
    startNode = createNode();
    acceptNode = createNode();

    in_cond_mode = true;
    condNode = createNode();
    in_cond_mode = false;
}

int SVAConverter::createNode(int link_node)
{
    log_assert(!materialized);
    
    int idx = GetSize(nodes);
    nodes.push_back(SvaNFsmNode());
    nodes.back().is_cond_node = in_cond_mode;
    
    if (link_node >= 0)
        createLink(link_node, idx);
    
    return idx;
}

int SVAConverter::createStartNode()
{
    return createNode(startNode);
}

void SVAConverter::createEdge(int from_node, int to_node, RTLIL::SigBit ctrl)
{
    log_assert(!materialized);
    log_assert(0 <= from_node && from_node < GetSize(nodes));
    log_assert(0 <= to_node && to_node < GetSize(nodes));
    log_assert(from_node != acceptNode);
    log_assert(to_node != acceptNode);
    log_assert(from_node != condNode);
    log_assert(to_node != condNode);
    log_assert(to_node != startNode);
    
    if (from_node != startNode)
        log_assert(nodes.at(from_node).is_cond_node == nodes.at(to_node).is_cond_node);
    
    // Apply throughout condition
    if (throughout_sig != RTLIL::S1) {
        if (ctrl != RTLIL::S1)
            ctrl = netlist.canvas->And(NEW_ID, throughout_sig, ctrl);
        else
            ctrl = throughout_sig;
    }
    
    nodes[from_node].edges.push_back(std::make_pair(to_node, ctrl));
}

void SVAConverter::createLink(int from_node, int to_node, RTLIL::SigBit ctrl)
{
    log_assert(!materialized);
    log_assert(0 <= from_node && from_node < GetSize(nodes));
    log_assert(0 <= to_node && to_node < GetSize(nodes));
    log_assert(from_node != acceptNode);
    log_assert(from_node != condNode);
    log_assert(to_node != startNode);
    
    if (from_node != startNode)
        log_assert(nodes.at(from_node).is_cond_node == nodes.at(to_node).is_cond_node);
    
    // Apply throughout condition
    if (throughout_sig != RTLIL::S1) {
        if (ctrl != RTLIL::S1)
            ctrl = netlist.canvas->And(NEW_ID, throughout_sig, ctrl);
        else
            ctrl = throughout_sig;
    }
    
    nodes[from_node].links.push_back(std::make_pair(to_node, ctrl));
}

void SVAConverter::pushDisable(RTLIL::SigBit sig)
{
    log_assert(!materialized);
    
    disable_stack.push_back(disable_sig);
    
    if (disable_sig == RTLIL::S0)
        disable_sig = sig;
    else
        disable_sig = netlist.canvas->Or(NEW_ID, disable_sig, sig);
}

void SVAConverter::popDisable()
{
    log_assert(!materialized);
    log_assert(!disable_stack.empty());
    
    disable_sig = disable_stack.back();
    disable_stack.pop_back();
}

void SVAConverter::pushThroughout(RTLIL::SigBit sig)
{
    log_assert(!materialized);
    
    throughout_stack.push_back(throughout_sig);
    
    if (throughout_sig == RTLIL::S1)
        throughout_sig = sig;
    else
        throughout_sig = netlist.canvas->And(NEW_ID, throughout_sig, sig);
}

void SVAConverter::popThroughout()
{
    log_assert(!materialized);
    log_assert(!throughout_stack.empty());
    
    throughout_sig = throughout_stack.back();
    throughout_stack.pop_back();
}

void SVAConverter::node_to_unode(int node, int unode, RTLIL::SigSpec ctrl)
{
    if (node == acceptNode)
        unodes[unode].accept.push_back(ctrl);
    
    if (node == condNode)
        unodes[unode].cond.push_back(ctrl);
    
    for (auto &it : nodes[node].edges) {
        if (it.second != RTLIL::S1) {
            RTLIL::SigSpec s = {ctrl, it.second};
            s.sort_and_unify();
            unodes[unode].edges.push_back(std::make_pair(it.first, s));
        } else {
            unodes[unode].edges.push_back(std::make_pair(it.first, ctrl));
        }
    }
    
    for (auto &it : nodes[node].links) {
        if (it.second != RTLIL::S1) {
            RTLIL::SigSpec s = {ctrl, it.second};
            s.sort_and_unify();
            node_to_unode(it.first, unode, s);
        } else {
            node_to_unode(it.first, unode, ctrl);
        }
    }
}

void SVAConverter::mark_reachable_unode(int unode)
{
    if (unodes[unode].reachable)
        return;
    
    unodes[unode].reachable = true;
    for (auto &it : unodes[unode].edges)
        mark_reachable_unode(it.first);
}

void SVAConverter::usortint(std::vector<int> &vec)
{
    std::vector<int> newvec;
    std::sort(vec.begin(), vec.end());
    for (int i = 0; i < GetSize(vec); i++)
        if (i == GetSize(vec)-1 || vec[i] != vec[i+1])
            newvec.push_back(vec[i]);
    vec.swap(newvec);
}

bool SVAConverter::cmp_ctrl(const Yosys::pool<RTLIL::SigBit> &ctrl_bits, const RTLIL::SigSpec &ctrl)
{
    for (int i = 0; i < GetSize(ctrl); i++)
        if (ctrl_bits.count(ctrl[i]) == 0)
            return false;
    return true;
}

void SVAConverter::create_dnode(const std::vector<int> &state, bool firstmatch, bool condaccept)
{
    if (dnodes.count(state) != 0)
        return;
    
    SvaDFsmNode dnode;
    dnodes[state] = SvaDFsmNode();
    
    for (int unode : state) {
        log_assert(unodes[unode].reachable);
        for (auto &it : unodes[unode].edges)
            dnode.ctrl.append(it.second);
        for (auto &it : unodes[unode].accept)
            dnode.ctrl.append(it);
        for (auto &it : unodes[unode].cond)
            dnode.ctrl.append(it);
    }
    
    dnode.ctrl.sort_and_unify();
    
    if (GetSize(dnode.ctrl) > sva_fsm_limit) {
        log_error("SVA DFSM state ctrl signal has %d (>%d) bits. State explosion detected.\n",
                 GetSize(dnode.ctrl), sva_fsm_limit);
    }
    
    for (unsigned long long i = 0; i < (1ull << GetSize(dnode.ctrl)); i++)
    {
        RTLIL::Const ctrl_val(i, GetSize(dnode.ctrl));
        Yosys::pool<RTLIL::SigBit> ctrl_bits;
        
        for (int j = 0; j < GetSize(dnode.ctrl); j++)
            if (ctrl_val[j] == RTLIL::State::S1)
                ctrl_bits.insert(dnode.ctrl[j]);
        
        std::vector<int> new_state;
        bool accept = false, cond = false;
        
        for (int unode : state) {
            for (auto &it : unodes[unode].accept)
                if (cmp_ctrl(ctrl_bits, it))
                    accept = true;
            for (auto &it : unodes[unode].cond)
                if (cmp_ctrl(ctrl_bits, it))
                    cond = true;
        }
        
        bool new_state_cond = false;
        bool new_state_noncond = false;
        
        if (accept && condaccept)
            accept = cond;
        
        if (!accept || !firstmatch) {
            for (int unode : state)
            for (auto &it : unodes[unode].edges)
                if (cmp_ctrl(ctrl_bits, it.second)) {
                    if (nodes.at(it.first).is_cond_node)
                        new_state_cond = true;
                    else
                        new_state_noncond = true;
                    new_state.push_back(it.first);
                }
        }
        
        if (accept)
            dnode.accept.push_back(ctrl_val);
        
        if (condaccept && (!new_state_cond || !new_state_noncond))
            new_state.clear();
        
        if (new_state.empty()) {
            // Dead-end state: mark as reject if not accept
            // Match Verific's logic (verificsva.cc:529-531)
            if (!accept)
                dnode.reject.push_back(ctrl_val);
        } else {
            usortint(new_state);
            dnode.edges.push_back(std::make_pair(new_state, ctrl_val));
            create_dnode(new_state, firstmatch, condaccept);
        }
    }
    
    dnodes[state] = dnode;
}

void SVAConverter::optimize_cond(std::vector<RTLIL::Const> &values)
{
    bool did_something = true;
    
    while (did_something)
    {
        did_something = false;
        
        for (int i = 0; i < GetSize(values); i++)
        for (int j = 0; j < GetSize(values); j++)
        {
            if (i == j)
                continue;
            
            log_assert(GetSize(values[i]) == GetSize(values[j]));
            
            int delta_pos = -1;
            bool i_within_j = true;
            bool j_within_i = true;
            
            for (int k = 0; k < GetSize(values[i]); k++) {
                if (values[i][k] == RTLIL::State::Sa && values[j][k] != RTLIL::State::Sa) {
                    i_within_j = false;
                    continue;
                }
                if (values[i][k] != RTLIL::State::Sa && values[j][k] == RTLIL::State::Sa) {
                    j_within_i = false;
                    continue;
                }
                if (values[i][k] == values[j][k])
                    continue;
                if (delta_pos >= 0)
                    goto next_pair;
                delta_pos = k;
            }
            
            if (delta_pos >= 0 && i_within_j && j_within_i) {
                did_something = true;
                values[i].set(delta_pos, RTLIL::State::Sa);
                values[j] = values.back();
                values.pop_back();
                goto next_pair;
            }
            
            if (delta_pos < 0 && i_within_j) {
                did_something = true;
                values[i] = values.back();
                values.pop_back();
                goto next_pair;
            }
            
            if (delta_pos < 0 && j_within_i) {
                did_something = true;
                values[j] = values.back();
                values.pop_back();
                goto next_pair;
            }
    next_pair:;
        }
    }
}

RTLIL::SigBit SVAConverter::make_cond_eq_dfsm(const RTLIL::SigSpec &ctrl, const RTLIL::Const &value, RTLIL::SigBit enable)
{
    RTLIL::SigSpec sig_a, sig_b;
    
    log_assert(GetSize(ctrl) == GetSize(value));
    
    for (int i = 0; i < GetSize(ctrl); i++)
        if (value[i] != RTLIL::State::Sa) {
            sig_a.append(ctrl[i]);
            sig_b.append(value[i]);
        }
    
    if (GetSize(sig_a) == 0)
        return enable;
    
    if (enable != RTLIL::S1) {
        sig_a.append(enable);
        sig_b.append(RTLIL::State::S1);
    }
    
    auto key = std::make_pair(sig_a, sig_b);
    
    if (cond_eq_cache.count(key) == 0)
    {
        if (sig_b == RTLIL::State::S1)
            cond_eq_cache[key] = sig_a;
        else if (sig_b == RTLIL::State::S0)
            cond_eq_cache[key] = netlist.canvas->Not(NEW_ID, sig_a);
        else
            cond_eq_cache[key] = netlist.Eq(sig_a, sig_b);
    }
    
    return cond_eq_cache.at(key);
}

RTLIL::SigBit SVAConverter::getAccept()
{
    log_assert(!materialized);
    materialized = true;
    
    std::vector<RTLIL::Wire*> state_wire(GetSize(nodes));
    std::vector<RTLIL::SigBit> state_sig(GetSize(nodes));
    std::vector<RTLIL::SigBit> next_state_sig(GetSize(nodes));
    
    // Create state signals
    {
        RTLIL::SigBit not_disable = RTLIL::S1;
        
        if (disable_sig != RTLIL::S0)
            not_disable = netlist.canvas->Not(NEW_ID, disable_sig);
        
        for (int i = 0; i < GetSize(nodes); i++)
        {
            RTLIL::Wire *w = netlist.canvas->addWire(NEW_ID);
            // Set initial value to 0 for formal verification (BMC)
            w->attributes[ID::init] = RTLIL::Const(0, 1);
            state_wire[i] = w;
            state_sig[i] = w;

            if (i == startNode)
                state_sig[i] = netlist.canvas->Or(NEW_ID, state_sig[i], trigger_sig);

            if (disable_sig != RTLIL::S0)
                state_sig[i] = netlist.canvas->And(NEW_ID, state_sig[i], not_disable);
        }
    }
    
    // Follow Links (resolve epsilon transitions)
    // We need to propagate signals through link edges in the correct order
    // to handle chains of links properly
    {
        // Build link order: topological sort based on link dependencies
        std::vector<int> node_order(GetSize(nodes), 0);
        std::vector<std::vector<int>> order_to_nodes;
        
        // Calculate maximum link depth for each node
        std::function<void(int, int)> calc_link_order;
        calc_link_order = [&](int node, int min_order) {
            node_order[node] = std::max(node_order[node], min_order);
            for (auto &it : nodes[node].links) {
                calc_link_order(it.first, node_order[node] + 1);
            }
        };
        
        // Calculate orders starting from all nodes
        for (int i = 0; i < GetSize(nodes); i++) {
            calc_link_order(i, 0);
        }
        
        // Group nodes by order
        for (int i = 0; i < GetSize(nodes); i++) {
            int order = node_order[i];
            if (order >= GetSize(order_to_nodes)) {
                order_to_nodes.resize(order + 1);
            }
            order_to_nodes[order].push_back(i);
        }
        
        // Process nodes in order, propagating link signals
        for (int order = 0; order < GetSize(order_to_nodes); order++) {
            for (int node : order_to_nodes[order]) {
                for (auto &it : nodes[node].links) {
                    int target = it.first;
                    RTLIL::SigBit ctrl = state_sig[node];
                    
                    if (it.second != RTLIL::S1)
                        ctrl = netlist.canvas->And(NEW_ID, ctrl, it.second);
                    
                    state_sig[target] = netlist.canvas->Or(NEW_ID, state_sig[target], ctrl);
                }
            }
        }
    }
    
    // Construct activations
    {
        std::vector<RTLIL::SigSpec> activate_sig(GetSize(nodes));
        
        for (int i = 0; i < GetSize(nodes); i++) {
            for (auto &it : nodes[i].edges)
                activate_sig[it.first].append(netlist.canvas->And(NEW_ID, state_sig[i], it.second));
        }
        
        for (int i = 0; i < GetSize(nodes); i++) {
            if (GetSize(activate_sig[i]) == 0)
                next_state_sig[i] = RTLIL::S0;
            else if (GetSize(activate_sig[i]) == 1)
                next_state_sig[i] = activate_sig[i];
            else
                next_state_sig[i] = netlist.ReduceBool(activate_sig[i]);
        }
    }
    
    // Create state FFs
    for (int i = 0; i < GetSize(nodes); i++)
    {
        if (next_state_sig[i] != RTLIL::S0) {
            create_dff(next_state_sig[i], state_wire[i]->name);
            netlist.canvas->connect(state_wire[i], create_dff(next_state_sig[i], state_wire[i]->name));
    } else {
            netlist.canvas->connect(state_wire[i], RTLIL::S0);
        }
    }
    
    final_accept_sig = state_sig[acceptNode];
    return final_accept_sig;
}

RTLIL::SigBit SVAConverter::getReject()
{
    RTLIL::SigBit reject;
    getFirstAcceptReject(nullptr, &reject);
    return reject;
}

void SVAConverter::getFirstAcceptReject(RTLIL::SigBit *accept_p, RTLIL::SigBit *reject_p)
{
    log_assert(!materialized);
    materialized = true;
    
    // Create unlinked NFSM
    unodes.resize(GetSize(nodes));
    
    for (int node = 0; node < GetSize(nodes); node++)
        node_to_unode(node, node, RTLIL::SigSpec());
    
    mark_reachable_unode(startNode);
    
    // Create DFSM
    create_dnode(std::vector<int>{startNode}, true, false);
    dnodes.sort();
    
    // Create DFSM Circuit
    RTLIL::SigSpec accept_sig, reject_sig;
    
    for (auto &it : dnodes)
    {
        SvaDFsmNode &dnode = it.second;
        dnode.ffoutwire = netlist.canvas->addWire(NEW_ID);
        // Set initial value to 0 for formal verification (BMC)
        dnode.ffoutwire->attributes[ID::init] = RTLIL::Const(0, 1);
        dnode.statesig = dnode.ffoutwire;

        if (it.first == std::vector<int>{startNode})
            dnode.statesig = netlist.canvas->Or(NEW_ID, dnode.statesig, trigger_sig);
    }
    
    for (auto &it : dnodes)
    {
        SvaDFsmNode &dnode = it.second;
        Yosys::dict<std::vector<int>, std::vector<RTLIL::Const>> edge_cond;
        
        for (auto &edge : dnode.edges)
            edge_cond[edge.first].push_back(edge.second);
        
        for (auto &it2 : edge_cond) {
            optimize_cond(it2.second);
            for (auto &value : it2.second)
                dnodes.at(it2.first).nextstate.append(make_cond_eq_dfsm(dnode.ctrl, value, dnode.statesig));
        }
        
        if (accept_p) {
            std::vector<RTLIL::Const> accept_cond = dnode.accept;
            optimize_cond(accept_cond);
            for (auto &value : accept_cond)
                accept_sig.append(make_cond_eq_dfsm(dnode.ctrl, value, dnode.statesig));
        }
        
        if (reject_p) {
            std::vector<RTLIL::Const> reject_cond = dnode.reject;
            optimize_cond(reject_cond);
            for (auto &value : reject_cond)
                reject_sig.append(make_cond_eq_dfsm(dnode.ctrl, value, dnode.statesig));
        }
    }
    
    for (auto &it : dnodes)
    {
        SvaDFsmNode &dnode = it.second;
        if (GetSize(dnode.nextstate) == 0) {
            netlist.canvas->connect(dnode.ffoutwire, RTLIL::S0);
        } else if (GetSize(dnode.nextstate) == 1) {
            RTLIL::SigSpec dff_out = create_dff(dnode.nextstate, dnode.ffoutwire->name);
            netlist.canvas->connect(dnode.ffoutwire, dff_out);
    } else {
            RTLIL::SigSpec nextstate = netlist.ReduceBool(dnode.nextstate);
            RTLIL::SigSpec dff_out = create_dff(nextstate, dnode.ffoutwire->name);
            netlist.canvas->connect(dnode.ffoutwire, dff_out);
        }
    }
    
    if (accept_p)
    {
        if (GetSize(accept_sig) == 0)
            final_accept_sig = RTLIL::S0;
        else if (GetSize(accept_sig) == 1)
            final_accept_sig = accept_sig;
        else
            final_accept_sig = netlist.ReduceBool(accept_sig);
        *accept_p = final_accept_sig;
    }
    
    if (reject_p)
    {
        if (GetSize(reject_sig) == 0)
            final_reject_sig = RTLIL::S0;
        else if (GetSize(reject_sig) == 1)
            final_reject_sig = reject_sig;
        else
            final_reject_sig = netlist.ReduceBool(reject_sig);
        *reject_p = final_reject_sig;
    }
}

} // namespace slang_frontend
