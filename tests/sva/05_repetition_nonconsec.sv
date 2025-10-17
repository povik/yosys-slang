// Test: Non-Consecutive Repetition [=n] and Goto Repetition [->n]
// Category: Advanced sequence repetition
// Expected: Should fail - non-consecutive and goto repetition not supported

module nonconsec_goto_repetition_test(
    input logic clk,
    input logic start,
    input logic req,
    input logic grant,
    input logic ack,
    input logic done,
    input logic event_signal
);

    // Test 1: Non-consecutive repetition [=3]
    property p_nonconsec_fixed;
        @(posedge clk) start ##1 grant[=3] ##1 done;
        // grant occurs 3 times (not necessarily consecutive)
    endproperty
    assert property (p_nonconsec_fixed);

    // Test 2: Non-consecutive range [=2:5]
    property p_nonconsec_range;
        @(posedge clk) start |-> req[=2:5];
        // req occurs 2-5 times
    endproperty
    assert property (p_nonconsec_range);

    // Test 3: Goto repetition [->3]
    property p_goto_fixed;
        @(posedge clk) start ##1 ack[->3] ##2 done;
        // 3rd occurrence of ack must be exactly 2 cycles before done
    endproperty
    assert property (p_goto_fixed);

    // Test 4: Goto with range [->2:4]
    property p_goto_range;
        @(posedge clk) start |-> event_signal[->2:4] ##1 done;
    endproperty
    assert property (p_goto_range);

    // Test 5: Mixed repetitions
    property p_mixed;
        @(posedge clk) start ##1 req[*2] ##1 grant[=3] ##1 ack[->1];
    endproperty
    assert property (p_mixed);

    // Test 6: Non-consecutive in implication
    property p_nonconsec_impl;
        @(posedge clk) start |-> req[=3] |=> done;
    endproperty
    assert property (p_nonconsec_impl);

endmodule
