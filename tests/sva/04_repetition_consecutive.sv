// Test: Consecutive Repetition [*n]
// Category: Sequence repetition operators
// Expected: Should fail - consecutive repetition not supported

module consecutive_repetition_test(
    input logic clk,
    input logic req,
    input logic busy,
    input logic valid,
    input logic ready,
    input logic [3:0] state
);

    // Test 1: Fixed repetition [*3]
    property p_fixed_rep;
        @(posedge clk) req ##1 busy[*3];  // busy high for exactly 3 cycles
    endproperty
    assert property (p_fixed_rep);

    // Test 2: Range repetition [*2:4]
    property p_range_rep;
        @(posedge clk) req ##1 busy[*2:4];  // busy high for 2-4 cycles
    endproperty
    assert property (p_range_rep);

    // Test 3: Zero or more repetition [*0:$]
    property p_zero_or_more;
        @(posedge clk) valid[*0:$] ##1 ready;
    endproperty
    assert property (p_zero_or_more);

    // Test 4: One or more repetition [*1:$]
    property p_one_or_more;
        @(posedge clk) busy[*1:$] ##1 !busy;
    endproperty
    assert property (p_one_or_more);

    // Test 5: Unbounded repetition [*]
    property p_unbounded;
        @(posedge clk) req |-> busy[*] ##1 ready;
    endproperty
    assert property (p_unbounded);

    // Test 6: Repetition with condition
    property p_rep_condition;
        @(posedge clk) (state == 4'd3)[*4];  // stay in state 3 for 4 cycles
    endproperty
    assert property (p_rep_condition);

    // Test 7: Multiple repetitions in sequence
    property p_multiple_reps;
        @(posedge clk) req[*2] ##1 busy[*3] ##1 ready;
    endproperty
    assert property (p_multiple_reps);

    // Test 8: Nested repetitions
    property p_nested_reps;
        @(posedge clk) (valid ##1 ready)[*3];
    endproperty
    assert property (p_nested_reps);

endmodule
