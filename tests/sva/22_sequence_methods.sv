// Test: Sequence Methods (.triggered, .matched)
// Category: Sequence status queries within sequences
// Expected: Should pass after implementation

module sequence_methods_test(
    input logic clk,
    input logic req,
    input logic ack,
    input logic valid,
    input logic ready,
    input logic start
);

    // Base sequence
    sequence s_req_ack;
        @(posedge clk) $rose(req) ##1 ack ##1 valid;
    endsequence

    sequence s_trigger(a, b);
        @(posedge clk) $rose(a) ##1 b;
    endsequence

    // Test 1: Using .triggered in sequence
    sequence s_with_triggered;
        @(posedge clk) s_req_ack.triggered ##1 ready;
    endsequence
    assert property (s_with_triggered);

    // Test 2: Using .matched in sequence  
    sequence s_with_matched;
        @(posedge clk) start ##1 s_req_ack.matched [->1] ##1 ready;
    endsequence
    assert property (s_with_matched);

    // Test 3: Parameterized sequence with .triggered
    sequence s_param_triggered;
        @(posedge clk) s_trigger(req, ack).triggered ##1 valid;
    endsequence
    assert property (s_param_triggered);

    // Test 4: Multiple .triggered in same sequence
    sequence s_multi_trigger;
        @(posedge clk) s_req_ack.triggered ##1 s_trigger(valid, ready).triggered;
    endsequence
    assert property (s_multi_trigger);

endmodule

