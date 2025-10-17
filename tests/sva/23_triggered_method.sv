// Test: Sequence .triggered Method (used within sequences)
// Category: Sequence evaluation tracking
// Expected: Should pass after implementation

module triggered_method_test(
    input logic clk,
    input logic req,
    input logic ack,
    input logic valid,
    input logic ready
);

    // Sequences that can be triggered
    sequence s_req_ack;
        @(posedge clk) req ##[1:3] ack;
    endsequence

    sequence s_valid;
        @(posedge clk) valid ##1 ack;
    endsequence

    // Test 1: Using .triggered in a sequence
    sequence s_use_triggered;
        @(posedge clk) s_req_ack.triggered ##1 ready;
    endsequence
    assert property (s_use_triggered);

    // Test 2: Chaining triggered sequences
    sequence s_chain;
        @(posedge clk) s_req_ack.triggered ##1 s_valid.triggered;
    endsequence
    assert property (s_chain);

    // Test 3: Triggered as part of boolean expression
    sequence s_bool_trigger;
        @(posedge clk) s_req_ack.triggered ##1 (valid && ready);
    endsequence
    assert property (s_bool_trigger);

endmodule
