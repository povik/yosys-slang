// Test: Strong and Weak Sequence Operators
// Category: Advanced sequence semantics
// Expected: Should pass after implementation

module strong_weak_test(
    input logic clk,
    input logic req,
    input logic ack,
    input logic valid,
    input logic ready
);

    // Define sequences
    sequence s_req_to_ack;
        req ##[1:5] ack;
    endsequence

    sequence s_valid_ready;
        valid ##1 ready;
    endsequence

    // Test 1: Strong operator on sequence
    property p_strong;
        @(posedge clk) strong(s_req_to_ack);
    endproperty
    assert property (p_strong);

    // Test 2: Weak operator on sequence
    property p_weak;
        @(posedge clk) weak(s_req_to_ack);
    endproperty
    assert property (p_weak);

    // Test 3: Strong with inline sequence
    property p_strong_inline;
        @(posedge clk) strong(req ##1 ack ##1 valid);
    endproperty
    assert property (p_strong_inline);

    // Test 4: Weak with inline sequence
    property p_weak_inline;
        @(posedge clk) weak(valid ##[1:3] ready);
    endproperty
    assert property (p_weak_inline);

    // Test 5: Strong in implication
    property p_strong_impl;
        @(posedge clk) req |-> strong(##[1:3] ack);
    endproperty
    assert property (p_strong_impl);

    // Test 6: Weak with repetition
    property p_weak_rep;
        @(posedge clk) weak(valid[*2] ##1 ready);
    endproperty
    assert property (p_weak_rep);

endmodule
