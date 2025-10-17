// Test: Zero-Length Sequences
// Category: Edge cases in sequence matching
// Expected: Should pass after implementation

module zero_length_test(
    input logic clk,
    input logic a, b, c,
    input logic req,
    input logic ack
);

    // Test 1: Zero repetition
    property p_zero_rep;
        @(posedge clk) a ##1 b[*0] ##1 c;
    endproperty
    assert property (p_zero_rep);

    // Test 2: Zero or more repetition
    property p_zero_or_more;
        @(posedge clk) a ##1 b[*0:2] ##1 c;
    endproperty
    assert property (p_zero_or_more);

    // Test 3: Empty sequence in implication
    property p_empty_impl;
        @(posedge clk) req ##1 ack[*0] |-> c;
    endproperty
    assert property (p_empty_impl);

    // Test 4: Zero delay
    property p_zero_delay;
        @(posedge clk) a ##0 b;
    endproperty
    assert property (p_zero_delay);

endmodule

