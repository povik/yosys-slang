// Test: Sequence Declarations
// Category: Named sequences and reusability
// Expected: Should fail - sequence declarations not supported

module sequence_test(
    input logic clk,
    input logic reset_n,
    input logic start,
    input logic req,
    input logic ack,
    input logic done,
    input logic valid,
    input logic ready
);

    // Test 1: Basic sequence declaration
    sequence s_req_ack;
        @(posedge clk) req ##1 ack;
    endsequence

    // Test 2: Sequence with range delay
    sequence s_handshake;
        @(posedge clk) req ##[1:3] ack ##1 done;
    endsequence

    // Test 3: Sequence with $rose
    sequence s_start_pulse;
        @(posedge clk) $rose(start);
    endsequence

    // Test 4: Using sequence in assertion
    assert property (s_req_ack);

    // Test 5: Using sequence in property
    property p_using_seq;
        @(posedge clk) s_handshake;
    endproperty
    assert property (p_using_seq);

    // Test 6: Sequence composition
    sequence s_valid_ready;
        @(posedge clk) valid ##1 ready;
    endsequence

    property p_composed;
        @(posedge clk) s_start_pulse |-> s_valid_ready;
    endproperty
    assert property (p_composed);

    // Test 7: Parameterized sequence (if supported)
    sequence s_delay(delay);
        @(posedge clk) req ##delay ack;
    endsequence

    assert property (@(posedge clk) s_delay(2));

    // Test 8: Sequence with throughout
    sequence s_enable_held;
        @(posedge clk) (valid throughout (req ##[1:5] ack));
    endsequence
    assert property (s_enable_held);

endmodule
