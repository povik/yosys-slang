// Test: Temporal Delay Operators (##)
// Category: Sequence operators - cycle delays
// Expected: Should fail - temporal delay operators not supported

module temporal_delay_test(
    input logic clk,
    input logic req,
    input logic ack,
    input logic grant
);

    // Test 1: Fixed delay - ##1
    property p_fixed_delay_1;
        @(posedge clk) req ##1 ack;  // ack must be true 1 cycle after req
    endproperty
    assert property (p_fixed_delay_1);

    // Test 2: Fixed delay - ##2
    property p_fixed_delay_2;
        @(posedge clk) req ##2 ack;  // ack must be true 2 cycles after req
    endproperty
    assert property (p_fixed_delay_2);

    // Test 3: Range delay - ##[2:5]
    property p_range_delay;
        @(posedge clk) req ##[2:5] ack;  // ack within 2-5 cycles after req
    endproperty
    assert property (p_range_delay);

    // Test 4: Unbounded delay - ##[1:$]
    property p_unbounded_delay;
        @(posedge clk) req ##[1:$] ack;  // ack eventually after req
    endproperty
    assert property (p_unbounded_delay);

    // Test 5: Zero delay - ##0
    property p_zero_delay;
        @(posedge clk) req ##0 ack;  // same cycle
    endproperty
    assert property (p_zero_delay);

    // Test 6: Chained delays
    property p_chained_delays;
        @(posedge clk) req ##1 grant ##2 ack;  // multi-step handshake
    endproperty
    assert property (p_chained_delays);

endmodule
