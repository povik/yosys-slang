// Test: Disable iff Clause
// Category: Conditional assertion disabling
// Expected: Should fail - disable iff not supported

module disable_iff_test(
    input logic clk,
    input logic rst,
    input logic reset_n,
    input logic req,
    input logic ack,
    input logic valid,
    input logic error,
    input logic [7:0] data
);

    // Test 1: Basic disable iff with reset
    property p_disable_reset;
        @(posedge clk) disable iff (rst)
            req |-> ##[1:3] ack;
    endproperty
    assert property (p_disable_reset);

    // Test 2: Disable iff with active-low reset
    property p_disable_resetn;
        @(posedge clk) disable iff (!reset_n)
            valid |-> !error;
    endproperty
    assert property (p_disable_resetn);

    // Test 3: Disable iff with complex condition
    property p_disable_complex;
        @(posedge clk) disable iff (rst || error)
            req |=> ack;
    endproperty
    assert property (p_disable_complex);

    // Test 4: Disable iff in assume
    property p_assume_disable;
        @(posedge clk) disable iff (rst)
            valid |-> (data != 8'h00);
    endproperty
    assume property (p_assume_disable);

    // Test 5: Disable iff in cover
    property p_cover_disable;
        @(posedge clk) disable iff (!reset_n)
            req ##1 ack;
    endproperty
    cover property (p_cover_disable);

    // Test 6: Multiple properties with same disable condition
    property p_multi_disable_1;
        @(posedge clk) disable iff (rst)
            req |-> valid;
    endproperty

    property p_multi_disable_2;
        @(posedge clk) disable iff (rst)
            valid |-> !error;
    endproperty

    assert property (p_multi_disable_1);
    assert property (p_multi_disable_2);

endmodule
