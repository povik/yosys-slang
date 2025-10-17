// Test: SVA System Functions
// Category: Temporal system functions
// Expected: Should fail - SVA system functions not supported

module sva_functions_test(
    input logic clk,
    input logic reset_n,
    input logic valid,
    input logic [7:0] data,
    input logic [7:0] addr,
    input logic req,
    input logic busy,
    input logic enable
);

    // Test 1: $rose - detects 0->1 transition
    property p_rose;
        @(posedge clk) $rose(valid) |-> ##1 $stable(data);
    endproperty
    assert property (p_rose);

    // Test 2: $fell - detects 1->0 transition
    property p_fell;
        @(posedge clk) $fell(busy) |-> ($past(req) == 1'b1);
    endproperty
    assert property (p_fell);

    // Test 3: $stable - value unchanged
    property p_stable;
        @(posedge clk) enable |-> $stable(addr);
    endproperty
    assert property (p_stable);

    // Test 4: $past - previous value
    property p_past_1;
        @(posedge clk) valid |-> (data == $past(data) + 1);
    endproperty
    assert property (p_past_1);

    // Test 5: $past with depth
    property p_past_depth;
        @(posedge clk) valid |-> (data > $past(data, 2));
    endproperty
    assert property (p_past_depth);

    // Test 6: $changed - value changed
    property p_changed;
        @(posedge clk) $changed(addr) |-> valid;
    endproperty
    assert property (p_changed);

    // Test 7: Combined SVA functions
    property p_combined;
        @(posedge clk) $rose(req) |-> ##1 ($stable(data) && !$fell(enable));
    endproperty
    assert property (p_combined);

    // Test 8: $past with gating expression
    property p_past_gated;
        @(posedge clk) valid |-> $past(data, 1, enable);
    endproperty
    assert property (p_past_gated);

    // Test 9: $onehot - exactly one bit set
    property p_onehot;
        @(posedge clk) valid |-> $onehot(data);
    endproperty
    assert property (p_onehot);

    // Test 10: $onehot0 - zero or one bit set
    property p_onehot0;
        @(posedge clk) $onehot0(addr);
    endproperty
    assert property (p_onehot0);

    // Test 11: $isunknown - check for X or Z
    property p_isunknown;
        @(posedge clk) reset_n |-> !$isunknown(data);
    endproperty
    assert property (p_isunknown);

    // Test 12: $countones - count set bits
    property p_countones;
        @(posedge clk) valid |-> ($countones(data) <= 4);
    endproperty
    assert property (p_countones);

endmodule
