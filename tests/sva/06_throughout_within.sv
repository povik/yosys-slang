// Test: Throughout and Within Operators
// Category: Sequence operators for condition checking
// Expected: Should fail - throughout and within operators not supported

module throughout_within_test(
    input logic clk,
    input logic enable,
    input logic req,
    input logic ack,
    input logic busy,
    input logic start,
    input logic end_sig,
    input logic valid
);

    // Test 1: Throughout operator - basic
    property p_throughout_basic;
        @(posedge clk) (enable throughout (req ##[1:5] ack));
        // enable must stay high throughout the req-ack sequence
    endproperty
    assert property (p_throughout_basic);

    // Test 2: Throughout with repetition
    property p_throughout_rep;
        @(posedge clk) (valid throughout (busy[*3]));
        // valid must stay high while busy is high for 3 cycles
    endproperty
    assert property (p_throughout_rep);

    // Test 3: Throughout in implication
    property p_throughout_impl;
        @(posedge clk) start |-> (enable throughout (req ##1 ack));
    endproperty
    assert property (p_throughout_impl);

    // Test 4: Within operator - basic
    property p_within_basic;
        @(posedge clk) (req ##1 ack) within (start ##[0:10] end_sig);
        // req-ack sequence must occur within start-end window
    endproperty
    assert property (p_within_basic);

    // Test 5: Within with longer sequences
    property p_within_complex;
        @(posedge clk) (req ##1 busy ##1 ack) within (start ##[0:20] end_sig);
    endproperty
    assert property (p_within_complex);

    // Test 6: Nested throughout
    property p_nested_throughout;
        @(posedge clk) (enable throughout (valid throughout (req ##1 ack)));
    endproperty
    assert property (p_nested_throughout);

endmodule
