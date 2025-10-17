// Test: Conditional Properties (if/else)
// Category: Runtime property selection
// Expected: Should pass after implementation

module conditional_property_test(
    input logic clk,
    input logic mode,
    input logic [1:0] state,
    input logic req,
    input logic ack,
    input logic valid,
    input logic ready
);

    // Test 1: Simple if property
    property p_if;
        @(posedge clk) if (mode) (req |-> ack) else (valid |-> ready);
    endproperty
    assert property (p_if);

    // Test 2: If without else
    property p_if_no_else;
        @(posedge clk) if (mode) (req |-> ##1 ack);
    endproperty
    assert property (p_if_no_else);

    // Test 3: Nested conditional
    property p_nested;
        @(posedge clk) if (state == 2'b00)
            (req |-> ack)
        else if (state == 2'b01)
            (valid |-> ready)
        else
            (req |-> valid);
    endproperty
    assert property (p_nested);

    // Test 4: Conditional with complex properties
    property p_complex;
        @(posedge clk) if (mode)
            (req ##1 valid ##1 ready)
        else
            (req |=> ##[1:3] ack);
    endproperty
    assert property (p_complex);

endmodule

