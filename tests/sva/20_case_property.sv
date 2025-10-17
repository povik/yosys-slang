// Test: Case Property Selection
// Category: Multi-way property selection
// Expected: Should pass after implementation

module case_property_test(
    input logic clk,
    input logic [2:0] opcode,
    input logic [1:0] state,
    input logic req,
    input logic ack,
    input logic valid,
    input logic ready,
    input logic error
);

    // Test 1: Case with multiple branches
    property p_case;
        @(posedge clk) case (opcode)
            3'b000: (req |-> ack);
            3'b001: (valid |-> ready);
            3'b010: (req |=> ##1 ack);
            default: (1);
        endcase
    endproperty
    assert property (p_case);

    // Test 2: Case without default
    property p_case_no_default;
        @(posedge clk) case (state)
            2'b00: (req ##1 ack);
            2'b01: (valid ##1 ready);
            2'b10: (req |-> valid);
        endcase
    endproperty
    assert property (p_case_no_default);

    // Test 3: Case with complex properties
    property p_case_complex;
        @(posedge clk) case (opcode)
            3'b000: (req ##[1:3] ack);
            3'b001: (valid throughout (req ##[1:5] ack));
            3'b010: (req |-> s_eventually[1:10] ready);
            default: (!error);
        endcase
    endproperty
    assert property (p_case_complex);

endmodule

