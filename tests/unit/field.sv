module test_field_assign #(
    parameter integer FIELD0_WIDTH = 4,
    parameter integer FIELD1_WIDTH = 4
) (
    input logic [FIELD0_WIDTH-1:0] in0,
    input logic [FIELD1_WIDTH-1:0] in1
);
    typedef struct packed {
        logic [FIELD0_WIDTH-1:0] field0;
        logic [FIELD1_WIDTH-1:0] field1;
    } test_t;

    test_t struct_signal;
    assign struct_signal[FIELD0_WIDTH+FIELD1_WIDTH-1:FIELD1_WIDTH] = in0;
    assign struct_signal[FIELD1_WIDTH-1:0] = in1;

    always_comb begin
        assert(struct_signal.field0 === in0);
        assert(struct_signal.field1 === in1);
    end
endmodule
