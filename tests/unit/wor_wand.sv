module top(input logic [3:0] a, input logic [3:0] b);
    wor [3:0] wor_net;
    wand [3:0] wand_net;
    wire [1:0] other_wire;

    assign {wor_net[3:2], other_wire[1:0]} = a;
    assign wor_net = b;
    assign wand_net[1:0] = other_wire;
    assign wand_net = b;
    assign {wor_net[3], wand_net[3]} = 2;

    wire [3:0] ref_wor = {a[3:2], 2'b00} | b | 4'b1000;
    wire [3:0] ref_wand = {2'b11, a[1:0]} & b & 4'b0111;

    always_comb begin
        if (^a !== 1'bx && ^b !== 1'bx) begin
            assert(wor_net === ref_wor);
            assert(wand_net === ref_wand);
        end
    end
endmodule
