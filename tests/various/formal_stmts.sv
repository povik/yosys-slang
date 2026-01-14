module m_assert(input logic x);
	always_comb assert(x);
endmodule

module m_assume(input logic x);
	always_comb assume(x);
endmodule

module m_cover(input logic x);
	always_comb cover(x);
endmodule

module m_labeled_assertions(input logic x, y, z);
	always_comb my_assert: assert(x);
	always_comb my_assume: assume(y);
	always_comb my_cover: begin
		begin
			cover(z);
		end
	end
endmodule

module m_past (
    input clk,
    input rst_n,
    input [7:0] index
);
    reg [7:0] regs[7:0];
    reg [7:0] past1_reg;
    reg [7:0] past2_reg;
    always @(posedge clk) begin
        past1_reg <= regs[index];
        past2_reg <= past1_reg;
        if (rst_n) begin
            assert ($past(regs[index]) == past1_reg);
            assert ($past(regs[index], 1) == past1_reg);
            if ($past(rst_n))
                assert ($past(regs[index], 2) == past2_reg);
        end
    end
endmodule
