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

module m_assert_conc(input logic clk_i, input logic x);
        named: assert property(@(posedge clk_i) x);
endmodule

module m_assume_conc(input logic clk_i, input logic x);
        named: assume property(@(posedge clk_i) x);
endmodule

module m_cover_conc(input logic clk_i, input logic x);
        named: cover property(@(posedge clk_i) x);
endmodule

module m_assert_implies(input logic clk_i, input logic x, input logic y);
        named: assert property(@(posedge clk_i) x |-> y);
endmodule

module m_assume_implies(input logic clk_i, input logic x, input logic y);
        named: assume property(@(posedge clk_i) y |-> x);
endmodule

module m_assert_seq_1(input logic clk_i, input logic x, input logic y);
        named: assert property(@(posedge clk_i) x ##1 y);
endmodule

module m_assert_seq_2(input logic clk_i, input logic x, input logic y);
        named: assert property(@(posedge clk_i) x ##[1:2] y);
endmodule

module m_assert_seq_3(input logic clk_i, input logic x, input logic y, input logic z);
        named: assert property(@(posedge clk_i) x ##[1:2] y |=> (z ##[1:2] x) or (##1 y));
endmodule

module m_assert_seq_4(input logic clk_i, input logic x, input logic y, input logic z);
        named: assert property(@(posedge clk_i) ((z ##[1:2] x) and (##1 y)) ##1 x);
endmodule

module m_assert_seq_5(input logic clk_i, input logic x);
        named: assert property(@(posedge clk_i) ##3 x);
endmodule

module m_assert_seq_6(input logic clk_i, input logic x, input logic y, input logic z);
        named: assert property(@(posedge clk_i) x |=> y or (##1 z));
endmodule

module m_assert_seq_7(input logic clk_i, input logic x, input logic y, input logic z);
        named: assert property(@(posedge clk_i) disable iff (~z)  x |-> ##3 ~y);
endmodule
