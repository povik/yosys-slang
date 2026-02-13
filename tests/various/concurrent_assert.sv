// Test simple concurrent assertions
module m_concurrent_assert(input clk, input rst_n, input [7:0] data);
	// Basic posedge assertion
	assert property (@(posedge clk) data != 8'hFF);
endmodule

module m_concurrent_assume(input clk, input [7:0] data);
	// Basic posedge assume
	assume property (@(posedge clk) data != 8'h00);
endmodule

module m_concurrent_cover(input clk, input valid);
	// Basic posedge cover
	cover property (@(posedge clk) valid);
endmodule

module m_negedge_assert(input clk, input [7:0] data);
	// Negedge assertion
	assert property (@(negedge clk) data != 8'hAA);
endmodule

module m_disable_iff(input clk, input rst_n, input [7:0] data);
	// Assertion with disable iff
	assert property (@(posedge clk) disable iff (!rst_n) data != 8'hFF);
endmodule

module m_multiple_concurrent(input clk, input rst_n, input [7:0] data, input valid);
	// Multiple concurrent assertions in one module
	assert property (@(posedge clk) disable iff (!rst_n) data != 8'hFF);
	assume property (@(posedge clk) disable iff (!rst_n) data[7] == 1'b0);
	cover property (@(posedge clk) valid && data == 8'hAA);
	assert property (@(negedge clk) data != 8'h00);
endmodule

module m_labeled_concurrent(input clk, input rst_n, input [7:0] data);
	// Labeled concurrent assertion
	my_concurrent_assert: assert property (@(posedge clk) disable iff (!rst_n) data != 8'hFF);
endmodule

module m_concurrent_past (input clk, input rst_n, input [7:0] index);
    reg [7:0] regs[7:0];
    reg [7:0] past1_reg;
    reg [7:0] past2_reg;
    always @(posedge clk) begin
        past1_reg <= regs[index];
        past2_reg <= past1_reg;
    end
	past_assert1: assert property (@(posedge clk) disable iff (!rst_n) $past(regs[index]) == past1_reg);
	past_assert2: assert property (@(posedge clk) disable iff (!rst_n) $past(regs[index], 1) == past1_reg);
	past_assert3: assert property (@(posedge clk) disable iff (!rst_n || !$past(rst_n)) $past(regs[index], 2) == past2_reg);
endmodule
