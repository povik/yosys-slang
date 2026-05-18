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

module m_overlapped_implication(input clk, input a, input b);
	// a |-> b is equivalent to !a || b in the same clock tick
	assert property (@(posedge clk) a |-> b);
endmodule

module m_overlapped_implication_disable_iff(input clk, input rst_n, input a, input b);
	// Overlapped implication with disable iff
	assert property (@(posedge clk) disable iff (!rst_n) a |-> b);
endmodule

module m_overlapped_implication_cover(input clk, input a, input b);
	// Cover with overlapped implication
	cover property (@(posedge clk) a |-> b);
endmodule
