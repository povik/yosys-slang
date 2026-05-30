module miter1(input clk_i, input logic x, input logic y);
	reg gate = 0;
	always @(posedge clk_i) begin
		seq_1_ref: assert(($past(x) && y) || !gate);
		gate = 1;
	end
	seq_1_test: assert property(@(posedge clk_i) x ##1 y);
endmodule
