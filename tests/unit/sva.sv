module test_sva_edge_cases (input clk, input a, input b, input c);
	always_comb begin
		if (^{a, b, c} !== 'x) begin
			if (a) begin
				foo: assert property (disable iff (a) b);
			end
		end
	end

	always_comb begin
		int i;
		automatic int j = 0;
		i = 0;
		bar1: assert property (i == 1 && const'(i) == 0 && j == 0);
		i++;
		j++;
	end
endmodule
