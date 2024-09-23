module top(input logic [3:0] w);
	logic [1:0] m1, m2;

	always_comb
	casez (w)
		4'b?00?: m1 = 0;
		4'b??10: m1 = 1;
		4'b010?: m1 = 2;
		4'b11??, 4'b??11: m1 = 3;
	endcase

	always_comb
	casex (w)
		4'bx00?: m2 = 0;
		4'b?x10: m2 = 1;
		4'b010x: m2 = 2;
		default: m2 = 3;
	endcase

	always_comb
	if (^w !== 'x) begin
		assert(m1 === m2);
		if (w[2:1] == '0)
			assert(m1 === 0);
		else if (w[1:0] == 2'b10)
			assert(m1 === 1);
		else if (w[3:1] == 3'b010)
			assert(m1 === 2);
		else
			assert(m1 === 3);
	end
endmodule
