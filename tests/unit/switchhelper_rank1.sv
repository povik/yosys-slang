module switchhelper_rank1_alignment(
	input logic sel,
	input logic [7:0] seed
);
	logic [7:0] actual;
	logic [7:0] expected;

	always_comb begin
		actual = seed;
		expected = seed;

		if (sel) begin
			{actual[0], actual[7], actual[3:2]} = {seed[6], seed[1], seed[5:4]};
			expected[0] = seed[6];
			expected[7] = seed[1];
			expected[3:2] = seed[5:4];
		end else begin
			{actual[6:5], actual[1]} = {seed[2:1], seed[7]};
			expected[6:5] = seed[2:1];
			expected[1] = seed[7];
		end

		if (sel !== 1'bx)
			assert(actual === expected);
	end
endmodule

module switchhelper_rank1_partial_overlap(
	input logic sel,
	input logic [7:0] base,
	input logic [5:0] hi,
	input logic [5:0] lo
);
	logic [7:0] actual;
	logic [7:0] expected;

	always_comb begin
		actual = base;
		expected = base;

		if (sel) begin
			actual[7:2] = hi;
			expected[7:2] = hi;
		end else begin
			actual[5:0] = lo;
			expected[5:0] = lo;
		end

		if (sel !== 1'bx)
			assert(actual === expected);
	end
endmodule

module switchhelper_rank1_automatic_eos(
	input logic sel,
	input logic [3:0] a,
	input logic [3:0] b
);
	logic [3:0] actual;
	logic [3:0] expected;

	always_comb begin
		actual = 4'h0;

		if (sel) begin
			automatic logic [3:0] tmp;
			tmp = {a[0], a[3:1]};
			actual = tmp;
		end else begin
			automatic logic [3:0] tmp;
			tmp = {b[2:0], b[3]};
			actual = tmp;
		end

		expected = sel ? {a[0], a[3:1]} : {b[2:0], b[3]};

		if (sel !== 1'bx)
			assert(actual === expected);
	end
endmodule

module switchhelper_rank1_order(
	input logic [1:0] sel,
	input logic [7:0] a,
	input logic [7:0] b,
	input logic [7:0] c,
	output logic [7:0] y
);
	always_comb begin
		y = a;
		case (sel)
			2'b00: begin
				y[7:2] = b[5:0];
			end
			2'b01: begin
				{y[1], y[6:5], y[3]} = {c[7], c[2:1], c[0]};
			end
			2'b10: begin
				y[5:0] = c[5:0];
			end
			default: begin
				y[4:2] = b[7:5];
			end
		endcase
	end
endmodule

module switchhelper_rank1_reentrant_automatic_local(
	input logic sel,
	input logic [5:0] seed
);
	logic [5:0] actual;
	logic [5:0] expected;

	function automatic logic [5:0] recurse(input logic [1:0] n, input logic [5:0] value);
		automatic logic [5:0] tmp;
		automatic logic [5:0] child;
		begin
			tmp = value ^ {4'b0000, n};
			if (n != 0) begin
				if (sel) begin
					child = recurse(n - 2'd1, tmp + 6'd3);
					tmp = tmp ^ {child[2:0], child[5:3]};
				end else begin
					child = recurse(n - 2'd1, tmp + 6'd5);
					tmp = tmp + {child[0], child[5:1]};
				end
			end
			recurse = tmp;
		end
	endfunction

	always_comb begin
		logic [5:0] f2_tmp;
		logic [5:0] f2_child;
		logic [5:0] f1_input;
		logic [5:0] f1_tmp;
		logic [5:0] f1_child;

		actual = recurse(2'd2, seed);

		f2_tmp = seed ^ 6'd2;
		if (sel) begin
			f1_input = f2_tmp + 6'd3;
			f1_tmp = f1_input ^ 6'd1;
			f1_child = (f1_tmp + 6'd3) ^ 6'd0;
			f2_child = f1_tmp ^ {f1_child[2:0], f1_child[5:3]};
			expected = f2_tmp ^ {f2_child[2:0], f2_child[5:3]};
		end else begin
			f1_input = f2_tmp + 6'd5;
			f1_tmp = f1_input ^ 6'd1;
			f1_child = (f1_tmp + 6'd5) ^ 6'd0;
			f2_child = f1_tmp + {f1_child[0], f1_child[5:1]};
			expected = f2_tmp + {f2_child[0], f2_child[5:1]};
		end

		if (sel !== 1'bx)
			assert(actual === expected);
	end
endmodule
