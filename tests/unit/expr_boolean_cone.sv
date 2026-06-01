module expr_boolean_cone_1bit(
	input logic a,
	input logic b,
	input logic c,
	input logic d
);
	wire and_chain = ((a & b) & c) & d;
	wire or_chain = ((a | b) | c) | d;
	wire dup_chain = (a & b) | (a & b);
	wire mixed_not = (~(a & b)) | c;

	always_comb begin
		if (a === 1'b0 || b === 1'b0 || c === 1'b0 || d === 1'b0)
			assert(and_chain === 1'b0);
		if (a === 1'b1 && b === 1'b1 && c === 1'b1 && d === 1'b1)
			assert(and_chain === 1'b1);
		if (a === 1'bx && b === 1'b1 && c === 1'b1 && d === 1'b1)
			assert(and_chain === 1'bx);

		if (a === 1'b1 || b === 1'b1 || c === 1'b1 || d === 1'b1)
			assert(or_chain === 1'b1);
		if (a === 1'b0 && b === 1'b0 && c === 1'b0 && d === 1'b0)
			assert(or_chain === 1'b0);
		if (a === 1'bx && b === 1'b0 && c === 1'b0 && d === 1'b0)
			assert(or_chain === 1'bx);

		if (a === 1'b0 || b === 1'b0)
			assert(dup_chain === 1'b0);
		if (a === 1'b1 && b === 1'b1)
			assert(dup_chain === 1'b1);
		if (a === 1'bx && b === 1'b1)
			assert(dup_chain === 1'bx);

		if (a === 1'b1 && b === 1'b1 && c === 1'b0)
			assert(mixed_not === 1'b0);
		if (a === 1'b0 && c === 1'b0)
			assert(mixed_not === 1'b1);
		if (a === 1'bx && b === 1'b1 && c === 1'b0)
			assert(mixed_not === 1'bx);
	end
endmodule

module expr_boolean_cone_multibit(
	input logic [3:0] a,
	input logic [3:0] b,
	input logic [3:0] c
);
	wire [3:0] actual_and = a & b & c;
	wire [3:0] actual_or = a | b | c;
	logic [3:0] expected_and;
	logic [3:0] expected_or;

	always_comb begin
		for (int i = 0; i < 4; i++) begin
			expected_and[i] = a[i] & b[i] & c[i];
			expected_or[i] = a[i] | b[i] | c[i];
		end

		assert(actual_and === expected_and);
		assert(actual_or === expected_or);
	end
endmodule
