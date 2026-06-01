module expr_wide_bitwise_semantics(
	input logic [3:0] a,
	input logic [3:0] b
);
	wire [3:0] actual_and = a & b;
	wire [3:0] actual_and_commuted = b & a;
	wire [3:0] actual_or = a | b;
	wire [3:0] actual_or_commuted = b | a;
	wire [3:0] actual_xor = a ^ b;
	wire [3:0] actual_xor_commuted = b ^ a;
	wire [3:0] actual_xnor = a ~^ b;
	wire [3:0] actual_not = ~a;

	logic [3:0] expected_and;
	logic [3:0] expected_or;
	logic [3:0] expected_xor;
	logic [3:0] expected_xnor;
	logic [3:0] expected_not;

	always_comb begin
		for (int i = 0; i < 4; i++) begin
			expected_and[i] = a[i] & b[i];
			expected_or[i] = a[i] | b[i];
			expected_xor[i] = a[i] ^ b[i];
			expected_xnor[i] = ~(a[i] ^ b[i]);
			expected_not[i] = ~a[i];

			if (a[i] === 1'bx && b[i] === 1'b0) begin
				assert(actual_and[i] === 1'b0);
				assert(actual_or[i] === 1'bx);
				assert(actual_xor[i] === 1'bx);
				assert(actual_xnor[i] === 1'bx);
				assert(actual_not[i] === 1'bx);
			end

			if (a[i] === 1'bx && b[i] === 1'b1) begin
				assert(actual_and[i] === 1'bx);
				assert(actual_or[i] === 1'b1);
				assert(actual_xor[i] === 1'bx);
				assert(actual_xnor[i] === 1'bx);
				assert(actual_not[i] === 1'bx);
			end
		end

		assert(actual_and === expected_and);
		assert(actual_and_commuted === expected_and);
		assert(actual_or === expected_or);
		assert(actual_or_commuted === expected_or);
		assert(actual_xor === expected_xor);
		assert(actual_xor_commuted === expected_xor);
		assert(actual_xnor === expected_xnor);
		assert(actual_not === expected_not);
	end
endmodule
