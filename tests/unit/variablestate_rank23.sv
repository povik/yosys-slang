module variablestate_rank2_repeated_write(
	input logic sel,
	input logic [7:0] base,
	input logic [7:0] a,
	input logic [7:0] b
);
	logic [7:0] actual;
	logic [7:0] expected;

	always_comb begin
		actual = base;
		expected = base;

		if (sel) begin
			actual[5:1] = a[4:0];
			actual[5:1] = b[4:0];
			expected[5:1] = b[4:0];
		end else begin
			actual[7:3] = a[7:3];
			expected[7:3] = a[7:3];
		end

		if (sel !== 1'bx)
			assert(actual === expected);
	end
endmodule

module variablestate_rank2_nested_branch(
	input logic outer,
	input logic inner,
	input logic [9:0] base,
	input logic [5:0] a,
	input logic [5:0] b,
	input logic [5:0] c
);
	logic [9:0] actual;
	logic [9:0] expected;

	always_comb begin
		actual = base;
		expected = base;

		if (outer) begin
			actual[7:2] = a;
			expected[7:2] = a;

			if (inner) begin
				actual[5:0] = b;
				expected[5:0] = b;
			end else begin
				actual[9:4] = c;
				expected[9:4] = c;
			end
		end else begin
			actual[8:3] = c;
			expected[8:3] = c;
		end

		if (outer !== 1'bx && inner !== 1'bx)
			assert(actual === expected);
	end
endmodule

module variablestate_rank2_masked_overlap(
	input logic [1:0] sel,
	input logic [7:0] base,
	input logic [3:0] data
);
	logic [7:0] actual;
	logic [7:0] expected;

	always_comb begin
		actual = base;
		expected = base;

		actual[sel +: 4] = data;

		if (^sel !== 1'bx) begin
			for (int i = 0; i < 4; i++)
				expected[sel + i] = data[i];
			assert(actual === expected);
		end
	end
endmodule

module variablestate_rank23_sparse_fields(
	input logic [3:0] valid,
	output logic [31:0] packed_entries
);
	typedef struct packed {
		logic [6:0] payload;
		logic valid;
	} entry_t;

	entry_t [3:0] entries;

	always_comb begin
		for (int i = 0; i < 4; i++)
			entries[i].valid = valid[i];

		packed_entries = entries;

		assert(packed_entries[0] === valid[0]);
		assert(packed_entries[8] === valid[1]);
		assert(packed_entries[16] === valid[2]);
		assert(packed_entries[24] === valid[3]);
	end
endmodule

module variablestate_rank3_mixed_static_visible(
	input logic [7:0] data,
	output logic [15:0] value,
	output logic [11:0] slice
);
	always_comb begin
		value[11:4] = data;
		slice = value[13:2];

		assert(slice[0] === value[2]);
		assert(slice[1] === value[3]);
		assert(slice[9:2] === data);
		assert(slice[10] === value[12]);
		assert(slice[11] === value[13]);
	end
endmodule

module variablestate_rank3_static_miss(
	input logic [15:0] a,
	input logic [15:0] b,
	output logic [15:0] actual
);
	assign actual[15:8] = b[15:8];

	always_comb begin
		actual[7:0] = a[7:0];

		assert(actual === {b[15:8], a[7:0]});
	end
endmodule
