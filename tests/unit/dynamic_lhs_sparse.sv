module dynamic_lhs_bit_static_priority(
	input logic [3:0] base,
	input logic [1:0] sel,
	input logic dynamic_bit,
	input logic static_bit,
	output logic [3:0] actual
);
	logic [3:0] expected;

	always_comb begin
		actual = base;
		actual[sel] = dynamic_bit;
		actual[1] = static_bit;

		expected = base;
		case (sel)
			2'd0: expected[0] = dynamic_bit;
			2'd1: expected[1] = dynamic_bit;
			2'd2: expected[2] = dynamic_bit;
			2'd3: expected[3] = dynamic_bit;
		endcase
		expected[1] = static_bit;

		if (^sel !== 1'bx)
			assert(actual === expected);
	end
endmodule

module dynamic_lhs_static_dynamic_priority(
	input logic [3:0] base,
	input logic [1:0] sel,
	input logic dynamic_bit,
	input logic static_bit,
	output logic [3:0] actual
);
	logic [3:0] expected;

	always_comb begin
		actual = base;
		actual[1] = static_bit;
		actual[sel] = dynamic_bit;

		expected = base;
		expected[1] = static_bit;
		case (sel)
			2'd0: expected[0] = dynamic_bit;
			2'd1: expected[1] = dynamic_bit;
			2'd2: expected[2] = dynamic_bit;
			2'd3: expected[3] = dynamic_bit;
		endcase

		if (^sel !== 1'bx)
			assert(actual === expected);
	end
endmodule

module dynamic_lhs_packed_lane(
	input logic [31:0] base_flat,
	input logic [1:0] sel,
	input logic [7:0] data,
	output logic [31:0] actual_flat
);
	logic [3:0][7:0] base;
	logic [3:0][7:0] actual;
	logic [3:0][7:0] expected;

	assign base = base_flat;
	assign actual_flat = actual;

	always_comb begin
		actual = base;
		actual[sel] = data;

		expected = base;
		case (sel)
			2'd0: expected[0] = data;
			2'd1: expected[1] = data;
			2'd2: expected[2] = data;
			2'd3: expected[3] = data;
		endcase

		if (^sel !== 1'bx)
			assert(actual === expected);
	end
endmodule

module dynamic_lhs_indexed_byte_partselect(
	input logic [31:0] base,
	input logic [1:0] sel,
	input logic [7:0] data,
	output logic [31:0] actual
);
	logic [31:0] expected;

	always_comb begin
		actual = base;
		actual[{sel, 3'b000} +: 8] = data;

		expected = base;
		case (sel)
			2'd0: expected[7:0] = data;
			2'd1: expected[15:8] = data;
			2'd2: expected[23:16] = data;
			2'd3: expected[31:24] = data;
		endcase

		if (^sel !== 1'bx)
			assert(actual === expected);
	end
endmodule

module dynamic_lhs_selected_struct_field(
	input logic [31:0] base_flat,
	input logic [1:0] sel,
	input logic [4:0] payload,
	output logic [31:0] actual_flat
);
	typedef struct packed {
		logic [2:0] tag;
		logic [4:0] payload;
	} item_t;

	item_t [3:0] base;
	item_t [3:0] actual;
	item_t [3:0] expected;

	assign base = base_flat;
	assign actual_flat = actual;

	always_comb begin
		actual = base;
		actual[sel].payload = payload;

		expected = base;
		case (sel)
			2'd0: expected[0].payload = payload;
			2'd1: expected[1].payload = payload;
			2'd2: expected[2].payload = payload;
			2'd3: expected[3].payload = payload;
		endcase

		if (^sel !== 1'bx)
			assert(actual === expected);
	end
endmodule

module dynamic_lhs_branch_updates(
	input logic [7:0] base,
	input logic choose,
	input logic [2:0] sel_a,
	input logic [2:0] sel_b,
	input logic bit_a,
	input logic bit_b,
	output logic [7:0] actual
);
	logic [7:0] expected;

	always_comb begin
		actual = base;
		if (choose)
			actual[sel_a] = bit_a;
		else
			actual[sel_b] = bit_b;

		expected = base;
		if (choose) begin
			case (sel_a)
				3'd0: expected[0] = bit_a;
				3'd1: expected[1] = bit_a;
				3'd2: expected[2] = bit_a;
				3'd3: expected[3] = bit_a;
				3'd4: expected[4] = bit_a;
				3'd5: expected[5] = bit_a;
				3'd6: expected[6] = bit_a;
				3'd7: expected[7] = bit_a;
			endcase
		end else begin
			case (sel_b)
				3'd0: expected[0] = bit_b;
				3'd1: expected[1] = bit_b;
				3'd2: expected[2] = bit_b;
				3'd3: expected[3] = bit_b;
				3'd4: expected[4] = bit_b;
				3'd5: expected[5] = bit_b;
				3'd6: expected[6] = bit_b;
				3'd7: expected[7] = bit_b;
			endcase
		end

		if (choose !== 1'bx && ^sel_a !== 1'bx && ^sel_b !== 1'bx)
			assert(actual === expected);
	end
endmodule

module dynamic_lhs_branch_absent_restore(
	input logic [7:0] base,
	input logic enable,
	input logic [2:0] sel,
	input logic data,
	output logic [7:0] actual
);
	logic [7:0] expected;

	always_comb begin
		actual = base;
		if (enable)
			actual[sel] = data;

		expected = base;
		if (enable) begin
			case (sel)
				3'd0: expected[0] = data;
				3'd1: expected[1] = data;
				3'd2: expected[2] = data;
				3'd3: expected[3] = data;
				3'd4: expected[4] = data;
				3'd5: expected[5] = data;
				3'd6: expected[6] = data;
				3'd7: expected[7] = data;
			endcase
		end

		if (enable !== 1'bx && ^sel !== 1'bx)
			assert(actual === expected);
	end
endmodule

module dynamic_lhs_overlap_priority(
	input logic [6:0] base,
	input logic [1:0] sel,
	input logic [2:0] data,
	input logic override_bit,
	output logic [6:0] actual
);
	logic [6:0] expected;

	always_comb begin
		actual = base;
		actual[sel +: 3] = data;
		actual[sel + 1] = override_bit;

		expected = base;
		case (sel)
			2'd0: expected[2:0] = data;
			2'd1: expected[3:1] = data;
			2'd2: expected[4:2] = data;
			2'd3: expected[5:3] = data;
		endcase
		case (sel)
			2'd0: expected[1] = override_bit;
			2'd1: expected[2] = override_bit;
			2'd2: expected[3] = override_bit;
			2'd3: expected[4] = override_bit;
		endcase

		if (^sel !== 1'bx)
			assert(actual === expected);
	end
endmodule

module dynamic_lhs_nonzero_vector_range(
	input logic [4:1] base,
	input logic [1:0] sel,
	input logic data,
	output logic [4:1] actual
);
	logic [4:1] expected;

	always_comb begin
		actual = base;
		actual[sel + 1] = data;

		expected = base;
		case (sel)
			2'd0: expected[1] = data;
			2'd1: expected[2] = data;
			2'd2: expected[3] = data;
			2'd3: expected[4] = data;
		endcase

		if (^sel !== 1'bx)
			assert(actual === expected);
	end
endmodule

module dynamic_lhs_descending_array_lane(
	input logic [15:0] base_flat,
	input logic [1:0] sel,
	input logic [3:0] data,
	output logic [15:0] actual_flat
);
	logic [1:4][3:0] base;
	logic [1:4][3:0] actual;
	logic [1:4][3:0] expected;

	assign base = base_flat;
	assign actual_flat = actual;

	always_comb begin
		actual = base;
		actual[sel + 1] = data;

		expected = base;
		case (sel)
			2'd0: expected[1] = data;
			2'd1: expected[2] = data;
			2'd2: expected[3] = data;
			2'd3: expected[4] = data;
		endcase

		if (^sel !== 1'bx)
			assert(actual === expected);
	end
endmodule

module dynamic_lhs_chunk_boundary(
	input logic [129:0] base,
	input logic [7:0] sel,
	input logic data,
	output logic [129:0] actual
);
	logic [129:0] selected;
	logic [129:0] expected;

	always_comb begin
		actual = base;
		actual[sel] = data;

		selected = 130'b1 << sel;
		expected = (base & ~selected) | ({130{data}} & selected);

		if (^sel !== 1'bx) begin
			if (sel < 8'd130)
				assert(actual === expected);
			else
				assert(actual === base);
		end
	end
endmodule

module dynamic_lhs_block_boundary(
	input logic [256:0] base,
	input logic [8:0] sel,
	input logic data,
	output logic [256:0] actual
);
	logic [256:0] selected;
	logic [256:0] expected;

	always_comb begin
		actual = base;
		actual[sel] = data;

		selected = 257'b1 << sel;
		expected = (base & ~selected) | ({257{data}} & selected);

		if (^sel !== 1'bx) begin
			if (sel < 9'd257)
				assert(actual === expected);
			else
				assert(actual === base);
		end
	end
endmodule

module dynamic_lhs_wide_lane_multi_block(
	input logic [1151:0] base_flat,
	input logic [2:0] sel,
	input logic [143:0] data,
	output logic [1151:0] actual_flat
);
	logic [7:0][143:0] base;
	logic [7:0][143:0] actual;
	logic [7:0][143:0] expected;

	assign base = base_flat;
	assign actual_flat = actual;

	always_comb begin
		actual = base;
		actual[sel] = data;

		expected = base;
		case (sel)
			3'd0: expected[0] = data;
			3'd1: expected[1] = data;
			3'd2: expected[2] = data;
			3'd3: expected[3] = data;
			3'd4: expected[4] = data;
			3'd5: expected[5] = data;
			3'd6: expected[6] = data;
			3'd7: expected[7] = data;
		endcase

		if (^sel !== 1'bx)
			assert(actual === expected);
	end
endmodule

module dynamic_lhs_narrow_selector_no_alias(
	input logic [191:0] base,
	input logic [5:0] sel,
	input logic data,
	output logic [191:0] actual
);
	logic [63:0] selected;
	logic [191:0] expected;

	always_comb begin
		actual = base;
		actual[sel] = data;

		selected = 64'b1 << sel;
		expected = {base[191:64], (base[63:0] & ~selected) | ({64{data}} & selected)};

		if (^sel !== 1'bx)
			assert(actual === expected);
	end
endmodule
