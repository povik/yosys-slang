module static_element_select_vector_base #(
	parameter integer MSB = 4,
	parameter integer LSB = -2,
	parameter integer IDX = 0
) (
	input logic [MSB:LSB] data
);
	localparam integer WIDTH = (MSB > LSB) ? (MSB - LSB + 1) : (LSB - MSB + 1);
	localparam integer OFFSET = (MSB > LSB) ? (IDX - LSB) : (LSB - IDX);

	wire actual = data[IDX];
	wire [WIDTH-1:0] shifted = data >> OFFSET;
	wire [WIDTH-1:0] low_bit_mask = {{(WIDTH-1){1'b0}}, 1'b1};
	wire expected = |(shifted & low_bit_mask);

	always_comb
		assert(actual === expected);
endmodule

module static_element_select_vector_little_neg(
	input logic [4:-2] data
);
	static_element_select_vector_base #(.MSB(4), .LSB(-2), .IDX(-1)) t(.*);
endmodule

module static_element_select_vector_little_high(
	input logic [7:2] data
);
	static_element_select_vector_base #(.MSB(7), .LSB(2), .IDX(6)) t(.*);
endmodule

module static_element_select_vector_big_mid(
	input logic [0:6] data
);
	static_element_select_vector_base #(.MSB(0), .LSB(6), .IDX(4)) t(.*);
endmodule

module static_element_select_vector_big_neg(
	input logic [-2:-7] data
);
	static_element_select_vector_base #(.MSB(-2), .LSB(-7), .IDX(-5)) t(.*);
endmodule

module static_element_select_array_base #(
	parameter integer MSB = 4,
	parameter integer LSB = -2,
	parameter integer IDX = 0
) (
	input logic [MSB:LSB] [1:0] data
);
	localparam integer ELEMENTS = (MSB > LSB) ? (MSB - LSB + 1) : (LSB - MSB + 1);
	localparam integer OFFSET = (MSB > LSB) ? (IDX - LSB) : (LSB - IDX);
	localparam integer TOTAL_WIDTH = ELEMENTS * 2;

	wire [1:0] actual = data[IDX];
	wire [TOTAL_WIDTH-1:0] shifted = data >> (OFFSET * 2);
	wire [TOTAL_WIDTH-1:0] low_bit_mask = {{(TOTAL_WIDTH-1){1'b0}}, 1'b1};
	wire [1:0] expected = {
		|((shifted >> 1) & low_bit_mask),
		|(shifted & low_bit_mask)
	};

	always_comb
		assert(actual === expected);
endmodule

module static_element_select_array_little(
	input logic [4:-2] [1:0] data
);
	static_element_select_array_base #(.MSB(4), .LSB(-2), .IDX(3)) t(.*);
endmodule

module static_element_select_array_big(
	input logic [0:6] [1:0] data
);
	static_element_select_array_base #(.MSB(0), .LSB(6), .IDX(5)) t(.*);
endmodule

module static_element_select_struct_member(
	input logic [2:0] top,
	input logic [1:0] mid,
	input logic low
);
	typedef struct packed {
		logic [2:0] top;
		logic [1:0] mid;
		logic low;
	} static_select_struct_t;

	static_select_struct_t value;
	wire actual_top = value.top[1];
	wire actual_mid = value.mid[0];

	assign value = '{top: top, mid: mid, low: low};

	always_comb begin
		assert(actual_top === top[1]);
		assert(actual_mid === mid[0]);
	end
endmodule
