typedef struct packed {
	logic [1:0] tag;
	logic [1:0][3:0] lanes;
	logic [2:0] tail;
} static_rhs_packet_t;

typedef logic [12:0] static_rhs_bits_t;
typedef logic signed [7:0] static_rhs_signed_byte_t;
typedef logic [7:0] static_rhs_unsigned_byte_t;

module static_rhs_member_select_chain(
	input logic [1:0] tag,
	input logic [1:0][3:0] lanes,
	input logic [2:0] tail
);
	static_rhs_packet_t packet;
	static_rhs_packet_t packet_again;

	assign packet = '{tag: tag, lanes: lanes, tail: tail};

	wire [7:0] actual = {
		packet.tag[0],
		packet.lanes[1][2:1],
		packet.lanes[0][3],
		packet.tail[2:1],
		packet.lanes[0][0],
		packet.tail[0]
	};
	wire [7:0] expected = {
		tag[0],
		lanes[1][2:1],
		lanes[0][3],
		tail[2:1],
		lanes[0][0],
		tail[0]
	};

	wire [12:0] packet_bits = static_rhs_bits_t'(packet);
	wire [12:0] expected_bits = {tag, lanes[1], lanes[0], tail};
	assign packet_again = static_rhs_packet_t'(packet_bits);

	always_comb begin
		assert(actual === expected);
		assert(packet_bits === expected_bits);
		assert(packet_again.tag === tag);
		assert(packet_again.lanes[1] === lanes[1]);
		assert(packet_again.lanes[0] === lanes[0]);
		assert(packet_again.tail === tail);
	end
endmodule

module static_rhs_same_width_vector_cast(
	input logic [7:0] data
);
	wire signed [7:0] signed_data = static_rhs_signed_byte_t'(data);
	wire [7:0] unsigned_data = static_rhs_unsigned_byte_t'(signed_data);

	always_comb
		assert(unsigned_data === data);
endmodule

module static_rhs_dynamic_select_fallback(
	input logic [7:0] data,
	input logic [3:0] bit_sel,
	input logic [3:0] base_sel
);
	wire actual_bit = data[bit_sel];
	wire [1:0] actual_part = data[base_sel +: 2];
	logic expected_bit;
	logic [1:0] expected_part;

	always_comb begin
		expected_bit = 1'bx;
		expected_part = 2'bxx;

		if (^bit_sel !== 1'bx) begin
			case (bit_sel)
				3'd0: expected_bit = data[0];
				3'd1: expected_bit = data[1];
				3'd2: expected_bit = data[2];
				3'd3: expected_bit = data[3];
				3'd4: expected_bit = data[4];
				3'd5: expected_bit = data[5];
				3'd6: expected_bit = data[6];
				3'd7: expected_bit = data[7];
				default: expected_bit = 1'bx;
			endcase
		end

		if (^base_sel !== 1'bx) begin
			case (base_sel)
				3'd0: expected_part = {data[1], data[0]};
				3'd1: expected_part = {data[2], data[1]};
				3'd2: expected_part = {data[3], data[2]};
				3'd3: expected_part = {data[4], data[3]};
				3'd4: expected_part = {data[5], data[4]};
				3'd5: expected_part = {data[6], data[5]};
				3'd6: expected_part = {data[7], data[6]};
				3'd7: expected_part = {1'bx, data[7]};
				default: expected_part = 2'bxx;
			endcase
		end

		assert(actual_bit === expected_bit);
		assert(actual_part === expected_part);
	end
endmodule
