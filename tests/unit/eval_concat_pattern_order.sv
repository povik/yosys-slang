typedef struct packed {
	logic [2:0] top;
	logic mid;
	logic [3:0] low;
} eval_order_struct_t;

module eval_concat_rhs_order(
	input logic [3:0] a,
	input logic [3:0] b
);
	wire [7:0] actual = {a[3:2], b[1:0], a[1:0], b[3:2]};

	always_comb begin
		assert(actual[7:6] === a[3:2]);
		assert(actual[5:4] === b[1:0]);
		assert(actual[3:2] === a[1:0]);
		assert(actual[1:0] === b[3:2]);
	end
endmodule

module eval_concat_rhs_dynamic_select_order(
	input logic [7:0] data,
	input logic [1:0] sel
);
	wire [3:0] actual = {data[sel + 3], data[sel +: 3]};

	always_comb begin
		if (^sel !== 1'bx) begin
			assert(actual[3] === data[sel + 3]);
			assert(actual[2:0] === data[sel +: 3]);
		end
	end
endmodule

module eval_assignment_pattern_rhs_struct_order(
	input logic [2:0] top,
	input logic mid,
	input logic [3:0] low
);
	eval_order_struct_t actual;

	assign actual = '{top, mid, low};

	always_comb begin
		assert(actual.top === top);
		assert(actual.mid === mid);
		assert(actual.low === low);
	end
endmodule

module eval_assignment_pattern_rhs_keyed_struct_order(
	input logic [2:0] top,
	input logic mid,
	input logic [3:0] low
);
	eval_order_struct_t actual;

	assign actual = '{low: low, mid: mid, top: top};

	always_comb begin
		assert(actual.top === top);
		assert(actual.mid === mid);
		assert(actual.low === low);
	end
endmodule

module eval_assignment_pattern_rhs_packed_array_order(
	input logic [3:0] high,
	input logic [3:0] low
);
	logic [1:0][3:0] actual;

	assign actual = '{high, low};

	always_comb begin
		assert(actual[1] === high);
		assert(actual[0] === low);
	end
endmodule

module eval_assignment_pattern_rhs_replicated_order(
	input logic [1:0] high,
	input logic [1:0] low
);
	logic [1:0][3:0] actual;

	assign actual = '{2{'{high[1], high[0], low[1], low[0]}}};

	always_comb begin
		assert(actual[1][3:2] === high);
		assert(actual[1][1:0] === low);
		assert(actual[0][3:2] === high);
		assert(actual[0][1:0] === low);
	end
endmodule
