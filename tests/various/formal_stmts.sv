module m_assert(input logic x);
	always_comb assert(x);
endmodule

module m_assume(input logic x);
	always_comb assume(x);
endmodule

module m_cover(input logic x);
	always_comb cover(x);
endmodule

module m_labeled_assertions(input logic x, y, z);
	always_comb my_assert: assert(x);
	always_comb my_assume: assume(y);
	always_comb my_cover: cover(z);
endmodule
