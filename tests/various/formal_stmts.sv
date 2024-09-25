module m_assert(input logic x);
	always_comb assert(x);
endmodule

module m_assume(input logic x);
	always_comb assume(x);
endmodule

module m_cover(input logic x);
	always_comb cover(x);
endmodule
