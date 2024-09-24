// To catch regressions around snippets which previously failed
// to parse

module r1;
	logic a [0:1];
	assign a[1'b0] = 1;
endmodule

module r2;
	logic [1:0] a [0:1];
	always_comb
		a[1'b0-:1] = '{0};
endmodule

module r3;
logic [7:0] m;
always @(*) begin
	m[4-:2] <= 0;
end
endmodule
