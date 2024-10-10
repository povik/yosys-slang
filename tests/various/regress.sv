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

module r4;
	logic [1:0] [31:0] data;
	logic [1:0] s;

	always_comb begin
		for (int i = -10; i < 10; i++)
			data[s][i+:8] = 0;
	end
endmodule

module r5;
	logic [1:0] [31:0] data;
	logic [1:0] s;

	always_comb begin
		reg [31:0] acc;
		for (int i = -10; i < 10; i++)
			acc += data[s][i+:8];
	end
endmodule
