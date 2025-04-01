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

module r6;
	logic a, b;
	assign {>>{ a }} = b;
endmodule

module r7submod(input logic [3:0] i);
	logic [3:0] w;
	assign w = i + 1;
endmodule

module r7(input logic [3:0] i, output logic [3:0] out);
	r7submod submod(.i(i));
	always_comb begin
		automatic logic [3:0] w_fetched = submod.w;
		out <= w_fetched;
	end
endmodule

module r8();
// `bit` type memories have implicit initialization
bit _bit [7:0];
logic _logic [7:0];
reg _reg [7:0];
endmodule

module r9_blackbox_inner(output w);
endmodule

(* blackbox *)
module r9_blackbox(output w);
	r9_blackbox_inner inner(.*);
endmodule

module r9();
	r9_blackbox box();
endmodule
