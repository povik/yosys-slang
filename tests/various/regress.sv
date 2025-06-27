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

`ifndef KEEP_HIERARCHY
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
`endif

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

`ifndef KEEP_HIERARCHY
// issue #129
module r10n();
wire n;
endmodule

module r10a();
wire t;
assign t = n1.n;
r10n n1();
endmodule

module r10b();
wire t;
r10n n1();
assign t = n1.n;
endmodule
`endif

module r11(input a, input b, input c, output y);
	let andor(a, b, c) = a && b || c;
	assign y = andor(a, b, c);
endmodule

module r12();
	interface class c1#(type T = logic);
	endclass
endmodule

module r13();
	specparam delay = 50;
endmodule

module r14(input x);
	assert #0 (x);
endmodule

module r15sub(input [7:0] allbits, input [1:0] onebit, output bitout);
endmodule

module r15();
	wire [17:10] bitout;
	reg [7:0] allbits;
	reg [15:0] onebit;
	r15sub sub [7:0] (allbits, onebit, bitout);
endmodule

module r16();
	wire [3:0] in;
	wire [3:0] out;
	wire invert;
	xor X[3:0] (out, in, invert);
endmodule

// false memory inference on function argument
module r17();
	function f(int arg [1:0]);
	endfunction
	always_comb begin
		int v [1:0];
		f(v);
	end
endmodule

// return out of task
module r18(
    input logic [7:0] a, input logic [7:0] b, output logic [8:0] out
);
	task sum(logic [7:0] a, logic [7:0] b, output logic [8:0] out);
	    out = a + b;
	    return;
	endtask;
    always_comb sum(a, b, out);
endmodule

// defparam
module r19sub();
	parameter s = 0;
	initial begin
		if (s == 0)
			$error("bad");
	end
endmodule
module r19();
	r19sub inst();
	defparam inst.s = 1;
endmodule

// recursion
module r20(input [31:0] x, output [31:0] q);
	function automatic [31:0] pow;
		input [31:0] base;
		input [31:0] exp;
		begin
			if (exp > 0)
				pow = base * pow(base, exp - 1);
			else
				pow = 1;
		end
	endfunction
	assign q = pow(x, 3);
endmodule

// $fatal with bad arg type
module r21(input clk);
    always @(posedge clk) begin
        // ... long procedure
        if (0)
        	$fatal("foo");
    end
endmodule

// propagate bounds through multiplication
module r22(input clk, input [31:0] i, output reg [31:0] q,
           input [1:0] a, input [1:0] b);
    always @(posedge clk) begin
        q = i;
        for (int i = 1; i < a * b; i++)
            q = q * i;
    end
endmodule
