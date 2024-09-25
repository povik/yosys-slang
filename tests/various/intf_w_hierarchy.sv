interface bus(input clk);
	logic a, b;
	modport primary(input a, output b, input clk);
	modport secondary(input b, output a, input clk);
endinterface

module m1(bus.primary intf, input logic clk);
	assign intf.b = !intf.a;
	always_comb assert(intf.clk === clk);
endmodule

module m3(bus.secondary intf, input logic s);
	assign intf.a = s;
	always_comb assert(intf.b === !s);
endmodule

module m2(bus.secondary intf, input logic s);
	m3 c(.*);
endmodule

module top(input logic s, input logic clk);
	bus intf(clk);
	m1 a(.*);
	m2 b(.*);
endmodule
