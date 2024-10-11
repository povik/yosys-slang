interface bus(input clk);
	logic a, b;
	modport primary(input a, output b, input clk);
	modport secondary(input b, output a, input clk);
endinterface

module m1(bus.primary intf [1:0], input logic clk);
	assign intf[0].b = !intf[0].a;
	always_comb assert(intf[0].clk === clk);

	assign intf[1].b = !intf[1].a;
	always_comb assert(intf[1].clk === clk);
endmodule

module m3(bus.secondary intf [1:0], input logic [1:0] s);
	assign intf[0].a = s[0];
	assign intf[1].a = s[1];
	always_comb assert(intf[0].b === !s[0]);
	always_comb assert(intf[1].b === !s[1]);
endmodule

module m2(bus.secondary intf [1:0], input logic [1:0] s);
	m3 c(.*);
endmodule

module top(input logic [1:0] s, input logic clk);
	bus intf[1:0](clk);
	m1 m1i(intf, clk);
	m2 m2i(intf, s);
endmodule
