interface bus;
	logic a, b;
	modport primary(input a, output b);
	modport secondary(input b, output a);
endinterface

module m1(bus.primary intf);
	assign intf.b = !intf.a;
endmodule

module m2(bus.secondary intf, input logic s);
	assign intf.a = s;
	always_comb assert(intf.b === !s);
endmodule

module top(input logic s);
	bus intf();
	m1 a(.*);
	m2 b(.*);
endmodule

module m3(bus.primary intf, output logic x);
	// Missing assign to intf.b
	assign x = intf.a;
endmodule

module top2();
	logic x;
	bus intf();
	m3 c(.*);
	always_comb assert(intf.b === 'x);
endmodule
