module pass_thru1(input logic [3:0] a=6, output logic [3:0] b);
	assign b = a;
endmodule

// ordered list connection
module ordered_list(output logic [3:0] y);
	// missing, uses default
	pass_thru1 sb(, y);
	always_comb assert(y === 6);
endmodule

// connection by name
module named_conn(output logic [3:0] y, output logic [3:0] y2);
	// omitted, uses default
	pass_thru1 sb(.b(y));
	always_comb assert(y === 6);

	// connnected to an empty argument, explicitly unconnected and ignores default
	pass_thru1 sb2(.a(), .b(y2));
	always_comb assert(y2 === 'x);
endmodule
