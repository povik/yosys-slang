module b1(output logic signed [3:0] y);
	assign y = -3;
endmodule

module a1(output logic signed [7:0] y);
	b1 sb(.y(y));
	always_comb assert(y == 8'hfd);
endmodule

module b2(output logic [3:0] y);
	assign y = -3;
endmodule

module a2(output logic signed [7:0] y);
	b2 sb(.y(y));
	always_comb assert(y == 8'h0d);
endmodule

module b3(output logic signed [3:0] y);
	assign y = -3;
endmodule

module a3(output logic [7:0] y);
	b3 sb(.y(y));
	always_comb assert(y == 8'hfd);
endmodule
