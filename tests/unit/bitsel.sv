module base(data, sel);
	parameter MSB = 4;
	parameter LSB = 0;
	localparam little_endian = MSB > LSB;

	input [MSB:LSB] data;
	input signed [4:0] sel;

	wire o = data[sel];

	always @* begin
		if (^sel === 'x) begin
			assert(o === 1'bx);
		end else begin
			if (little_endian) begin
				if (sel > $signed(MSB) || sel < $signed(LSB)) begin
					assert(o === 1'bx);
				end else begin
					assert(o === {data >> (sel - LSB)}[0]);
				end
			end else begin
				if (sel > $signed(LSB) || sel < $signed(MSB)) begin
					assert(o === 1'bx);
				end else begin
					assert(o === {data >> (LSB - sel)}[0]);
				end
			end
		end
	end
endmodule

module test_bitsel01(data, sel);
	input [4:-2] data;
	input signed [4:0] sel;
	base #(.MSB(4), .LSB(-2)) t(.*);
endmodule

module test_bitsel02(data, sel);
	input [6:0] data;
	input signed [4:0] sel;
	base #(.MSB(6), .LSB(0)) t(.*);
endmodule

module test_bitsel03(data, sel);
	input [7:2] data;
	input signed [4:0] sel;
	base #(.MSB(7), .LSB(2)) t(.*);
endmodule

module test_bitsel04(data, sel);
	input [0:6] data;
	input signed [4:0] sel;
	base #(.MSB(0), .LSB(6)) t(.*);
endmodule

module test_bitsel05(data, sel);
	input [2:7] data;
	input signed [4:0] sel;
	base #(.MSB(2), .LSB(7)) t(.*);
endmodule

module test_bitsel06(data, sel);
	input [-7:-2] data;
	input signed [4:0] sel;
	base #(.MSB(-7), .LSB(-2)) t(.*);
endmodule

module test_bitsel07(data, sel);
	input [-2:-7] data;
	input signed [4:0] sel;
	base #(.MSB(-2), .LSB(-7)) t(.*);
endmodule
