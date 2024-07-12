module t_base(data, sel);
	parameter MSB = 4;
	parameter LSB = 0;
	localparam little_endian = MSB > LSB;

	input [MSB:LSB] data;
	input signed [4:0] sel;

	wire o = data[sel];

	always @* begin
		if (sel[0] === 1'bx ||
				sel[1] === 1'bx ||
				sel[2] === 1'bx ||
				sel[3] === 1'bx ||
				sel[4] === 1'bx) begin
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

module t01(data, sel);
	input [4:-2] data;
	input signed [4:0] sel;
	t_base #(.MSB(4), .LSB(-2)) t(.*);
endmodule

module t02(data, sel);
	input [6:0] data;
	input signed [4:0] sel;
	t_base #(.MSB(6), .LSB(0)) t(.*);
endmodule

module t03(data, sel);
	input [7:2] data;
	input signed [4:0] sel;
	t_base #(.MSB(7), .LSB(2)) t(.*);
endmodule

module t04(data, sel);
	input [0:6] data;
	input signed [4:0] sel;
	t_base #(.MSB(0), .LSB(6)) t(.*);
endmodule

module t05(data, sel);
	input [2:7] data;
	input signed [4:0] sel;
	t_base #(.MSB(2), .LSB(7)) t(.*);
endmodule

module t06(data, sel);
	input [-7:-2] data;
	input signed [4:0] sel;
	t_base #(.MSB(-7), .LSB(-2)) t(.*);
endmodule

module t07(data, sel);
	input [-2:-7] data;
	input signed [4:0] sel;
	t_base #(.MSB(-2), .LSB(-7)) t(.*);
endmodule
