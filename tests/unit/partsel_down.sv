module base(data, sel);
	parameter MSB = 0;
	parameter LSB = 0;
	localparam big_endian = MSB < LSB;

	input [MSB:LSB] data;
	input [2:0] sel;

	wire [1:0] o = data[sel-:2];
	wire signed [3:0] sel_signed = sel;
	wire [1:0] o2 = (big_endian ?
							{data[sel_signed - 1], data[sel]}
							: {data[sel], data[sel_signed - 1]});

	always @* begin
		if (sel[0] === 1'bx ||
				sel[1] === 1'bx ||
				sel[2] === 1'bx) begin
			assert(o === 2'bxx);
		end else begin
			assert(o === (big_endian ?
							{data[sel_signed - 1], data[sel]}
							: {data[sel], data[sel_signed - 1]}));
		end
	end
endmodule

module test_partsel_down01(data, sel);
	input [4:-2] data;
	input [2:0] sel;
	base #(.MSB(4), .LSB(-2)) t(.*);
endmodule

module test_partsel_down02(data, sel);
	input [6:0] data;
	input [2:0] sel;
	base #(.MSB(6), .LSB(0)) t(.*);
endmodule

module test_partsel_down03(data, sel);
	input [7:2] data;
	input [2:0] sel;
	base #(.MSB(7), .LSB(2)) t(.*);
endmodule

module test_partsel_down04(data, sel);
	input [0:6] data;
	input [2:0] sel;
	base #(.MSB(0), .LSB(6)) t(.*);
endmodule

module test_partsel_down05(data, sel);
	input [2:7] data;
	input [2:0] sel;
	base #(.MSB(2), .LSB(7)) t(.*);
endmodule

module base2(i1, i2, sel);
	parameter MSB = 0;
	parameter LSB = 0;
	localparam big_endian = MSB < LSB;

	input [2:0] sel;
	input [MSB:LSB] i1;
	input [1:0] i2;

	reg [MSB:LSB] data;
	always @* begin
		data = i1;
		data[sel-:2] = i2;
	end

	reg [MSB:LSB] data2;
	wire signed [3:0] sel_signed = sel;
	always @* begin
		data2 = i1;
		if (big_endian) begin
			data2[sel_signed] = i2[0];
			data2[sel_signed - 1] = i2[1];
		end else begin
			data2[sel_signed - 1] = i2[0];
			data2[sel_signed] = i2[1];
		end
	end

	always @* begin
		if (sel[0] === 1'bx ||
				sel[1] === 1'bx ||
				sel[2] === 1'bx) begin
			// No guarantees
		end else begin
			assert(data2 === data);
		end
	end
endmodule

module test_partsel_down06(i1, i2, sel);
	input [4:-2] i1;
	input [1:0] i2;
	input [2:0] sel;
	base2 #(.MSB(4), .LSB(-2)) t(.*);
endmodule

module test_partsel_down07(i1, i2, sel);
	input [6:0] i1;
	input [1:0] i2;
	input [2:0] sel;
	base2 #(.MSB(6), .LSB(0)) t(.*);
endmodule

module test_partsel_down08(i1, i2, sel);
	input [7:2] i1;
	input [1:0] i2;
	input [2:0] sel;
	base2 #(.MSB(7), .LSB(2)) t(.*);
endmodule

module test_partsel_down09(i1, i2, sel);
	input [0:6] i1;
	input [1:0] i2;
	input [2:0] sel;
	base2 #(.MSB(0), .LSB(6)) t(.*);
endmodule

module test_partsel_down10(i1, i2, sel);
	input [2:7] i1;
	input [1:0] i2;
	input [2:0] sel;
	base2 #(.MSB(2), .LSB(7)) t(.*);
endmodule
