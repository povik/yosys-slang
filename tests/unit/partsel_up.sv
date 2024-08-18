module base(data, sel);
	parameter MSB = 0;
	parameter LSB = 0;
	localparam big_endian = MSB < LSB;

	input [MSB:LSB] data;
	input [2:0] sel;

	wire [1:0] o = data[sel+:2];

	always_comb begin
		if (sel[0] === 1'bx ||
				sel[1] === 1'bx ||
				sel[2] === 1'bx) begin
			assert(o === 2'bxx);
		end else begin
			assert(o === (big_endian ?
							{data[sel], data[sel + 1]}
							: {data[sel + 1], data[sel]}));
		end
	end
endmodule

module test_partsel_up01(data, sel);
	input [4:-2] data;
	input [2:0] sel;
	base #(.MSB(4), .LSB(-2)) t(.*);
endmodule

module test_partsel_up02(data, sel);
	input [6:0] data;
	input [2:0] sel;
	base #(.MSB(6), .LSB(0)) t(.*);
endmodule

module test_partsel_up03(data, sel);
	input [7:2] data;
	input [2:0] sel;
	base #(.MSB(7), .LSB(2)) t(.*);
endmodule

module test_partsel_up04(data, sel);
	input [0:6] data;
	input [2:0] sel;
	base #(.MSB(0), .LSB(6)) t(.*);
endmodule

module test_partsel_up05(data, sel);
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
	always_comb begin
		data = i1;
		data[sel+:2] = i2;
	end

	reg [MSB:LSB] data2;
	always_comb begin
		data2 = i1;
		if (big_endian) begin
			data2[sel + 1] = i2[0];
			data2[sel] = i2[1];
		end else begin
			data2[sel] = i2[0];
			data2[sel + 1] = i2[1];
		end
	end

	always_comb begin
		if (sel[0] === 1'bx ||
				sel[1] === 1'bx ||
				sel[2] === 1'bx) begin
			// No guarantees
		end else begin
			assert(data2 === data);
		end
	end
endmodule

module test_partsel_up06(i1, i2, sel);
	input [4:-2] i1;
	input [1:0] i2;
	input [2:0] sel;
	base2 #(.MSB(4), .LSB(-2)) t(.*);
endmodule

module test_partsel_up07(i1, i2, sel);
	input [6:0] i1;
	input [1:0] i2;
	input [2:0] sel;
	base2 #(.MSB(6), .LSB(0)) t(.*);
endmodule

module test_partsel_up08(i1, i2, sel);
	input [7:2] i1;
	input [1:0] i2;
	input [2:0] sel;
	base2 #(.MSB(7), .LSB(2)) t(.*);
endmodule

module test_partsel_up09(i1, i2, sel);
	input [0:6] i1;
	input [1:0] i2;
	input [2:0] sel;
	base2 #(.MSB(0), .LSB(6)) t(.*);
endmodule

module test_partsel_up10(i1, i2, sel);
	input [2:7] i1;
	input [1:0] i2;
	input [2:0] sel;
	base2 #(.MSB(2), .LSB(7)) t(.*);
endmodule
