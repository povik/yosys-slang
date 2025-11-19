// This file tests the mapping of SystemVerilog expressions onto
// the internal Yosys cell library.
//
// Each expression passed in argument to `$t` is evaluated twice:
// The result of slang's constant evaluation is checked to agree
// with the result obtained by evaluating the mapped Yosys cells.
//
// Nets and static variables cannot be used; but functions, automatic
// variables, and localparams can be.

module top;

function [7:0] f1();
	f1 = 8'hab;
endfunction;

initial $t(f1());

// unary
initial begin
	$t(-7);
	$t(-4'hf);
	$t(-4'he);
	$t(!(-4));
	$t(!0);
	$t(|3'd0);
	$t(|3'd1);
	$t(|3'd3);
	$t(&3'd0);
	$t(&3'd6);
	$t(&3'd7);
	$t(~&3'd0);
	$t(~&3'd6);
	$t(~&3'd7);
	$t(~|3'd0);
	$t(~|3'd1);
	$t(~|3'd3);
	$t(~^3'd0);
	$t(~^3'd1);
	$t(~^3'd3);
	$t(+(3'd3));
end

// binary
initial begin
	$t(-1 + -1);
	$t(-8'd1 + 1);
	$t(8'shff + $unsigned(1));
	$t((8'd5 - 8'd8) + 16'd1);
	$t(3'd1 * 8'd7);
	$t(13 / 4);
	$t(-13 / 4);
	$t(13 / -4);
	$t(-13 / -4);
	$t(13 % 4);
	$t(-13 % 4);
	$t(13 % -4);
	$t(-13 % -4);
	$t(16'd123 & 16'd71);
	$t(16'd123 | 16'd71);
	$t(16'd123 ^ 16'd71);
	$t(16'd123 ~^ 16'd71);
	$t(4'hf > -11);
	$t(-1 > 7);
	$t(3 > 3);
	$t(4'hf >= -11);
	$t(-1 >= 7);
	$t(3 >= 3);
	$t(4'hf < -11);
	$t(-1 < 7);
	$t(3 < 3);
	$t(4'hf <= -11);
	$t(-1 <= 7);
	$t(3 <= 3);
	$t(2 -> 1);
	$t(0 -> 3);
	$t(-1 -> 0);
	$t(0 -> 0);
	$t(2 <-> 1);
	$t(0 <-> 3);
	$t(-1 <-> 0);
	$t(0 <-> 0);
	$t(2 <-> 1);
	$t(0 <-> 3);
	$t(-1 <-> 0);
	$t(8'd1 << 5);
	$t(-8'h2 << 3);
	$t(8'd1 >> 5);
	$t(-8'd2 >> 3);
	$t(8'd1 <<< 5);
	$t(-8'd2 <<< 3);
	$t(8'd1 >>> 5);
	$t(-8'd2 >>> 3);
	$t(2'd1 == 8'd2);
	$t(-2'd1 == 8'hff);
	$t(3**2);
	$t(-3**2);
	$t(-3**-2);
	$t(-3**-7);
	$t(-3**0);
	$t(0**7);
end

typedef logic [7:0] byte_t;

initial begin
	$t(byte_t'({<<1{8'hd6}}));
	$t(byte_t'({>>1{8'hd6}}));
	$t(byte_t'({<<2{8'hd6}}));
	$t(byte_t'({>>2{8'hd6}}));
	$t(byte_t'({>>3{8'hd6}}));
	$t(byte_t'({<<3{8'hd6}}));
	$t(byte_t'({>>5{8'hd6}}));
	$t(byte_t'({<<5{8'hd6}}));
end

function [7:0] stream1();
	stream1 = {<<1{8'hd6}};
endfunction
function [7:0] stream2();
	stream2 = {>>1{7'h56}};
endfunction
function [7:0] stream3();
	stream3 = {<<2{8'hd6}};
endfunction
function [7:0] stream4();
	stream4 = {>>2{8'hd6}};
endfunction

initial begin
	$t(stream1());
	$t(stream2());
	$t(stream3());
	$t(stream4());
end

function [7:0] stream5();
	{<<1{stream5}} = 8'hd6;
endfunction
function [7:0] stream6();
	{>>1{stream6}} = 9'h56;
endfunction
function [7:0] stream7();
	{<<2{stream7}} = 8'hd6;
endfunction
function [7:0] stream8();
	{>>2{stream8}} = 8'hd6;
endfunction

initial begin
	$t(stream5());
	$t(stream6());
	$t(stream7());
	$t(stream8());
end

// nested streaming
initial $t(byte_t'({>>3{4'h6, {>>2{4'h7}}}}));

function automatic [7:0] f();
    logic [4:0] data[2] = '{12, 43};
	logic [4:0] a, b;
	'{ a, b } = data;
	return {a, b};
endfunction
initial $t(f());

initial begin
	$t(4'b0110 ==? 4'b0z10);
	$t(4'b0010 ==? 4'b0z10);
	$t(4'b1110 ==? 4'b0z10);
	$t(4'b0101 ==? 4'bzz01);
	$t(4'b1001 ==? 4'bzz01);
	$t(4'b1011 ==? 4'bzz01);
	$t(4'bzzzz ==? 4'b0000);
	$t(4'b0110 ==? 4'b0x10);
	$t(4'b0010 ==? 4'b0x10);
	$t(4'b1110 ==? 4'b0x10);
	$t(4'b0101 ==? 4'bxx01);
	$t(4'b1001 ==? 4'bxx01);
	$t(4'b1011 ==? 4'bxx01);
	$t(4'bxxxx ==? 4'b0000);
end

function automatic [15:0] decrpre(logic [7:0] v);
	logic [7:0] a;
	logic [7:0] b;
	a = v--;
	b = v;
	return {a, b};
endfunction

function automatic [15:0] decrpost(logic [7:0] v);
	logic [7:0] a;
	logic [7:0] b;
	a = --v;
	b = v;
	return {a, b};
endfunction

function automatic [15:0] incrpre(logic [7:0] v);
	logic [7:0] a;
	logic [7:0] b;
	a = v++;
	b = v;
	return {a, b};
endfunction

function automatic [15:0] incrpost(logic [7:0] v);
	logic [7:0] a;
	logic [7:0] b;
	a = ++v;
	b = v;
	return {a, b};
endfunction

initial begin
	$t(decrpre(8'h7));
	$t(decrpost(8'h7));
	$t(incrpre(8'h7));
	$t(incrpost(8'h7));
end

// casting and signedness
parameter type hpdcache_mem_id_t = logic [3:0];
function logic f2();
	automatic hpdcache_mem_id_t icache_miss_id_i;
	icache_miss_id_i = hpdcache_mem_id_t'(1 << 3);
	return (8 == int'(icache_miss_id_i));
endfunction
initial $t(f2());

// unpacked struct member access
typedef struct {
    logic a;
    logic [1:0] b;
    logic c;
    logic d;
} unpacked_t;
function logic [4:0] f3();
	unpacked_t x;
	x = unpacked_t'(5'b1x100);
	return {x.a, x.c, x.d, x.b};
endfunction
initial $t(f3());

// unpacked struct write
function unpacked_t f4();
    unpacked_t x;
    x.a = 1'bx;
    x.b = 2'b01;
    x.c = 1'bx;
    x.d = 1'b0;
    return x;
endfunction
initial $t(f4());

endmodule
