module t(input logic data, input logic [1:0] sel, input logic [3:0] bg);
	logic [3:0] a;
	logic [3:0] b;
	logic [3:0] c;
	logic [3:0] d;

	always_comb begin
		a = bg;
		b = bg + 1;
		c = bg;
		d = bg + 1;
		a[sel] = data;
		b[~sel] = ~data;
		{c[sel], d[~sel]} = {data, ~data};
		assert(a === c);
		assert(b === d);
	end
endmodule
