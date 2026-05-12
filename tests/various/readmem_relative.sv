module top();
	(* rom_block *)
	reg [7:0] x[0:3];
	reg [7:0] y[0:3];

	initial begin
		$readmemh("readmem_data.hex", x);
		y = '{8'h01, 8'h2a, 8'hff, 8'h80};
	end

	always_comb
		assert(x[0] === y[0] && x[1] === y[1] && x[2] === y[2] && x[3] === y[3]);
endmodule
