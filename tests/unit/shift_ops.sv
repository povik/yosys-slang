module top(input logic signed [3:0] a, input logic [3:0] sham);
	logic [3:0] shr;
	logic [3:0] sshr;
	assign shr = a >> sham;
	assign sshr = a >>> sham;
	always_comb begin
		if (^a !== 'x && ^sham !== 'x) begin
			for (integer i = 0; i < 4; i++) begin
				if (sham >= 4 - i) begin
					assert(shr[i] === 0);
					assert(sshr[i] === a[3]);
				end
			end
		end
	end
endmodule
