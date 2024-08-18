module top(input logic [1:0] a, input logic sel);
	task incr(input logic [1:0] x, output logic [1:0] xx);
		xx = x + 1;
	endtask

	logic [1:0] arr[1:0];
	always_comb begin
		arr = {0, 0};
		incr(a, arr[sel]);
	end

	always_comb begin
		if (sel !== 'x) begin
			logic [1:0] a1;
			a1 = a + 1;
			assert(arr[sel] === a1);
			assert(arr[~sel] === '0);
		end
	end
endmodule
