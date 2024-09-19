module top;
logic [7:0] m;
always @(*) begin
	m[4-:2] <= 0;
end
endmodule
