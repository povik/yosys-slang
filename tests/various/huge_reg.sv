module top;

localparam ADDRW = 14;
logic clk;
logic[ADDRW-1:0] aaddr;

reg [32-1:0] mem [2**ADDRW-1:0];

function automatic void some_helper;
	mem[0][0] <= '0;
endfunction

always_ff @(posedge clk) begin
    some_helper();
    mem[aaddr][0] <= '0;
end

endmodule
