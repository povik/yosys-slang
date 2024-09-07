module top();

logic [31:0]data[4] = '{ 4 { 32'hdeadbeef } };

logic [31:0]a, b, c, d;

// should allow mismatched size
//assign '{ {a[15:0], b[31:16]}, { b[15:0], a[31:24] }, c, d } = data;

assign '{ {a[15:0], b[31:16]}, { b[15:0], a[31:16] }, c, d } = data;

endmodule
