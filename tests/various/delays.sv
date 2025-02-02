module top(input wire clk);

wire #10 a;
wire #(10+0) b;
wire #(10+0, 1+1) c;
wire #(10+0, 1+1, 2+2) d;

assign #10 a = b;
assign #(10+1) b = c;

reg ra, rb;
always @(posedge clk) begin
    #1;
    #1 ra <= a;
    rb <= #1 a;
end

logic la, lb;
always @(*) begin
    #10;
    #10 la = a;
    lb = #10 a;
end

logic lc, ld;
initial begin
    #10;
    #10 lc = ra;
    ld = #10 ra;
end

int foo;

initial begin
    #10 foo = 32'h0;
    $display(foo);
    #10 foo = 32'hdeadbeef;
    $display(foo);
end


endmodule
