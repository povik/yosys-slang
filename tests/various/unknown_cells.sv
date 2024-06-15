module bsg_clkbuf #(parameter width_p=2)
   (input    [width_p-1:0] i
    , output [width_p-1:0] o
    );

    for (genvar j = 0; j < width_p; j++)
      sky130_fd_sc_hd__clkbuf_1 b (.X(o[j]), .A(i[j]));

endmodule
