module top;
// pragma translate_off
initial $error("1");
// pragma translate_on

//pragma synthesis_off
initial $error("2");
// pragma synthesis_on

// pragma synthesis_off
// this one should not get picked up: pragma synthesis_on
// this one neither:
//pragma synthesis_onff
initial $error("3");
// pragma synthesis_on
endmodule
