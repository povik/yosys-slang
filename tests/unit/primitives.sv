module primitives(
  // and
  input logic and_a,
  input logic and_b,
  input logic and_c,
  output logic and_y0,
  output logic and_y1,
  output logic and_y2,

  // or
  input logic or_a,
  input logic or_b,
  input logic or_c,
  output logic or_y0,
  output logic or_y1,
  output logic or_y2,

  // xor
  input logic xor_a,
  input logic xor_b,
  input logic xor_c,
  output logic xor_y0,
  output logic xor_y1,
  output logic xor_y2,

  // xnor
  input logic xnor_a,
  input logic xnor_b,
  input logic xnor_c,
  output logic xnor_y0,
  output logic xnor_y1,
  output logic xnor_y2,

  // nand
  input logic nand_a,
  input logic nand_b,
  input logic nand_c,
  output logic nand_y0,
  output logic nand_y1,
  output logic nand_y2,

  // nor
  input logic nor_a,
  input logic nor_b,
  input logic nor_c,
  output logic nor_y0,
  output logic nor_y1,
  output logic nor_y2,

  // buf
  input logic buf_a,
  output logic buf_y0,
  output logic buf_y1,
  output logic buf_y2,

  // not
  input logic not_a,
  output logic not_y0,
  output logic not_y1,
  output logic not_y2,

  // pulldown: buffer with constant 0 input
  output logic pulldown_y0,

  // pullup: buffer with constant 1 input
  output logic pullup_y0,

  // bufif0: tribuf with inverted enable
  input logic bufif0_a,
  input logic bufif0_en,
  output logic bufif0_y0,

  // bufif1: tribuf
  input logic bufif1_a,
  input logic bufif1_en,
  output logic bufif1_y0,

  // notif0: tribuf with inverted enable and inverted output
  input logic notif0_a,
  input logic notif0_en,
  output logic notif0_y0,

  // notif1: tribuf with inverted output
  input logic notif1_a,
  input logic notif1_en,
  output logic notif1_y0,

  // nmos: tribuf
  input logic nmos_a,
  input logic nmos_en,
  output logic nmos_y0,

  // rnmos: tribuf
  input logic rnmos_a,
  input logic rnmos_en,
  output logic rnmos_y0,

  // pmos: tribuf with inverted enable
  input logic pmos_a,
  input logic pmos_en,
  output logic pmos_y0,

  // rpmos: tribuf with inverted enable
  input logic rpmos_a,
  input logic rpmos_en,
  output logic rpmos_y0,

  // cmos: nmos + pmos
  input logic cmos_a,
  input logic cmos_n_en,
  input logic cmos_p_en,
  output logic cmos_y0,

  // rcmos: nmos + pmos
  input logic rcmos_a,
  input logic rcmos_n_en,
  input logic rcmos_p_en,
  output logic rcmos_y0

  // // tran: bidirectional wire
  // inout logic tran_a,
  // inout logic tran_y0,

  // // rtran: bidirectional wire
  // inout logic rtran_a,
  // inout logic rtran_y0,

  // // tranif0: bidirectional tribuf with inverted enable
  // inout logic tranif0_a,
  // input logic tranif0_en,
  // inout logic tranif0_y0,

  // // tranif1: bidirectional tribuf
  // inout logic tranif1_a,
  // input logic tranif1_en,
  // inout logic tranif1_y0,

  // // rtranif0: bidirectional tribuf with inverted enable
  // inout logic rtranif0_a,
  // input logic rtranif0_en,
  // inout logic rtranif0_y0,

  // // rtranif1: bidirectional tribuf
  // inout logic rtranif1_a,
  // input logic rtranif1_en,
  // inout logic rtranif1_y0
);

  // and
  and and_inst0(and_y0, and_a);
  and and_inst1(and_y1, and_a, and_b);
  and and_inst2(and_y2, and_a, and_b, and_c);

  // or
  or or_inst0(or_y0, or_a);
  or or_inst1(or_y1, or_a, or_b);
  or or_inst2(or_y2, or_a, or_b, or_c);

  // xor
  xor xor_inst0(xor_y0, xor_a);
  xor xor_inst1(xor_y1, xor_a, xor_b);
  xor xor_inst2(xor_y2, xor_a, xor_b, xor_c);

  // xnor
  xnor xnor_inst0(xnor_y0, xnor_a);
  xnor xnor_inst1(xnor_y1, xnor_a, xnor_b);
  xnor xnor_inst2(xnor_y2, xnor_a, xnor_b, xnor_c);

  // nand
  nand nand_inst0(nand_y0, nand_a);
  nand nand_inst1(nand_y1, nand_a, nand_b);
  nand nand_inst2(nand_y2, nand_a, nand_b, nand_c);

  // nor
  nor nor_inst0(nor_y0, nor_a);
  nor nor_inst1(nor_y1, nor_a, nor_b);
  nor nor_inst2(nor_y2, nor_a, nor_b, nor_c);

  // buf
  buf buf_inst0(buf_y0, buf_a);
  buf buf_inst1(buf_y1, buf_y2, buf_a);

  // not
  not not_inst0(not_y0, not_a);
  not not_inst1(not_y1, not_y2, not_a);

  // pulldown/pullup
  pulldown pulldown_inst0(pulldown_y0);
  pullup pullup_inst0(pullup_y0);

  // bufif/notif
  bufif0 bufif0_inst0(bufif0_y0, bufif0_a, bufif0_en);
  bufif1 bufif1_inst0(bufif1_y0, bufif1_a, bufif1_en);
  notif0 notif0_inst0(notif0_y0, notif0_a, notif0_en);
  notif1 notif1_inst0(notif1_y0, notif1_a, notif1_en);

  // mos
  nmos nmos_inst0(nmos_y0, nmos_a, nmos_en);
  rnmos rnmos_inst0(rnmos_y0, rnmos_a, rnmos_en);
  pmos pmos_inst0(pmos_y0, pmos_a, pmos_en);
  rpmos rpmos_inst0(rpmos_y0, rpmos_a, rpmos_en);
  cmos cmos_inst0(cmos_y0, cmos_a, cmos_n_en, cmos_p_en);
  rcmos rcmos_inst0(rcmos_y0, rcmos_a, rcmos_n_en, rcmos_p_en);

  // // tran/tranif
  // tran tran_inst0(tran_y0, tran_a);
  // rtran rtran_inst0(rtran_y0, rtran_a);
  // tranif0 tranif0_inst0(tranif0_y0, tranif0_a, tranif0_en);
  // tranif1 tranif1_inst0(tranif1_y0, tranif1_a, tranif1_en);
  // rtranif0 rtranif0_inst0(rtranif0_y0, rtranif0_a, rtranif0_en);
  // rtranif1 rtranif1_inst0(rtranif1_y0, rtranif1_a, rtranif1_en);

endmodule
