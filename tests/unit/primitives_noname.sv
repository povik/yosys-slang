module primitives_noname(
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
  input logic buf_b,
  output logic buf_y0,
  output logic buf_y1,
  output logic buf_y2,

  // not
  input logic not_a,
  input logic not_b,
  output logic not_y0,
  output logic not_y1,
  output logic not_y2,

  // pulldown: buffer with constant 0 input
  output logic pulldown_y0,

  // pullup: buffer with constant 1 input
  output logic pullup_y0

  // // bufif0: tribuf with inverted enable
  // input logic bufif0_a,
  // input logic bufif0_en,
  // output logic bufif0_y0,

  // // bufif1: tribuf
  // input logic bufif1_a,
  // input logic bufif1_en,
  // output logic bufif1_y0,

  // // notif0: tribuf with inverted enable and inverted output
  // input logic notif0_a,
  // input logic notif0_en,
  // output logic notif0_y0,

  // // notif1: tribuf with inverted output
  // input logic notif1_a,
  // input logic notif1_en,
  // output logic notif1_y0,

  // // nmos: tribuf
  // input logic nmos_a,
  // input logic nmos_en,
  // output logic nmos_y0,

  // // rnmos: tribuf
  // input logic rnmos_a,
  // input logic rnmos_en,
  // output logic rnmos_y0,

  // // pmos: tribuf with inverted enable
  // input logic pmos_a,
  // input logic pmos_en,
  // output logic pmos_y0,

  // // rpmos: tribuf with inverted enable
  // input logic rpmos_a,
  // input logic rpmos_en,
  // output logic rpmos_y0,

  // // cmos: nmos + pmos
  // input logic cmos_a,
  // input logic cmos_n_en,
  // input logic cmos_p_en,
  // output logic cmos_y0,

  // // rcmos: nmos + pmos
  // input logic rcmos_a,
  // input logic rcmos_n_en,
  // input logic rcmos_p_en,
  // output logic rcmos_y0,

  // // tran: bidirectional wire
  // input tran_a,
  // output tran_y0

  // // rtran: bidirectional wire
  // inout rtran_a,
  // inout rtran_y0,

  // // tranif0: bidirectional tribuf with inverted enable
  // inout tranif0_a,
  // input logic tranif0_en,
  // inout tranif0_y0,

  // // tranif1: bidirectional tribuf
  // inout tranif1_a,
  // input logic tranif1_en,
  // inout tranif1_y0,

  // // rtranif0: bidirectional tribuf with inverted enable
  // inout rtranif0_a,
  // input logic rtranif0_en,
  // inout rtranif0_y0,

  // // rtranif1: bidirectional tribuf
  // inout rtranif1_a,
  // input logic rtranif1_en,
  // inout rtranif1_y0
);

  // ********************************************************
  // Instantiations
  // ********************************************************

  // and
  and (and_y0, and_a);
  and (and_y1, and_a, and_b);
  and (and_y2, and_a, and_b, and_c);

  // or
  or (or_y0, or_a);
  or (or_y1, or_a, or_b);
  or (or_y2, or_a, or_b, or_c);

  // xor
  xor (xor_y0, xor_a);
  xor (xor_y1, xor_a, xor_b);
  xor (xor_y2, xor_a, xor_b, xor_c);

  // xnor
  xnor (xnor_y0, xnor_a);
  xnor (xnor_y1, xnor_a, xnor_b);
  xnor (xnor_y2, xnor_a, xnor_b, xnor_c);

  // nand
  nand (nand_y0, nand_a);
  nand (nand_y1, nand_a, nand_b);
  nand (nand_y2, nand_a, nand_b, nand_c);

  // nor
  nor (nor_y0, nor_a);
  nor (nor_y1, nor_a, nor_b);
  nor (nor_y2, nor_a, nor_b, nor_c);

  // buf
  buf (buf_y0, buf_a);
  buf (buf_y1, buf_y2, buf_b);

  // not
  not (not_y0, not_a);
  not (not_y1, not_y2, not_b);

  // pulldown/pullup
  pulldown (pulldown_y0);
  pullup (pullup_y0);

  // // bufif/notif
  // bufif0 (bufif0_y0, bufif0_a, bufif0_en);
  // bufif1 (bufif1_y0, bufif1_a, bufif1_en);
  // notif0 (notif0_y0, notif0_a, notif0_en);
  // notif1 (notif1_y0, notif1_a, notif1_en);

  // // mos
  // nmos (nmos_y0, nmos_a, nmos_en);
  // rnmos (rnmos_y0, rnmos_a, rnmos_en);
  // pmos (pmos_y0, pmos_a, pmos_en);
  // rpmos (rpmos_y0, rpmos_a, rpmos_en);
  // cmos (cmos_y0, cmos_a, cmos_n_en, cmos_p_en);
  // rcmos (rcmos_y0, rcmos_a, rcmos_n_en, rcmos_p_en);

  // // tran/tranif
  // tran (tran_y0, tran_a);
  // rtran (rtran_y0, rtran_a);
  // tranif0 (tranif0_y0, tranif0_a, tranif0_en);
  // tranif1 (tranif1_y0, tranif1_a, tranif1_en);
  // rtranif0 (rtranif0_y0, rtranif0_a, rtranif0_en);
  // rtranif1 (rtranif1_y0, rtranif1_a, rtranif1_en);


  // ********************************************************
  // Assertions (don't assert anything in presence of x-bits)
  // ********************************************************

  always_comb if (^{and_a, and_b, and_c} !== 'x) begin
    assert(and_y0 == and_a);
    assert(and_y1 == (and_a & and_b));
    assert(and_y2 == (and_a & and_b & and_c));
  end

  always_comb if (^{or_a, or_b, or_c} !== 'x) begin
    assert(or_y0 == or_a);
    assert(or_y1 == (or_a | or_b));
    assert(or_y2 == (or_a | or_b | or_c));
  end

  always_comb if (^{xor_a, xor_b, xor_c} !== 'x) begin  
    assert(xor_y0 == xor_a);
    assert(xor_y1 == (xor_a ^ xor_b));
    assert(xor_y2 == (xor_a ^ xor_b ^ xor_c));
  end

  always_comb if (^{xnor_a, xnor_b, xnor_c} !== 'x) begin
    assert(xnor_y0 == ~xnor_a);
    assert(xnor_y1 == ~(xnor_a ^ xnor_b));
    assert(xnor_y2 == ~(xnor_a ^ xnor_b ^ xnor_c));
  end

  always_comb if (^{nand_a, nand_b, nand_c} !== 'x) begin
    assert(nand_y0 == ~nand_a);
    assert(nand_y1 == ~(nand_a & nand_b));
    assert(nand_y2 == ~(nand_a & nand_b & nand_c));
  end

  always_comb if (^{nor_a, nor_b, nor_c} !== 'x) begin
    assert(nor_y0 == ~nor_a);
    assert(nor_y1 == ~(nor_a | nor_b));
    assert(nor_y2 == ~(nor_a | nor_b | nor_c));
  end

  always_comb if (^{buf_a, buf_b} !== 'x) begin
    assert(buf_y0 == buf_a);
    assert(buf_y1 == buf_b);
    assert(buf_y2 == buf_b);
  end

  always_comb if (^{not_a, not_b} !== 'x) begin
    assert(not_y0 == ~not_a);
    assert(not_y1 == ~not_b);
    assert(not_y2 == ~not_b);
  end

  always_comb if (^{pulldown_y0, pullup_y0} !== 'x) begin
    assert(pulldown_y0 == 1'b0);
    assert(pullup_y0 == 1'b1);
  end

  // always_comb if (^{bufif0_a, bufif0_en} !== 'x) begin
  //   assert(bufif0_y0 == (bufif0_en ? 1'bz : bufif0_a));
  // end

  // always_comb if (^{bufif1_a, bufif1_en} !== 'x) begin
  //   assert(bufif1_y0 == (bufif1_en ? bufif1_a : 1'bz));
  // end

  // always_comb if (^{notif0_a, notif0_en} !== 'x) begin
  //   assert(notif0_y0 == (notif0_en ? 1'bz : ~notif0_a));
  // end
  
  // always_comb if (^{notif1_a, notif1_en} !== 'x) begin
  //   assert(notif1_y0 == (notif1_en ? ~notif1_a : 1'bz));
  // end

  // always_comb if (^{nmos_a, nmos_en} !== 'x) begin
  //   assert(nmos_y0 == (nmos_en ? nmos_a : 1'bz));
  // end

  // always_comb if (^{rnmos_a, rnmos_en} !== 'x) begin
  //   assert(rnmos_y0 == (rnmos_en ? rnmos_a : 1'bz));
  // end

  // always_comb if (^{pmos_a, pmos_en} !== 'x) begin
  //   assert(pmos_y0 == (pmos_en ? 1'bz : pmos_a));
  // end

  // always_comb if (^{rpmos_a, rpmos_en} !== 'x) begin
  //   assert(rpmos_y0 == (rpmos_en ? 1'bz : rpmos_a));
  // end

  // always_comb if (^{cmos_a, cmos_n_en, cmos_p_en} !== 'x) begin
  //   assert(cmos_y0 == ((cmos_n_en || ~cmos_p_en) ? cmos_a : 1'bz));
  // end

  // always_comb if (^{rcmos_a, rcmos_n_en, rcmos_p_en} !== 'x) begin
  //   assert(rcmos_y0 == ((rcmos_n_en || ~rcmos_p_en) ? rcmos_a : 1'bz));
  // end

  // always_comb if (^{tran_a} !== 'x) begin
  //   assert(tran_y0 == tran_a);
  // end

  // always_comb if (^{rtran_a} !== 'x) begin
  //   assert(rtran_y0 == rtran_a);
  // end

  // always_comb if (^{tranif0_a, tranif0_en} !== 'x) begin
  //   assert(tranif0_y0 == (tranif0_en ? 1'bz : tranif0_a));
  // end

  // always_comb if (^{tranif1_a, tranif1_en} !== 'x) begin
  //   assert(tranif1_y0 == (tranif1_en ? tranif1_a : 1'bz));
  // end

  // always_comb if (^{rtranif0_a, rtranif0_en} !== 'x) begin
  //   assert(rtranif0_y0 == (rtranif0_en ? 1'bz : rtranif0_a));
  // end

  // always_comb if (^{rtranif1_a, rtranif1_en} !== 'x) begin
  //   assert(rtranif1_y0 == (rtranif1_en ? rtranif1_a : 1'bz));
  // end

endmodule
