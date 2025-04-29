module test_while(incoming);
  parameter NENTRIES = 8;
  input [NENTRIES-1:0] incoming;
  logic [$clog2(NENTRIES)-1:0] idx;
  logic sample;
  always_comb begin
    idx = '0;
    sample = incoming[idx];
    while (!sample && idx != NENTRIES - 1) begin
      idx += 1'b1;
      sample = incoming[idx];
    end
  end
  always_comb begin
    if (^incoming !== 'x) begin
      for (integer i = 0; i < NENTRIES - 1; i++) begin
        assert(idx != i || incoming[i]);
        assert(idx <= i || ~incoming[i]);
      end
    end
  end
endmodule

// Not supported: cannot be statically unrolled
/*
module test_while_return1(incoming);
  parameter NENTRIES = 8;
  input [NENTRIES-1:0] incoming;

  function [$clog2(NENTRIES)-1:0] ffs();
    logic [$clog2(NENTRIES)-1:0] idx;
    idx = '0;
    while (idx != NENTRIES - 1) begin
      if (incoming[idx])
        return idx;
      idx += 1'b1;
    end
    return idx;
  endfunction

  logic [$clog2(NENTRIES)-1:0] idx;
  always_comb begin
    idx = ffs();
  end
  always_comb begin
    if (^incoming !== 'x) begin
      for (integer i = 0; i < NENTRIES - 1; i++) begin
        assert(idx != i || incoming[i]);
        assert(idx <= i || ~incoming[i]);
      end
    end
  end
endmodule
*/

module test_while_return2(incoming);
  parameter NENTRIES = 8;
  input [NENTRIES-1:0] incoming;

  function [$clog2(NENTRIES)-1:0] ffs();
    logic [$clog2(NENTRIES)-1:0] idx;
    idx = '0;
    while (idx != NENTRIES - 1) begin
      idx += 1'b1;
      if (incoming[idx - 1])
        return idx - 1;
    end
    return idx;
  endfunction

  logic [$clog2(NENTRIES)-1:0] idx;
  always_comb begin
    idx = ffs();
  end
  always_comb begin
    if (^incoming !== 'x) begin
      for (integer i = 0; i < NENTRIES - 1; i++) begin
        assert(idx != i || incoming[i]);
        assert(idx <= i || ~incoming[i]);
      end
    end
  end
endmodule
