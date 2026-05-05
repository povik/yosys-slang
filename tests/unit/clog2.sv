// Test $clog2 lowering to RTLIL
module clog2_constants;
    always_comb begin
        assert($clog2(0) == 0);
        assert($clog2(1) == 0);
        assert($clog2(2) == 1);
        assert($clog2(3) == 2);
        assert($clog2(4) == 2);
        assert($clog2(5) == 3);
        assert($clog2(8) == 3);
        assert($clog2(9) == 4);
        assert($clog2(16) == 4);
        assert($clog2(255) == 8);
        assert($clog2(256) == 8);
        assert($clog2(257) == 9);
    end
endmodule

// Test with a variable input, verifying against a reference implementation
module clog2_test #(parameter WIDTH = 8) (input logic [WIDTH-1:0] val);
    function automatic integer reference_clog2(logic [WIDTH-1:0] n);
        integer v;
        reference_clog2 = 0;
        if (n <= 1) return 0;
        v = n - 1;
        for (int i = 0; i < WIDTH; i++)
            if (v[i]) reference_clog2 = i + 1;
    endfunction

    always_comb if (^val !== 'x) begin
        assert($clog2(val) == reference_clog2(val));
    end
endmodule

module clog2_8bit(input logic [7:0] val);
    clog2_test #(.WIDTH(8)) t(.val(val));
endmodule
