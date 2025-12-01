module countones_test #(parameter WIDTH = 8) (input logic [WIDTH-1:0] val);
    function automatic integer reference_count(logic [WIDTH-1:0] v);
        reference_count = 0;
        for (int i = 0; i < WIDTH; i++)
            reference_count += v[i];
    endfunction

    always_comb if (^val !== 'x) begin
        assert($countones(val) == reference_count(val));
    end
endmodule

module countones_1bit(input logic val);
    countones_test #(.WIDTH(1)) t(.val(val));
endmodule

module countones_8bit(input logic [7:0] val);
    countones_test #(.WIDTH(8)) t(.val(val));
endmodule

module countones_32bit(input logic [31:0] val);
    countones_test #(.WIDTH(32)) t(.val(val));
endmodule

module countones_constants;
    always_comb begin
        assert($countones(8'b00000000) == 0);
        assert($countones(8'b11111111) == 8);
        assert($countones(1'b1) == 1);
        assert($countones(16'hFFFF) == 16);
        assert($countones(-2'b1) == 2);
        assert($countones(-4'b111) == 2);
    end
endmodule // countones_constants
