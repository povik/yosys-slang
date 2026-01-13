module init01_submod (
    output reg a=0,
    output reg b=1
);
endmodule

module init01();
    logic a, b;
    init01_submod sm(.a, .b);
    always_comb begin
        assert(a === 0);
        assert(b === 1);
    end
endmodule
