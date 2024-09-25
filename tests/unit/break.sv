module priority_encoder #(
    parameter integer INPUT_WIDTH = 8
) (
    input logic [INPUT_WIDTH-1:0] bits,
    output logic [$clog2(INPUT_WIDTH)-1:0] encoded
);
    always_comb begin: for_loop_priority_encoder
        encoded = 1'b0;
        for (integer unsigned i = 0; i < INPUT_WIDTH; i++) begin
            if (bits[i]) begin
                encoded = i;
                break;
            end
        end
    end

    always_comb begin
        if (bits == 'd0 || ^bits === 1'bx) begin
        end else begin
            logic [INPUT_WIDTH-1:0] masked;

            assert(bits[encoded]);
            masked = bits & ~(-1 << encoded);
            assert(masked == '0);
        end
    end
endmodule

module test_break00 (bits, encoded);
    input  logic[2:0] bits;
    output logic[1:0] encoded;
    priority_encoder #(3) test_0_inst (.*);
endmodule

module test_break01 (bits, encoded);
    input  logic[1:0] bits;
    output logic[0:0] encoded;
    priority_encoder #(2) test_1_inst (.*);
endmodule

module test_break02 (bits, encoded);
    input  logic[4:0] bits;
    output logic[2:0] encoded;
    priority_encoder #(5) test_2_inst (.*);
endmodule

module test_break03 (bits, encoded);
    input  logic[7:0] bits;
    output logic[2:0] encoded;
    priority_encoder #(8) test_3_inst (.*);
endmodule

module priority_encoder2 #(
    parameter integer INPUT_WIDTH = 8
) (
    input logic [INPUT_WIDTH-1:0] bits,
    output logic [$clog2(INPUT_WIDTH)-1:0] encoded
);
    always_comb begin: for_loop_priority_encoder
        integer i = 0;
        encoded = 1'b0;
        for (i = 0; i < INPUT_WIDTH; i++) begin
            if (bits[i]) begin
                break;
            end
        end
        encoded = i;
    end

    always_comb begin
        if (bits == 'd0 || ^bits === 1'bx) begin
        end else begin
            logic [INPUT_WIDTH-1:0] masked;

            assert(bits[encoded]);
            masked = bits & ~(-1 << encoded);
            assert(masked == '0);
        end
    end
endmodule

module test_break04 (bits, encoded);
    input  logic[2:0] bits;
    output logic[1:0] encoded;
    priority_encoder2 #(3) test_4_inst (.*);
endmodule

module test_break05 (bits, encoded);
    input  logic[1:0] bits;
    output logic[0:0] encoded;
    priority_encoder2 #(2) test_5_inst (.*);
endmodule

module test_break06 (bits, encoded);
    input  logic[4:0] bits;
    output logic[2:0] encoded;
    priority_encoder2 #(5) test_6_inst (.*);
endmodule

module test_break07 (bits, encoded);
    input  logic[7:0] bits;
    output logic[2:0] encoded;
    priority_encoder2 #(8) test_7_inst (.*);
endmodule

module test_break08;
    wire tie_down = 0;
    logic out;

    always_comb begin
        for (int i = 0; i < 1; i++) begin
            out = 1;
            if (!tie_down)
                break;
            out = 0;
        end
    end

    always_comb assert(out == 1);
endmodule

module test_break09(logic [2:0] span);
    logic [7:0] mask1, mask2;

    always_comb begin
        mask1 = 0;
        for (int i = 0; i < span && i < 8; i++)
            mask1[i] = 1;
    end

    always_comb begin
        mask2 = 0;
        for (int i = 0; i < 8; i++)
            if (i < span)
                mask2[i] = 1;
    end

    always_comb begin
        if (^span !== 'x)
            assert(mask1 === mask2);
    end
endmodule

module test_break10(logic [2:0] span);
    logic [7:0] mask1, mask2;

    always_comb begin
        mask1 = 0;
        for (int i = 0; i < span; i++)
            mask1[i] = 1;
    end

    always_comb begin
        mask2 = 0;
        for (int i = 0; i < 8; i++)
            if (i < span)
                mask2[i] = 1;
    end

    always_comb begin
        if (^span !== 'x)
            assert(mask1 === mask2);
    end
endmodule
