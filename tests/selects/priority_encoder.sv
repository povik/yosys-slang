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
            integer previousSet = 0;
            for (integer unsigned i = 0; i < INPUT_WIDTH; i++) begin
                if (bits[i]) begin
                    if (previousSet == 0) begin
                        assert(encoded == i);
                        previousSet = 1;
                    end
                end
            end

        end
    end
endmodule

module test_0 (bits, encoded);
    input  logic[2:0] bits;
    output logic[1:0] encoded;
    priority_encoder #(3) test_0_inst (.*);
endmodule
