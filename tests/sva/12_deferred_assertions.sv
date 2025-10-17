// Test: Deferred Assertions (#0 and final)
// Category: Immediate assertion timing control
// Expected: Should fail - deferred assertions not supported

module deferred_assertions_test(
    input logic clk,
    input logic data_valid,
    input logic [7:0] data,
    input logic no_error,
    input logic req,
    input logic ack
);

    // Test 1: Deferred immediate assertion - #0 (Observed region)
    always_comb begin
        a_deferred_observed: assert #0 (data_valid);
    end

    // Test 2: Deferred immediate assertion - final (Postponed region)
    always_comb begin
        a_deferred_postponed: assert final (no_error);
    end

    // Test 3: Multiple deferred assertions in same block
    always_comb begin
        assert #0 (data_valid);
        assert #0 (!no_error || (data != 8'h00));
    end

    // Test 4: Deferred assume
    always_comb begin
        assume #0 (req ? ack : 1'b1);
    end

    // Test 5: Deferred cover
    always_comb begin
        cover #0 (data_valid && (data == 8'hFF));
    end

    // Test 6: Final assertion in procedural block
    always @(posedge clk) begin
        if (data_valid)
            assert final (data inside {[0:127]});
    end

    // Test 7: Mixing immediate and deferred
    always_comb begin
        assert (data_valid);        // immediate
        assert #0 (!no_error);      // deferred observed
        assert final (req == ack);  // deferred postponed
    end

endmodule
