// Test: Expect Statement
// Category: Procedural assertion with blocking behavior
// Expected: Should fail - expect statement not supported

module expect_statement_test(
    input logic clk,
    input logic start,
    input logic req,
    input logic ack,
    input logic done,
    input logic [7:0] data
);

    // Test 1: Basic expect with property
    initial begin
        wait(start);
        expect (@(posedge clk) req ##[1:5] ack)
            $display("Handshake OK");
        else
            $error("Handshake failed");
    end

    // Test 2: Expect with sequence
    initial begin
        wait(start);
        expect (@(posedge clk) req ##1 ack ##1 done)
            $display("Full sequence completed");
        else
            $error("Sequence failed");
    end

    // Test 3: Expect in always block
    always @(posedge start) begin
        expect (@(posedge clk) req |=> ack)
            $display("Request acknowledged");
        else
            $error("No acknowledgment");
    end

    // Test 4: Nested expect - INVALID per SV-2023 spec section 16.14.6
    // "An expect statement shall not be used in an action block of a concurrent assertion"
    // Commenting out as this is intentionally invalid SystemVerilog
    // initial begin
    //     wait(start);
    //     expect (@(posedge clk) req)
    //         expect (@(posedge clk) ##[1:3] ack)
    //             $display("Nested expect passed");
    // end

    // Test 5: Expect with complex property
    initial begin
        wait(start);
        expect (@(posedge clk) req |-> ##[1:10] (ack && !done))
            $display("Complex property satisfied");
        else
            $fatal("Property violation");
    end

endmodule
