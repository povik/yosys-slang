// Test: Abort Operators (accept_on, reject_on)
// Category: Early property termination
// Expected: Should pass after implementation

module abort_operators_test(
    input logic clk,
    input logic rst_n,
    input logic req,
    input logic ack,
    input logic abort_sig,
    input logic error,
    input logic timeout
);

    // Test 1: Accept on condition
    property p_accept_on;
        @(posedge clk) disable iff (!rst_n)
            accept_on (ack) (req ##[1:10] ack);
    endproperty
    assert property (p_accept_on);

    // Test 2: Reject on condition
    property p_reject_on;
        @(posedge clk) disable iff (!rst_n)
            reject_on (error) (req |-> ##[1:5] ack);
    endproperty
    assert property (p_reject_on);

    // Test 3: Sync accept on
    property p_sync_accept_on;
        @(posedge clk) disable iff (!rst_n)
            sync_accept_on (ack) (req ##1 req ##1 req);
    endproperty
    assert property (p_sync_accept_on);

    // Test 4: Sync reject on
    property p_sync_reject_on;
        @(posedge clk) disable iff (!rst_n)
            sync_reject_on (timeout) (req |=> ##[1:20] ack);
    endproperty
    assert property (p_sync_reject_on);

endmodule

