// Test: Complex Real-World SVA Scenarios
// Category: Comprehensive examples combining multiple features
// Expected: Should fail - demonstrates realistic formal verification scenarios

module complex_sva_scenarios(
    input logic clk,
    input logic rst_n,
    input logic req,
    input logic gnt,
    input logic [3:0] arb_req,
    input logic [3:0] arb_gnt,
    input logic write_en,
    input logic read_en,
    input logic [31:0] addr,
    input logic [31:0] data_in,
    input logic [31:0] data_out,
    input logic fifo_push,
    input logic fifo_pop,
    input logic fifo_empty,
    input logic fifo_full,
    input logic [7:0] fifo_count
);

    // Scenario 1: Round-robin arbiter fairness
    // If a request is asserted, it must be granted within 4 cycles
    property p_arbiter_fairness;
        @(posedge clk) disable iff (!rst_n)
            arb_req[0] |-> ##[1:4] arb_gnt[0];
    endproperty
    assert property (p_arbiter_fairness);

    // Scenario 2: Memory write-read coherency
    // Data written to an address should be readable
    property p_mem_coherency;
        logic [31:0] saved_addr, saved_data;
        @(posedge clk) disable iff (!rst_n)
            (write_en, saved_addr = addr, saved_data = data_in) ##[1:5]
            (read_en && (addr == saved_addr)) |-> (data_out == saved_data);
    endproperty
    assert property (p_mem_coherency);

    // Scenario 3: Mutex guarantee
    // Request and grant should never overlap for different requesters
    property p_mutex;
        @(posedge clk) disable iff (!rst_n)
            |arb_gnt |-> $onehot(arb_gnt);
    endproperty
    assert property (p_mutex);

    // Scenario 4: FIFO behavior
    // Push increments count, pop decrements count
    property p_fifo_push_inc;
        @(posedge clk) disable iff (!rst_n)
            (fifo_push && !fifo_full && !fifo_pop) |=>
            (fifo_count == $past(fifo_count) + 1);
    endproperty
    assert property (p_fifo_push_inc);

    property p_fifo_pop_dec;
        @(posedge clk) disable iff (!rst_n)
            (fifo_pop && !fifo_empty && !fifo_push) |=>
            (fifo_count == $past(fifo_count) - 1);
    endproperty
    assert property (p_fifo_pop_dec);

    // Scenario 5: FIFO full/empty flags
    property p_fifo_empty_check;
        @(posedge clk) disable iff (!rst_n)
            fifo_empty |-> (fifo_count == 0);
    endproperty
    assert property (p_fifo_empty_check);

    property p_fifo_full_check;
        @(posedge clk) disable iff (!rst_n)
            fifo_full |-> (fifo_count == 8'd255);
    endproperty
    assert property (p_fifo_full_check);

    // Scenario 6: Request-grant protocol
    // Request must stay asserted until grant
    property p_req_stable_until_gnt;
        @(posedge clk) disable iff (!rst_n)
            $rose(req) |-> req throughout (##[0:$] gnt);
    endproperty
    assert property (p_req_stable_until_gnt);

    // Scenario 7: Handshake with timeout
    // Acknowledgment must come within reasonable time
    property p_handshake_timeout;
        @(posedge clk) disable iff (!rst_n)
            req |-> ##[1:16] gnt;
    endproperty
    assert property (p_handshake_timeout);

    // Scenario 8: No back-to-back grants without request
    property p_no_spurious_grant;
        @(posedge clk) disable iff (!rst_n)
            gnt && !req |=> !gnt;
    endproperty
    assert property (p_no_spurious_grant);

    // Scenario 9: Reset behavior
    // After reset, all grants should be deasserted
    property p_reset_clears_grants;
        @(posedge clk) $fell(rst_n) |=> (arb_gnt == 4'b0000);
    endproperty
    assert property (p_reset_clears_grants);

    // Scenario 10: Coverage - detect interesting corner cases
    cover property (
        @(posedge clk) (arb_req == 4'b1111) ##1 (arb_gnt != 4'b0000)
    );

    cover property (
        @(posedge clk) fifo_push ##1 fifo_full
    );

endmodule
