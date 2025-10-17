// Test: Local Variables in Properties and Sequences
// Category: Advanced property features
// Expected: Should fail - local variables in properties not supported

module local_variables_test(
    input logic clk,
    input logic valid,
    input logic out_valid,
    input logic [7:0] data,
    input logic [7:0] out_data,
    input logic [15:0] addr,
    input logic write_en,
    input logic read_en
);

    // Test 1: Local variable to capture data
    property p_data_capture;
        logic [7:0] saved_data;
        @(posedge clk) (valid, saved_data = data) |=>
            (out_valid && (out_data == saved_data));
    endproperty
    assert property (p_data_capture);

    // Test 2: Multiple local variables
    property p_multi_locals;
        logic [7:0] saved_data;
        logic [15:0] saved_addr;
        @(posedge clk) (write_en, saved_data = data, saved_addr = addr) ##[1:5]
            (read_en && (addr == saved_addr)) |-> (out_data == saved_data);
    endproperty
    assert property (p_multi_locals);

    // Test 3: Local variable with calculation
    property p_local_calc;
        int saved_sum;
        @(posedge clk) (valid, saved_sum = data + out_data) |=>
            (out_data == saved_sum);
    endproperty
    assert property (p_local_calc);

    // Test 4: Local variable in sequence
    sequence s_with_local;
        logic [7:0] temp;
        @(posedge clk) (valid, temp = data) ##1 (out_data == temp);
    endsequence
    assert property (s_with_local);

    // Test 5: Local variable scope across delays
    property p_local_scope;
        logic [7:0] saved;
        @(posedge clk) (valid, saved = data) ##3 (out_data == saved + 1);
    endproperty
    assert property (p_local_scope);

endmodule
