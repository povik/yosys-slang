// Test: Intersect and First_match Operators
// Category: Advanced sequence operators
// Expected: Should fail - intersect and first_match not supported

module intersect_firstmatch_test(
    input logic clk,
    input logic a, b, c, d,
    input logic req,
    input logic ack,
    input logic start
);

    // Test 1: Sequence intersect
    sequence s1;
        @(posedge clk) a ##1 b;
    endsequence

    sequence s2;
        @(posedge clk) c ##1 d;
    endsequence

    property p_intersect;
        @(posedge clk) (s1 intersect s2);
        // Both sequences must match simultaneously
    endproperty
    assert property (p_intersect);

    // Test 2: First_match with unbounded delay
    property p_firstmatch_unbounded;
        @(posedge clk) first_match(req ##[1:$] ack);
        // Matches on first occurrence of ack after req
    endproperty
    assert property (p_firstmatch_unbounded);

    // Test 3: First_match with range
    property p_firstmatch_range;
        @(posedge clk) first_match(start ##[3:10] req);
    endproperty
    assert property (p_firstmatch_range);

    // Test 4: First_match in implication
    property p_firstmatch_impl;
        @(posedge clk) start |-> first_match(req ##[1:$] ack);
    endproperty
    assert property (p_firstmatch_impl);

    // Test 5: Intersect with repetition
    sequence s3;
        @(posedge clk) a[*2];
    endsequence

    sequence s4;
        @(posedge clk) b ##1 c;
    endsequence

    property p_intersect_rep;
        @(posedge clk) (s3 intersect s4);
    endproperty
    assert property (p_intersect_rep);

endmodule
