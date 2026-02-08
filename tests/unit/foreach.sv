module multi_array_sum;
  int array[2][3][4]  ='{ '{'{0, 0, 0, 0},
                          '{0, 0, 0, 0},
                          '{0, 0, 0, 1}}, '{'{0, 0, 0, 0},
                          '{0, 0, 0, 0},
                          '{0, 0, 0, 1}}};
  int array1[2][3][4]  ='{ '{'{0, 0, 0, 0},
                          '{0, 0, 0, 0},
                          '{0, 0, 0, 1}}, '{'{0, 0, 0, 0},
                          '{0, 0, 0, 0},
                          '{0, 0, 0, 1}}};
  int sum;
    localparam O = 32;
    localparam I = 16;

  always_comb begin
    foreach (array[i, j, k])
        array1[i][j][k] += {{O - I-1{array[i][j][k][I]}}, array[i][j][k]};
  end
endmodule

module foreach_array_sum_1d(array1d);
    input reg [1:0] array1d[4];
    int sum1, sum2;

    always_comb begin
        sum1 = 0;
        foreach (array1d[i]) begin
            sum1 += array1d[i];
        end
    end

    always_comb begin
        sum2 = 0;
        for (int i = 0; i < 4; i++)
            sum2 += array1d[i];
        assert(sum1 === sum2);
    end
endmodule

module foreach_array_sum_2d_with_1_iter_dim(array2d);
    input reg array2d[3][4];
    int sum1, sum2;

    always_comb begin
        sum1 = 0;
        foreach (array2d[i, ]) begin
            sum1 = (sum1 << 1) + array2d[i][1];
        end
    end

    always_comb begin
        sum2 = 0;
        for (int i = 0; i < 3; i++)
            sum2 = (sum2 << 1) + array2d[i][1];
        assert(sum1 === sum2);
    end
endmodule

module foreach_array_sum_2d_packed_unpacked(array2d);
    input reg [3:0] array2d[3];
    int sum1, sum2;

    always_comb begin
        sum1 = 0;
        foreach (array2d[i, j]) begin
            sum1 = (sum1 << 1) + array2d[i][j];
        end
    end

    always_comb begin
        sum2 = 0;
        for (int i = 0; i < 3; i++)
            for (int j = 3; j >= 0; j--)
                sum2 = (sum2 << 1) + array2d[i][j];
        assert(sum1 === sum2);
    end
endmodule

module foreach_array_sum_2d(array2d);
    input reg array2d[3][4];
    int sum1, sum2;

    always_comb begin
        sum1 = 0;
        foreach (array2d[i, j]) begin
            sum1 = (sum1 << 1) + array2d[i][j];
        end
    end

    always_comb begin
        sum2 = 0;
        for (int i = 0; i < 3; i++)
            for (int j = 0; j < 4; j++)
                sum2 = (sum2 << 1) + array2d[i][j];
        assert(sum1 === sum2);
    end
endmodule

module foreach_array_sum_2d_with_break(array2d);
    input reg array2d[3][4];
    int sum1, sum2;

    always_comb begin
        sum1 = 0;
        foreach (array2d[i, j]) begin
            sum1 = (sum1 << 1) + array2d[i][j];
            if (i == 2 && j == 1) begin
                break;
            end
        end
    end

    always_comb begin
        sum2 = 0;
        for (int i = 0; i < 2; i++) begin
            for (int j = 0; j < 4; j++) begin
                sum2 = (sum2 << 1) + array2d[i][j];
            end
        end
        sum2 = (sum2 << 1) + array2d[2][0];
        sum2 = (sum2 << 1) + array2d[2][1];
        assert(sum1 === sum2);
    end

endmodule

module foreach_array_sum_3d(array3d);
    input reg array3d[2][3:0][3];
    int sum1, sum2;

    always_comb begin
        sum1 = 0;
        foreach (array3d[i, j, k]) begin
            sum1 = (sum1 << 1) + array3d[i][j][k];
        end
    end

    always_comb begin
        sum2 = 0;
        for (int i = 0; i < 2; i++) begin
            for (int j = 3; j >= 0; j--) begin
                for (int k = 0; k < 3; k++) begin
                    sum2 = (sum2 << 1) + array3d[i][j][k];
                end
            end
        end
        assert(sum1 === sum2);
    end
endmodule

module load_and_store;
        int array[5] = '{1, 2, 3, 4, 5};
        int sum = 0;

        always_comb begin
                foreach (array[l_index]) begin
                        array[l_index] += 1;
                        sum += array[l_index];
                end
        end
endmodule
