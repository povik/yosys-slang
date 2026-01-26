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

module foreach_array_sum_1d;

    reg array1d[4] ='{0, 0, 0, 0};
    int sum = 0;

    always_comb begin
        foreach (array1d[i]) begin
            sum += array1d[i];
        end
    end

endmodule


module foreach_array_sum_2d;

    reg array2d[3][4] ='{'{0, 0, 0, 0},
                          '{0, 0, 0, 0},
                          '{0, 0, 0, 1}};
    int sum = 0;

    always_comb begin
        foreach (array2d[i, j]) begin
            sum += array2d[i][j];
        end
    end

endmodule

module foreach_array_sum_3d;

    reg array3d[2][3][4] ='{ '{'{0, 0, 0, 0},
                          '{0, 0, 0, 0},
                          '{0, 0, 0, 1}}, '{'{0, 0, 0, 0},
                          '{0, 0, 0, 0},
                          '{0, 0, 0, 1}}};
    int sum = 0;

    always_comb begin
        foreach (array3d[i, j, k]) begin
            sum += array3d[i][j][k];
        end
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
