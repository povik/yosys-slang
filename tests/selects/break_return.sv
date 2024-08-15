module test_simple_return();
	function [7:0] f();
		return 8'hb3;
	endfunction

	always_comb begin
		assert(f() == 8'hb3);
	end
endmodule

module test_return_w_followup();
	function [7:0] f();
		return 8'hb3;
		return 8'h72;
	endfunction

	always_comb begin
		assert(f() == 8'hb3);
	end
endmodule

module test_return_from_loop();
	function [7:0] f();
        for (integer unsigned i = 0; i < 10; i++) begin
            if (i > 5)
            	return i * 3;
        end
	endfunction

	always_comb begin
		assert(f() == 18);
	end
endmodule

module test_void_return(input [1:0] a);
	function void f([1:0] a);
		if (a > 1)
			return;
		else
			return;
	endfunction

	always_comb begin
		f(a);
	end
endmodule

module test_nested_loop_break(input [1:0] a);
	function [3:0] f([3:0] a);
		logic [2:0] x, y;
		for (x = 0; x < 4; x++) begin
            for (y = 0; y < 4; y++) begin
	            if (~y[1:0] == a[1:0])
	            	break;
	        end
	        if (~x[1:0] == a[3:2])
	        	break;
        end
        return {x[1:0], y[1:0]};
	endfunction

	always_comb begin
		if (^a !== 'x)
			assert(f(a) == ~a);
	end
endmodule
