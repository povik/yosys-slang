module sm1;
endmodule

module sm2;
	sm1 inst1();
endmodule

module top1;
	sm2 inst2();
endmodule

module top2;
	sm1 inst3();
endmodule

module top3;
endmodule
