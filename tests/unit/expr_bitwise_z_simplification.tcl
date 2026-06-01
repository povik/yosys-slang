yosys -import

set sv_source {
module expr_bitwise_z_simplification(
	input logic dynamic_bit
);
	wire [1:0] and_equal = {1'bz, dynamic_bit} & {1'bz, dynamic_bit};
	wire [1:0] or_equal = {1'bz, dynamic_bit} | {1'bz, dynamic_bit};
	wire [1:0] and_one_left = {1'bz, dynamic_bit} & 2'b11;
	wire [1:0] and_one_right = 2'b11 & {1'bz, dynamic_bit};
	wire [1:0] or_zero_left = {1'bz, dynamic_bit} | 2'b00;
	wire [1:0] or_zero_right = 2'b00 | {1'bz, dynamic_bit};
endmodule
}

set sv_file [file join /tmp "yosys_slang_expr_bitwise_z_simplification_[pid].sv"]
set sv_fd [open $sv_file w]
puts -nonewline $sv_fd $sv_source
close $sv_fd

read_slang $sv_file
file delete -force $sv_file

set dump_file [file join /tmp "yosys_slang_expr_bitwise_z_simplification_[pid].il"]
write_rtlil $dump_file

set fd [open $dump_file r]
set rtlil [read $fd]
close $fd
file delete -force $dump_file

proc reject_preserved_z_result {rtlil signal} {
	set preserved_z [format {connect \A { 1'z \dynamic_bit }
    connect \Y \%s} $signal]

	if {[string first $preserved_z $rtlil] >= 0} {
		error "bitwise simplification preserved 1'bz in $signal instead of producing unknown"
	}
}

foreach signal {
	and_equal
	or_equal
	and_one_left
	and_one_right
	or_zero_left
	or_zero_right
} {
	reject_preserved_z_result $rtlil $signal
}
