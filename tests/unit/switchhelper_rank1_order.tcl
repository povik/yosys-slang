yosys -import

set sv_file [file join [pwd] switchhelper_rank1.sv]
set first_dump [file join /tmp "yosys_slang_switchhelper_rank1_order_[pid]_a.il"]
set second_dump [file join /tmp "yosys_slang_switchhelper_rank1_order_[pid]_b.il"]

proc dump_order_test {sv_file dump_file} {
	design -reset
	# This test covers frontend-generated process ordering, not Yosys's
	# version-specific proc lowering order.
	read_slang --no-proc $sv_file
	hierarchy -top switchhelper_rank1_order
	write_rtlil $dump_file
}

proc normalized_rtlil {dump_file} {
	set fd [open $dump_file r]
	set text [read $fd]
	close $fd

	# A single Yosys process intentionally keeps allocating fresh internal
	# auto names across design resets. Normalize those IDs while preserving the
	# generated port, statement, cell, wire, and connection ordering.
	regsub -all {autoidx [0-9]+} $text {autoidx <N>} text
	regsub -all {\$procmux\$[0-9]+} $text {$procmux$<N>} text
	regsub -all {\$[0-9]+} $text {$<N>} text
	return $text
}

dump_order_test $sv_file $first_dump
dump_order_test $sv_file $second_dump

set first_text [normalized_rtlil $first_dump]
set second_text [normalized_rtlil $second_dump]

file delete -force $first_dump $second_dump

if {$first_text ne $second_text} {
	error "switchhelper_rank1_order RTLIL output changed between identical reads"
}
