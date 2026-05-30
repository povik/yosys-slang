yosys -import

proc module_list {} {
	set stat [yosys tee -q -s result.json stat -json A:top]
	return [dict keys [dict get $stat modules]]
}

foreach fn [glob *.sv] {
	log -header "Testset $fn"
	log -push
	design -reset

	read_slang --dump-ast $fn
	check -assert

	foreach m [module_list] {
		log -header "Testcase $m"
		log -push
		test_slangsva
		async2sync
		formalff -clk2ff
		techmap
		aigmap
		opt_clean
		# Strip backslash from the start of $m
		set m [string range $m 1 end]
		write_aiger -zinit "$fn-$m.aig"
		set flag "$fn-$m.aig.flag"
		file delete $flag
		yosys exec -- yosys-abc -c "\"read $fn-$m.aig; pdr -v; write_cex '$fn-$m.aig.flag'\""

		if {[file exists $flag]} {
		    puts stderr "Property failed to prove: counterexample exists"
		    exit 1
		}

		log -pop
	}
	log -pop
}
