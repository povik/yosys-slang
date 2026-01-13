yosys -import

proc module_list {} {
	set stat [yosys tee -q -s result.json stat -json A:top]
	return [dict keys [dict get $stat modules]]
}

foreach fn [glob *.sv] {
	log -header "Testset $fn"
	log -push
	design -reset

	read_slang $fn
	chformal -lower

	foreach m [module_list] {
		log -header "Testcase $m"
		log -push
		setundef -undriven -undef $m
		sat -verify -enable_undef -prove-asserts -show-public $m
		log -pop
	}
	log -pop
}


foreach fn [glob *.sv] {
	log -header "Testset $fn (hierarchical)"
	log -push
	design -reset

	read_slang --keep-hierarchy $fn

	chformal -lower

	foreach m [module_list] {
		log -header "Testcase $m (hierarchical)"
		log -push
		flatten $m
		setundef -undriven -undef $m
		sat -verify -enable_undef -prove-asserts -show-public $m
		log -pop
	}
	log -pop
}
