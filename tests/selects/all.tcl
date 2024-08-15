yosys -import

proc module_list {} {
	set stat [yosys tee -q -s result.json stat -json]
	return [dict keys [dict get $stat modules]]
}

foreach fn {bitsel.v indexed_down.v indexed_up.v priority_encoder.sv struct_bit_select.sv break_return.sv} {
	log -header "Testset $fn"
	log -push
	design -reset

	read_slang $fn

	chformal -lower

	foreach m [module_list] {
		log -header "Testcase $m"
		log -push
		sat -verify -enable_undef -prove-asserts -show-public $m
		log -pop
	}
	log -pop
}
