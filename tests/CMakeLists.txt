set(ALL_TESTS
    unit/async.ys
    unit/function_call.ys
    unit/latch.ys
    unit/selftests.tcl
    various/blackbox_scenarios.ys
    various/defaults.ys
    various/delays.ys
    various/expr.ys
    various/flop_naming.ys
    various/formal_stmts.ys
    various/intf_array_naming.ys
    various/intf_w_hierarchy.ys
    various/issue142.ys
    various/issue50.ys
    various/mem_inference.ys
    various/meminit.ys
    various/pragmas.ys
    various/regress.ys
    various/stringattrs.ys
    various/stringparams.ys
    various/timescale.ys
    various/top_attr.ys
    various/unknown_cells.ys
    various/hierref_error.ys
)
foreach(test_script ${ALL_TESTS})
    set(test_fullpath "${CMAKE_CURRENT_SOURCE_DIR}/${test_script}")
    get_filename_component(test_dir ${test_fullpath} DIRECTORY)
    add_test(
        NAME ${test_script}
        WORKING_DIRECTORY ${test_dir}
        COMMAND
            "${YOSYS_BINDIR}/yosys" -m "$<TARGET_FILE:yosys-slang>" "${test_fullpath}"
    )
endforeach()
