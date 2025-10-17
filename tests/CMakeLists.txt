if (WITH_COVERAGE)
    if (CMAKE_CXX_COMPILER_ID STREQUAL Clang)
        set(test_launcher
            ${CMAKE_COMMAND} -E env
            LLVM_PROFILE_FILE=${CMAKE_BINARY_DIR}/yosys-slang.%p.profraw
        )

        add_custom_target(
            coverage
            COMMAND
                llvm-profdata merge -sparse
                yosys-slang.*.profraw
                -o yosys-slang.profdata
            COMMAND
                llvm-cov export -format lcov
                $<TARGET_FILE:yosys-slang>
                -instr-profile=yosys-slang.profdata
                --ignore-filename-regex=/third_party/
                --ignore-filename-regex=^/usr
                > yosys-slang.info
            WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        )
    endif()
endif()

set(ALL_TESTS
    unit/async.ys
    unit/function_call.ys
    unit/latch.ys
    unit/selftests.tcl
    various/assign_mixing.ys
    various/bb_detect.ys
    various/blackbox_scenarios.ys
    various/defaults.ys
    various/delays.ys
    various/expr.ys
    various/flop_naming.ys
    various/formal_stmts.ys
    various/hierref_error.ys
    various/ignore_asserts.ys
    various/intf_array_naming.ys
    various/intf_w_hierarchy.ys
    various/issue142.ys
    various/issue208.ys
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
    # SVA Test Suite
    sva/01_temporal_delay.ys
    sva/02_implication.ys
    sva/03_sequences.ys
    sva/04_repetition_consecutive.ys
    sva/05_repetition_nonconsec.ys
    sva/06_throughout_within.ys
    sva/07_intersect_firstmatch.ys
    sva/08_sva_functions.ys
    sva/09_property_declarations.ys
    sva/10_disable_iff.ys
    sva/11_local_variables.ys
    sva/12_deferred_assertions.ys
    sva/13_expect_statement.ys
    sva/14_concurrent_assertions.ys
    sva/15_multiclock.ys
    sva/16_complex_scenarios.ys
    # Advanced SVA Features
    sva/17_strong_weak.ys
    sva/18_abort_operators.ys
    sva/19_conditional_property.ys
    sva/20_case_property.ys
    sva/21_zero_length.ys
    sva/22_sequence_methods.ys
    sva/23_triggered_method.ys
)
foreach(test_script ${ALL_TESTS})
    set(test_fullpath ${CMAKE_CURRENT_SOURCE_DIR}/${test_script})
    get_filename_component(test_dir ${test_fullpath} DIRECTORY)
    add_test(
        NAME ${test_script}
        WORKING_DIRECTORY ${test_dir}
        COMMAND
            ${test_launcher}
            ${YOSYS_BINDIR}/yosys -m $<TARGET_FILE:yosys-slang> ${test_fullpath}
    )
endforeach()
