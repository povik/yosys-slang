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
