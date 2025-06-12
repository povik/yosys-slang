file(GLOB YS_TESTS "${CMAKE_CURRENT_SOURCE_DIR}/*/*.ys")
file(GLOB TCL_TESTS "${CMAKE_CURRENT_SOURCE_DIR}/*/*.tcl")

set(ALL_TESTS ${YS_TESTS} ${TCL_TESTS})
foreach(test_script ${ALL_TESTS})
    get_filename_component(test_dir ${test_script} DIRECTORY)
    add_test(NAME ${test_script} WORKING_DIRECTORY ${test_dir} COMMAND  stdbuf -oL -eL ${YOSYS_BINDIR}/yosys -m $<TARGET_FILE:yosys-slang> ${test_script})
endforeach()
