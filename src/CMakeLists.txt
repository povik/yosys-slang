find_package(Yosys)

add_library(yosys-slang SHARED
    abort_helpers.cc
    addressing.h
    async_pattern.cc
    async_pattern.h
    blackboxes.cc
    builder.cc
    cases.h
    diag.cc
    diag.h
    initial_eval.cc
    initial_eval.h
    memory.h
    naming.cc
    slang_frontend.cc
    slang_frontend.h
)
target_link_libraries(yosys-slang PRIVATE yosys::yosys slang::slang)
set_target_properties(yosys-slang PROPERTIES
    PREFIX ""
    OUTPUT_NAME slang
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}
    LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}
)

if(WIN32)
    # install .dll only
    install(TARGETS yosys-slang RUNTIME DESTINATION ${YOSYS_DATDIR}/plugins)
else()
    # install .so/.dylib only
    install(TARGETS yosys-slang LIBRARY DESTINATION ${YOSYS_DATDIR}/plugins)
endif()
