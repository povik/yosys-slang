find_package(Yosys)
include(GitRevision)

git_rev_parse(YOSYS_SLANG_REVISION ${CMAKE_SOURCE_DIR})
git_rev_parse(SLANG_REVISION ${CMAKE_SOURCE_DIR}/third_party/slang)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/version.h.in ${CMAKE_CURRENT_BINARY_DIR}/version.h)

if (BUILD_AS_PLUGIN)
    set(LIBRARY_TYPE SHARED)
else()
    set(LIBRARY_TYPE STATIC)
endif()

add_library(yosys-slang ${LIBRARY_TYPE}
    abort_helpers.cc
    addressing.cc
    addressing.h
    async_pattern.cc
    async_pattern.h
    blackboxes.cc
    builder.cc
    cases.cc
    cases.h
    diag.cc
    diag.h
    initial_eval.cc
    initial_eval.h
    memory.h
    naming.cc
    procedural.cc
    slang_frontend.cc
    slang_frontend.h
    statements.h
    variables.cc
    variables.h
    ${CMAKE_CURRENT_BINARY_DIR}/version.h
)
target_include_directories(yosys-slang PRIVATE ${CMAKE_CURRENT_BINARY_DIR})
target_link_libraries(yosys-slang PRIVATE yosys::yosys slang::slang)

if (BUILD_AS_PLUGIN)
    set_target_properties(yosys-slang PROPERTIES
        RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}
        LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}
        # Yosys assumes `.so` to be the suffix on all platforms, so the following is required to make
        # `yosys -m slang` to work after installation on any platform.
        PREFIX ""
        OUTPUT_NAME "slang"
        SUFFIX ".so"
    )

    if (WIN32)
        # install .dll only
        install(TARGETS yosys-slang RUNTIME DESTINATION ${YOSYS_DATDIR}/plugins)
    else()
        # install .so/.dylib only
        install(TARGETS yosys-slang LIBRARY DESTINATION ${YOSYS_DATDIR}/plugins)
    endif()
else()
    set_target_properties(yosys-slang PROPERTIES
        ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}
        STATIC_LIBRARY_OPTIONS "$<TARGET_OBJECTS:fmt::fmt>;$<TARGET_OBJECTS:slang::slang>"
    )
endif()
