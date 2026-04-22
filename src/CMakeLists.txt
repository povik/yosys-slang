include(GitRevision)

# Paths resolved relative to this CMakeLists so the file works whether
# slang-elab is the top-level project or is pulled in via add_subdirectory.
get_filename_component(_SLANG_ELAB_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/.." ABSOLUTE)
git_rev_parse(YOSYS_SLANG_REVISION ${_SLANG_ELAB_ROOT})
git_rev_parse(SLANG_REVISION ${_SLANG_ELAB_ROOT}/third_party/slang)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/version.h.in ${CMAKE_CURRENT_BINARY_DIR}/version.h)

# Frontend-only static library: the slang-elab sources compiled without the
# Yosys backend. Mirrors the Bazel //third-party/slang-elab/src:slang_frontend
# target. Callers link their own backend (e.g. OpenROAD's syn::elab).
add_library(slang_frontend STATIC
    addressing.cc
    async_pattern.cc
    builder.cc
    diag.cc
    initialization.cc
    lvalue.cc
    naming.cc
    procedural.cc
    slang_frontend.cc
    variables.cc
    ${CMAKE_CURRENT_BINARY_DIR}/version.h
)
target_compile_definitions(slang_frontend PUBLIC
    SLANG_MUX_LOWERING
    SLANG_NO_YOSYS
)
target_include_directories(slang_frontend
    PUBLIC
        ${CMAKE_CURRENT_SOURCE_DIR}
    PRIVATE
        ${CMAKE_CURRENT_BINARY_DIR}
)
target_link_libraries(slang_frontend PUBLIC slang::slang fmt::fmt)
set_target_properties(slang_frontend PROPERTIES POSITION_INDEPENDENT_CODE ON)

option(SLANG_ELAB_BUILD_YOSYS_PLUGIN "Build slang-elab as a Yosys plugin" ON)
if (NOT SLANG_ELAB_BUILD_YOSYS_PLUGIN)
    return()
endif()

find_package(Yosys)

if (BUILD_AS_PLUGIN)
    set(LIBRARY_TYPE SHARED)
else()
    set(LIBRARY_TYPE STATIC)
endif()

add_library(yosys-slang ${LIBRARY_TYPE}
    backends/yosys/abort_helpers.cc
    backends/yosys/backend_builder.cc
    backends/yosys/backend_builder.h
    backends/yosys/blackboxes.cc
    backends/yosys/cases.cc
    backends/yosys/cases.h
    backends/yosys/driver.cc
    backends/yosys/ir.cc
    backends/yosys/ir.h
    addressing.cc
    async_pattern.cc
    async_pattern.h
    builder.cc
    diag.cc
    diag.h
    initialization.cc
    lvalue.cc
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
target_include_directories(yosys-slang PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}/backends/yosys
    ${CMAKE_CURRENT_BINARY_DIR}
)
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
