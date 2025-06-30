if (CMAKE_BINARY_DIR STREQUAL CMAKE_SOURCE_DIR)
    message(FATAL_ERROR "In-tree builds are not supported. Instead, run:\ncmake . -B build <options> && cmake --build build")
endif()

# as in slang
cmake_minimum_required(VERSION 3.20...3.29)

# as in slang
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

project(yosys-slang CXX)
set(CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake" ${CMAKE_MODULE_PATH})

option(BUILD_AS_PLUGIN "Build yosys-slang as a plugin" ON)
mark_as_advanced(BUILD_AS_PLUGIN)

if (APPLE AND BUILD_AS_PLUGIN)
    # On Linux, the shared libraries can refer to symbols from the executable by default.
    # On macOS, this is not the default behavior and needs to be enabled explicitly.
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -undefined dynamic_lookup")
endif()

include(AddCompileLinkOptions)

option(WITH_COVERAGE "Build with code coverage collection" OFF)
if (WITH_COVERAGE)
    if (CMAKE_CXX_COMPILER_ID STREQUAL Clang)
        add_compile_link_options(-fprofile-instr-generate -fcoverage-mapping)
    else()
        message(FATAL_ERROR "Unsupported compiler for coverage collection: ${CMAKE_CXX_COMPILER_ID}")
    endif()
endif()

option(WITH_UBSAN "Build with UndefinedBehaviorSanitizer" OFF)
if (WITH_UBSAN)
    add_compile_link_options(${sanitizer_options} -fsanitize=undefined)
endif()

option(WITH_ASAN "Build with AddressSanitizer" OFF)
if (WITH_ASAN)
    add_compile_link_options(${sanitizer_options} -fsanitize=undefined)
endif()

include(FetchContent)

# The log will show "-- Using remote fmt library", but that is misleading,
# as no network access will be done. (Our first declaration of `fmt` wins.)
option(FMT_INSTALL OFF)
FetchContent_Declare(
    fmt
    EXCLUDE_FROM_ALL
    SOURCE_DIR ${CMAKE_SOURCE_DIR}/third_party/fmt
)

set(SLANG_USE_MIMALLOC OFF)
add_subdirectory(third_party/slang)

# We're statically linking slang (and fmt) into our plugin, which itself is a shared library.
# Unless we build the dependencies as PIC, linking will fail.
set_target_properties(fmt PROPERTIES POSITION_INDEPENDENT_CODE ${BUILD_AS_PLUGIN})
set_target_properties(slang_slang PROPERTIES POSITION_INDEPENDENT_CODE ${BUILD_AS_PLUGIN})

add_subdirectory(src)

enable_testing()
add_subdirectory(tests)
