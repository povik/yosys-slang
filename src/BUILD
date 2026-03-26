# SPDX-License-Identifier: ISC
# slang-elab shared frontend sources, compiled without Yosys

load("@rules_cc//cc:cc_library.bzl", "cc_library")

cc_library(
    name = "slang_frontend",
    srcs = [
        "addressing.cc",
        "async_pattern.cc",
        "builder.cc",
        "diag.cc",
        "initialization.cc",
        "lvalue.cc",
        "naming.cc",
        "procedural.cc",
        "slang_frontend.cc",
        "variables.cc",
    ],
    hdrs = [
        "async_pattern.h",
        "diag.h",
        "memory.h",
        "slang_frontend.h",
        "statements.h",
        "variables.h",
    ],
    defines = [
        "SLANG_MUX_LOWERING",
        "SLANG_NO_YOSYS",
    ],
    includes = ["."],
    visibility = ["//visibility:public"],
    deps = [
        "//src/syn/src/elab:elab_hdrs",
        "//third-party/yosys-hashlib",
        "@fmt",
        "@slang",
    ],
)
