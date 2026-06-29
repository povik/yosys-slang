# The diagnostic_gen.py / syntax_gen.py codegen mirrors what slang's own
# cmake runs at build time. SLANG_VERSION_PATCH/HASH are stubbed (cmake
# derives them from `git describe`); refine with a workspace-status hook
# if needed.

load("@bazel_skylib//rules:expand_template.bzl", "expand_template")
load("@rules_cc//cc:cc_library.bzl", "cc_library")
load("@rules_license//rules:license.bzl", "license")
load(
    "@yosys-slang//:dependency_support/slang_ext.bzl",
    "SLANG_VERSION_HASH",
    "SLANG_VERSION_MAJOR",
    "SLANG_VERSION_MINOR",
    "SLANG_VERSION_PATCH",
)

package(
    features = ["layering_check"],
)

license(
    name = "license_slang",
    package_name = "slang",
    license_kinds = ["@rules_license//licenses/spdx:MIT"],
    license_text = "LICENSE",
)

genrule(
    name = "slang_export_h",
    outs = ["slang/slang_export.h"],
    cmd = """cat > $@ << 'HEADER'
#pragma once
#define SLANG_EXPORT
#define SLANG_NO_EXPORT
HEADER""",
)

expand_template(
    name = "slang_version_cpp",
    out = "VersionInfo.cpp",
    substitutions = {
        "@SLANG_VERSION_MAJOR@": str(SLANG_VERSION_MAJOR),
        "@SLANG_VERSION_MINOR@": str(SLANG_VERSION_MINOR),
        "@SLANG_VERSION_PATCH@": str(SLANG_VERSION_PATCH),
        "@SLANG_VERSION_HASH@": SLANG_VERSION_HASH,
    },
    template = "source/util/VersionInfo.cpp.in",
)

genrule(
    name = "slang_diag_gen",
    srcs = [
        "scripts/diagnostic_gen.py",
        "scripts/diagnostics.txt",
    ] + glob([
        "source/**/*.cpp",
        "include/slang/**/*.h",
    ]),
    outs = [
        "DiagCode.cpp",
        "slang/diagnostics/AllDiags.h",
        "slang/diagnostics/AnalysisDiags.h",
        "slang/diagnostics/CompilationDiags.h",
        "slang/diagnostics/ConstEvalDiags.h",
        "slang/diagnostics/DeclarationsDiags.h",
        "slang/diagnostics/DriverDiags.h",
        "slang/diagnostics/ExpressionsDiags.h",
        "slang/diagnostics/GeneralDiags.h",
        "slang/diagnostics/LexerDiags.h",
        "slang/diagnostics/LookupDiags.h",
        "slang/diagnostics/MetaDiags.h",
        "slang/diagnostics/NumericDiags.h",
        "slang/diagnostics/ParserDiags.h",
        "slang/diagnostics/PreprocessorDiags.h",
        "slang/diagnostics/StatementsDiags.h",
        "slang/diagnostics/SysFuncsDiags.h",
        "slang/diagnostics/TypesDiags.h",
    ],
    cmd = """
        SCRIPTS=$$(dirname $(location scripts/diagnostic_gen.py)) && \
        $(PYTHON3) $(location scripts/diagnostic_gen.py) \
            --outDir $(@D) \
            --srcDir $$SCRIPTS/../source \
            --incDir $$SCRIPTS/../include/slang \
            --diagnostics $(location scripts/diagnostics.txt)
    """,
    toolchains = ["@rules_python//python:current_py_toolchain"],
)

genrule(
    name = "slang_syntax_gen",
    srcs = glob(["scripts/*.txt"]) + [
        "scripts/syntax_gen.py",
    ],
    outs = [
        "AllSyntax.cpp",
        "KnownSystemName.cpp",
        "SyntaxClone.cpp",
        "TokenKind.cpp",
        "slang/syntax/AllSyntax.h",
        "slang/syntax/CSTJsonVisitorGen.h",
        "slang/syntax/SyntaxFwd.h",
        "slang/syntax/SyntaxKind.h",
        "slang/parsing/TokenKind.h",
        "slang/parsing/KnownSystemName.h",
    ],
    cmd = """
        SCRIPTS=$$(dirname $(location scripts/syntax_gen.py)) && \
        $(PYTHON3) $(location scripts/syntax_gen.py) \
            --dir $(@D) \
            --syntax $$SCRIPTS/syntax.txt
    """,
    toolchains = ["@rules_python//python:current_py_toolchain"],
)

cc_library(
    name = "slang",
    srcs = glob(
        ["source/**/*.cpp"],
    ) + glob(
        ["source/**/*.h"],
    ) + [
        ":AllSyntax.cpp",
        ":DiagCode.cpp",
        ":KnownSystemName.cpp",
        ":SyntaxClone.cpp",
        ":TokenKind.cpp",
        ":VersionInfo.cpp",
    ],
    hdrs = glob([
        "include/**/*.h",
        "external/**/*.hpp",  # buildifier: disable=external-path
        "external/ieee1800/**",  # buildifier: disable=external-path
    ]) + [
        ":slang/diagnostics/AllDiags.h",
        ":slang/diagnostics/AnalysisDiags.h",
        ":slang/diagnostics/CompilationDiags.h",
        ":slang/diagnostics/ConstEvalDiags.h",
        ":slang/diagnostics/DeclarationsDiags.h",
        ":slang/diagnostics/DriverDiags.h",
        ":slang/diagnostics/ExpressionsDiags.h",
        ":slang/diagnostics/GeneralDiags.h",
        ":slang/diagnostics/LexerDiags.h",
        ":slang/diagnostics/LookupDiags.h",
        ":slang/diagnostics/MetaDiags.h",
        ":slang/diagnostics/NumericDiags.h",
        ":slang/diagnostics/ParserDiags.h",
        ":slang/diagnostics/PreprocessorDiags.h",
        ":slang/diagnostics/StatementsDiags.h",
        ":slang/diagnostics/SysFuncsDiags.h",
        ":slang/diagnostics/TypesDiags.h",
        ":slang/parsing/KnownSystemName.h",
        ":slang/parsing/TokenKind.h",
        ":slang/slang_export.h",
        ":slang/syntax/AllSyntax.h",
        ":slang/syntax/CSTJsonVisitorGen.h",
        ":slang/syntax/SyntaxFwd.h",
        ":slang/syntax/SyntaxKind.h",
    ],
    applicable_licenses = [":license_slang"],
    copts = [
        "-fPIC",
        "-std=c++20",
        "-Wno-unused-parameter",
    ],
    includes = [
        "external",
        "include",
        "source/ast/builtins",
    ],
    visibility = ["@yosys-slang//:__subpackages__"],
    deps = [
        "@fmt",
        "@boost//regex:regex",
        "@tomlplusplus//:tomlplusplus",
    ],
)
