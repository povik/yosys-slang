load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _tomlplusplus_impl(module_ctx):
    http_archive(
        name = "tomlplusplus",
        urls = ["https://github.com/marzer/tomlplusplus/archive/refs/tags/v3.4.0.tar.gz"],
        strip_prefix = "tomlplusplus-3.4.0",
        build_file = "//:dependency_support/tomlplusplus.BUILD.bazel",
    )

tomlplusplus_ext = module_extension(
    implementation = _tomlplusplus_impl,
)
