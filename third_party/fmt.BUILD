load("@rules_cc//cc:defs.bzl", "cc_library")

cc_library(
    name = "fmt",
    srcs = [
        "src/format.cc",
        "src/os.cc",
    ],
    hdrs = glob(["include/fmt/*.h"]),
    includes = ["include"],
    visibility = ["//visibility:public"],
)
