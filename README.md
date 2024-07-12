# yosys & slang: A match made in heaven

This is an incomplete slang-based frontend for Yosys. You can use it to read SystemVerilog sources into Yosys.

## Background

This combination of software projects (Yosys and Slang) is perfect, because:

 * [Yosys](https://github.com/YosysHQ/yosys), being a great and versatile tool for synthesis and formal flows, has its native Verilog frontend in less-than-perfect shape, with significant technical debt and with no realistic outlook toward adding full SystemVerilog support.

 * [slang](https://github.com/MikePopoloski/slang) is a SystemVerilog parser and elaborator with a reputation of having gotten the fundamentals right.

## Status

Basically this can parse out simple Verilog projects (it does parse a functioning [picorv32](https://github.com/YosysHQ/picorv32)!). Some missing features are:

 * Memory inference

 * Interfaces

 * Full-featured execution of initial blocks

 * Assertions, formal statements

`yosys-slang` is on the [CHIPS Alliance sv-tests dashboard](https://chipsalliance.github.io/sv-tests-results/) where failing test cases and their error messages (with useful line numbers and AST dumps!) can be browsed.

## Building (provisional instructions)

*Prerequisities:*

 * Yosys installed

 * [libfmt](https://github.com/fmtlib/fmt)

 * Usual toolchains, CMake

Check out the repository including the submodule, e.g. with

    git clone --recursive https://github.com/povik/yosys-slang

First build slang and install it into `build/slang_install`:

    cmake -S third_party/slang -B build/slang -DCMAKE_INSTALL_PREFIX=build/slang_install -DSLANG_USE_MIMALLOC=OFF
    make -C build/slang -j$(nproc)
    make -C build/slang install

Then build the `build/slang.so` plugin for Yosys:

    yosys-config --build build/slang.so slang_frontend.cc initial_eval.cc proc_usage.cc -Ibuild/slang_install/include -std=c++20 -DSLANG_BOOST_SINGLE_HEADER -Lbuild/slang_install/lib -lsvlang -lfmt

## Usage

You load the plugin into Yosys on startup by passing the `-m` argument:

    $ yosys -m build/slang.so

Or, alternatively, you load the plugin at runtime with the `plugin` command:

    plugin -i build/slang.so

The frontend is invoked with the `read_slang` command. The command accepts standard slang options, see `help read_slang` and [slang documentation](https://www.sv-lang.com/command-line-ref.html).

Sample usage:

    read_slang picorv32.v --top picorv32 -D DEBUG

## Contributing

This is foremost a demonstrator with no fixed plans for its future. Any contributions, gradual improvements, or just better characterization of the available and missing feature sets are welcome! The glue code here understands some AST features, and rejects others, but it's not clear what language features that translates to when there's preprocessing done by slang.

## License

The main glue code (`slang_frontend.cc` `slang_frontend.h` `proc_usage.cc` `addressing.h`) is distributed under the ISC license, see `LICENSE`. The `initial_eval.cc` code contains modified portions of Slang and is distributed under the terms of the MIT license, see the file header.
