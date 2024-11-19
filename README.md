# yosys-slang: SystemVerilog frontend for Yosys

yosys-slang is a Yosys plugin providing a new command (`read_slang`) for loading SystemVerilog designs.

yosys-slang builds on top of the [slang](https://github.com/MikePopoloski/slang) library to provide comprehensive SystemVerilog support.

The plugin is available prebuilt as part of

 * [OSS CAD Suite](https://github.com/YosysHQ/oss-cad-suite-build) from YosysHQ, and

 * [IIC-OSIC-TOOLS](https://github.com/iic-jku/iic-osic-tools) from Johannes Kepler University

## Status

*News:* The [Microelectronics Design Center](https://dz.ethz.ch/) at ETH Zürich is now sponsoring yosys-slang development for usage in ASIC synthesis flows!

yosys-slang understands a synthesizable subset of SystemVerilog. Please open GitHub issues for missing features and/or confusing error messages.

yosys-slang can parse a number of open-source IPs, including:

 * [Black Parrot](https://github.com/black-parrot/black-parrot/)

 * [BSC Core Tile](https://github.com/bsc-loca/core_tile/)

 * [OpenHW Group's CV32E40P](https://github.com/openhwgroup/cv32e40p)

 * [Ibex RISC-V Core](https://github.com/lowRISC/ibex)

 * [OpenTitan: Open source silicon root of trust](https://github.com/lowRISC/opentitan)

 * [RSD RISC-V Out-of-Order Superscalar Processor](https://github.com/rsd-devel/rsd/)

For details see the [compat suite repository](https://github.com/povik/yosys-slang-compat-suite) which documents sample command lines.

yosys-slang is on the [CHIPS Alliance sv-tests dashboard](https://chipsalliance.github.io/sv-tests-results/) where failing test cases and their error messages (with useful line numbers and AST dumps!) can be browsed. Note some tests on the sv-tests dashboard are misconfigured for testing a synthesis tool.

If you wish to sponsor the project's development, and prioritize certain features, please get in touch.

## Building

*Prerequisities:*

 * Yosys installed

 * Usual toolchains, CMake

Check out the repository including the submodule, e.g. with

    git clone --recursive https://github.com/povik/yosys-slang

Then build both slang and the `build/slang.so` plugin for Yosys:

    make -j$(nproc)

Use a custom `-jN` switch to build with `N` concurrent processes instead of matching the number of cores.

The built plugin is placed at `build/slang.so`. Copy this file into the Yosys plugin directory, or use a full path to this file (instead of the `slang` shorthand) when loading the plugin.

## Usage

You load the plugin into Yosys on startup by passing the `-m` argument:

    $ yosys -m slang

Or, alternatively, you load the plugin at runtime with the `plugin` command:

    plugin -i slang

After the plugin has been loaded, the frontend is invoked with the `read_slang` command. The command accepts standard slang options, see `help read_slang` and [slang documentation](https://www.sv-lang.com/command-line-ref.html).

Sample usage:

    read_slang picorv32.v --top picorv32 -D DEBUG

## Contributing

Contributions are welcome! If you intent to develop a particular feature, feel free to get in touch and consult on the appropriate approach.

## License

The main glue code (`slang_frontend.cc` `slang_frontend.h` `memory.h` `addressing.h`) is distributed under the ISC license, see `LICENSE`. The `initial_eval.cc` code contains modified portions of Slang and is distributed under the terms of the MIT license, see the file header.
