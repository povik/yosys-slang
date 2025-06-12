# yosys-slang: SystemVerilog frontend for Yosys

yosys-slang is a Yosys plugin providing a new command (`read_slang`) for loading SystemVerilog designs.

yosys-slang builds on top of the [slang](https://github.com/MikePopoloski/slang) library to provide comprehensive SystemVerilog support. The plugin supports an (informally defined) synthesizable subset of SystemVerilog in version IEEE 1800-2017 or IEEE 1800-2023.

Please open GitHub issues for missing features and/or confusing error messages.

The plugin is available prebuilt as part of

 * [OSS CAD Suite](https://github.com/YosysHQ/oss-cad-suite-build) from YosysHQ, and

 * [IIC-OSIC-TOOLS](https://github.com/iic-jku/iic-osic-tools) from Johannes Kepler University

## News

<a href="http://asic.ethz.ch/2024/MLEM.html"><img align="right" width="100" height="100" src="docs/mlem.jpg"></a>

*2025/05:* [Koopa](http://asic.ethz.ch/2025/Koopa.html) taped out using yosys-slang.

*2024/12:* ETH Zürich have used yosys-slang for a chip tapeout. [Meet MLEM](http://asic.ethz.ch/2024/MLEM.html).

## Compatibility

yosys-slang can parse a number of open-source IPs, including:

 * [Black Parrot](https://github.com/black-parrot/black-parrot/)

 * [BSC Core Tile](https://github.com/bsc-loca/core_tile/)

 * [OpenHW Group's CV32E40P](https://github.com/openhwgroup/cv32e40p)

 * [Ibex RISC-V Core](https://github.com/lowRISC/ibex)

 * [OpenTitan: Open source silicon root of trust](https://github.com/lowRISC/opentitan)

 * [RSD RISC-V Out-of-Order Superscalar Processor](https://github.com/rsd-devel/rsd/)

For details see the [compat suite repository](https://github.com/povik/yosys-slang-compat-suite) which documents sample command lines.

## Building

*Prerequisities:*

 * Yosys installed: supported versions are **0.44 0.45 0.46 0.47 0.48 0.49 0.50 0.51 0.52 0.53 0.54**

 * C++ compiler: GCC 11 and clang 17 are minimum supported versions

 * Usual toolchains, CMake

Check out the repository including the submodule, e.g. with

    git clone --recursive https://github.com/povik/yosys-slang

Then build both slang and the `build/slang.so` plugin for Yosys:

    make -j$(nproc)

Use a custom `-jN` switch to build with `N` concurrent processes instead of matching the number of cores.

The built plugin is placed at `build/slang.so`. Copy this file into the Yosys plugin directory, which can be achieved through `make install`, or use a full path to this file (instead of the `slang` shorthand) when loading the plugin.

## Usage

You load the plugin into Yosys on startup by passing the `-m` argument:

    $ yosys -m slang

Or, alternatively, you load the plugin at runtime with the `plugin` command:

    plugin -i slang

After the plugin has been loaded, the frontend is invoked with the `read_slang` command.

For a full documentation of the command options, see `help read_slang`. The command understands standard [slang options](https://www.sv-lang.com/command-line-ref.html).

Sample usage:

    read_slang picorv32.v --top picorv32 -D DEBUG

## Contributing

Contributions are welcome! If you intent to develop a particular feature, feel free to get in touch and consult on the appropriate approach.

## Supporters

The following organizations have supported the project and contributed to yosys-slang development:

 * [Microelectronics Design Center of ETH Zürich](https://dz.ethz.ch/)

 * [PULP platform](https://pulp-platform.org/)

 * [Silimate](https://www.silimate.com/)

 * [YosysHQ](https://www.yosyshq.com/)

## License

The bulk of yosys-slang source code is is distributed under the ISC license, see `LICENSE`. An exception is `src/initial_eval.cc` which contains modified portions of Slang and is distributed under the terms of the MIT license, see the file header.

In addition, yosys-slang embeds

 * slang, Copyright (c) Michael Popoloski, see `third_party/slang/` for license information 
 * {fmt}, Copyright (c) Victor Zverovich and {fmt} contributors, see `third_party/fmt/` for license information 
