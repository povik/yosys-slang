#!/bin/bash
set -ex
TEST_DIR="$(dirname "${BASH_SOURCE[0]}")"
PLUGIN="$(realpath "$TEST_DIR/../../build/slang.so")"
CROC_PATH="$(realpath "$TEST_DIR/../third_party/croc/")"
(cd "$TEST_DIR" &&
	yosys -m ../../build/slang.so -s prepare.ys_ && \
	g++ -std=c++14 -o main main.cc -I `yosys-config --datdir`/include/backends/cxxrtl/runtime \
		-Wno-shift-count-overflow -Wno-array-bounds -O3)
rm -f /tmp/croc-jtag-bitbang.sock
"$TEST_DIR/main" /tmp/croc-jtag-bitbang.sock
(cd "$TEST_DIR" &&
	openocd -f debugger.tcl_ -d)
