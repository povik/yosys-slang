#!/bin/bash
set -ex
TEST_DIR="$(dirname "${BASH_SOURCE[0]}")"
PLUGIN="$(realpath "$TEST_DIR/../../build/slang.so")"
CROC_PATH="$(realpath "$TEST_DIR/../third_party/croc/")"
rm -rf /tmp/croc-jtag-bitbang.sock
(cd "$TEST_DIR" &&
	yosys -m ../../build/slang.so -s prepare.ys_ &&
	./main /tmp/croc-jtag-bitbang.sock)
(cd "$TEST_DIR" &&
	openocd -f debugger.tcl_ -d)
