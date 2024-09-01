#!/bin/sh
set -e
# this file is here for the benefit of chipsalliance/sv-tests and it will
# be retired once the build instructions within sv-tests are updated
make -j$(nproc) YOSYS_PREFIX=${YOSYS_PREFIX}
mkdir -p $(dirname "$TARGET")
cp build/slang.so "$TARGET"
