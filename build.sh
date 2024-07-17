#!/bin/sh
set -e
cmake -S third_party/slang -B build/slang -DCMAKE_INSTALL_PREFIX=build/slang_install -DSLANG_USE_MIMALLOC=OFF \
	-DSLANG_INCLUDE_TESTS=OFF -DCMAKE_BUILD_TYPE=Release -DSLANG_INCLUDE_TOOLS=OFF \
	-DCMAKE_CXX_FLAGS="-fPIC" -DBoost_NO_BOOST_CMAKE=ON
make -C build/slang -j$(nproc)
make -C build/slang install
mkdir -p $(dirname "$TARGET")
${YOSYS_PREFIX}yosys-config --build "$TARGET" \
				slang_frontend.cc initial_eval.cc \
				-Ibuild/slang_install/include -std=c++20 \
				-DSLANG_BOOST_SINGLE_HEADER -Lbuild/slang_install/lib \
				-lsvlang -lfmt
