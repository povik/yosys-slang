# for out-of-tree build support
SOURCE_DIR := $(dir $(firstword $(MAKEFILE_LIST)))

CMAKE_FLAGS = -DCMAKE_BUILD_TYPE=Release

build: configure
	+cmake --build build

install: build
	+cmake --install build

clean:
	rm -rf build/*

configure:
	@if [ ! -f "$(SOURCE_DIR)/third_party/slang/CMakeLists.txt" ]; then \
		echo "The content of the slang submodule seems to be missing."; \
		echo "Initialize the submodule with"; \
		echo ""; \
		echo "  git submodule init"; \
		echo "  git submodule update third_party/slang"; \
		echo ""; \
		exit 1; \
	fi
	@if [ ! -f "$(SOURCE_DIR)/third_party/fmt/CMakeLists.txt" ]; then \
		echo "The content of the fmt submodule seems to be missing."; \
		echo "Initialize the submodule with"; \
		echo ""; \
		echo "  git submodule init"; \
		echo "  git submodule update third_party/fmt"; \
		echo ""; \
		exit 1; \
	fi
	cmake -S . -B build -DYOSYS_CONFIG=$(YOSYS_PREFIX)yosys-config $(CMAKE_FLAGS)

.PHONY: build install clean configure
