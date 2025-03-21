# for out-of-tree build support
SRC_DIR := $(dir $(firstword $(MAKEFILE_LIST)))
VPATH := $(SRC_DIR)
YOSYS_CONFIG := $(YOSYS_PREFIX)yosys-config
PLUGINDIR:=$(shell $(YOSYS_CONFIG) --datdir)/plugins
CXXFLAGS :=
SRCS = $(wildcard $(SRC_DIR)/src/*.cc)
OBJS = $(patsubst $(SRC_DIR)/src/%.cc,build/%.o,$(SRCS))

build: build/slang.so

configure-slang:
	@mkdir -p $(@D)
	@if [ ! -f "$(SRC_DIR)/third_party/slang/CMakeLists.txt" ]; then \
		echo "The content of the slang submodule seems to be missing."; \
		echo "Initialize the submodule with"; \
		echo ""; \
		echo "  git submodule init"; \
		echo "  git submodule update third_party/slang"; \
		echo ""; \
		exit 1; \
	fi
	cmake -S $(SRC_DIR)/third_party/slang -B build/slang \
		-DCMAKE_INSTALL_PREFIX=build/slang_install \
		-DSLANG_INCLUDE_TESTS=OFF \
		-DSLANG_INCLUDE_TOOLS=OFF \
		-DCMAKE_BUILD_TYPE=Release \
		-DSLANG_USE_MIMALLOC=OFF \
		-DCMAKE_CXX_FLAGS="-fPIC" \
		-DCMAKE_DISABLE_FIND_PACKAGE_Boost=ON \
		-DCMAKE_DISABLE_FIND_PACKAGE_fmt=ON \
		-DCMAKE_INSTALL_LIBDIR=lib

build/slang/.configured:
	$(MAKE) configure-slang
	touch $@

build-slang: build/slang/.configured
	$(MAKE) -C $(dir $^)
	$(MAKE) -C $(dir $^) install
	touch build/slang_install/.built

build/slang_install/.built:
	$(MAKE) build-slang

clean-slang:
	rm -rf build/slang build/slang_install

clean-objects:
	rm -f $(OBJS)

clean: clean-objects
	rm -f build/slang.so

clean-all: clean clean-slang

install: build/slang.so
	mkdir -p $(PLUGINDIR)
	cp $< $(PLUGINDIR)

# Let developers opt in to have fater rebuilds at the cost of
# needing to make sure to run `make build-slang` if the slang
# version changes. To enable:
#
# make NO_SLANG_REBUILD=1
#
NO_SLANG_REBUILD := 0
ifeq ($(NO_SLANG_REBUILD),1)
SLANG_TARGET = build/slang_install/.built
else
SLANG_TARGET = build-slang
endif

# Note: -Ibuild/slang_install/include must appear before --cxxflags
# in case there's a slang install at the Yosys install prefix
-include $(OBJS:.o=.d)
build/%.o: src/%.cc $(SLANG_TARGET)
	@mkdir -p $(@D)
	@echo "    CXX $@"
	@$(YOSYS_CONFIG) --exec --cxx \
		 -DSLANG_BOOST_SINGLE_HEADER \
		 -Ibuild/slang_install/include \
		 --cxxflags -O3 -g -I . -MD \
		 -c -o $@ $< -std=c++20 \
		 $(CXXFLAGS)

build/slang.so: $(OBJS)
	@mkdir -p $(@D)
	@echo "   LINK $@"
	@$(YOSYS_CONFIG) --exec --cxx --cxxflags --ldflags -g -o $@ \
		$(CXXFLAGS) \
		-shared $^ --ldlibs \
		build/slang_install/lib/libsvlang.a \
		build/slang_install/lib/libfmt.a

.PHONY: build configure-slang build-slang clean-slang clean-objects clean clean-all install
