.PHONY: help configure build test clean docs debug release asan ubsan coverage valgrind

BUILD_DIR = build

# Default build type
BUILD_TYPE ?= Release

help:
	@echo "Makefile Targets:"
	@echo "  configure    - Configure the project with CMake (pass options via CMAKE_OPTS)"
	@echo "  build        - Build the project (after configuring)"
	@echo "  test         - Run tests with CTest (after building)"
	@echo "  docs         - Generate Doxygen documentation"
	@echo "  clean        - Clean the build directory"
	@echo ""
	@echo "Quick Build Targets:"
	@echo "  debug        - Configure and build in Debug mode"
	@echo "  release      - Configure and build in Release mode"
	@echo "  asan         - Build with Address Sanitizer"
	@echo "  ubsan        - Build with Undefined Behavior Sanitizer"
	@echo "  coverage     - Build with code coverage enabled"
	@echo "  valgrind     - Run tests with Valgrind memory checking"
	@echo ""
	@echo "Examples:"
	@echo "  make release                    - Build optimized release"
	@echo "  make asan test                  - Build and test with ASan"
	@echo "  CMAKE_OPTS=\"-DANVIL_ENABLE_LTO=OFF\" make build  - Custom options"

configure:
	@cmake -B $(BUILD_DIR) -DCMAKE_BUILD_TYPE=$(BUILD_TYPE) $(CMAKE_OPTS) .

build: configure
	@cmake --build $(BUILD_DIR)

test: build
	@cd $(BUILD_DIR) && ctest --output-on-failure

# Quick build configurations
debug:
	@$(MAKE) BUILD_TYPE=Debug build

release:
	@$(MAKE) BUILD_TYPE=Release build

asan:
	@$(MAKE) CMAKE_OPTS="-DANVIL_ENABLE_ASAN=ON" BUILD_TYPE=Debug build

ubsan:
	@$(MAKE) CMAKE_OPTS="-DANVIL_ENABLE_UBSAN=ON" BUILD_TYPE=Debug build

coverage:
	@$(MAKE) CMAKE_OPTS="-DANVIL_ENABLE_COVERAGE=ON" BUILD_TYPE=Debug build

valgrind:
	@$(MAKE) CMAKE_OPTS="-DANVIL_ENABLE_VALGRIND=ON" test

docs:
	@doxygen Doxyfile

clean:
	@rm -rf $(BUILD_DIR) docs/doxygen
