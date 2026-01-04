# Formal Verification for C and C++ Code Template

A template for building high-performance C/C++ projects with formal verification using Lean 4 and property-based testing.

## Overview

This template is for people who want higher confidence in C and C++ code without trying to
formally verify C or C++ itself.

The approach is to treat the Lean 4 code as the source of truth. A reference implementation is written and 
proven correct in Lean, while the real, performance-critical implementation is written in C and/or C++ with 
strict compiler settings. Property- and model-based tests then compare the behavior of the C/C++ code against 
the Lean model.

This gives you a principled workflow: specifications are precise and machine-checked, implementations are fast 
and practical, and testing becomes a way of checking refinement rather than guessing at edge cases. It works 
just as well for serious open-source or commercial code as it does for personal projects.

## Prerequisites

- Lean 4 toolchain with `lake` (install via `elan`)
- Git (for fetching Lean dependencies like mathlib/plausible)
- CMake (>= 3.22)
- C and C++ compiler with C23/C++23 support (e.g., GCC 13+/Clang 17+)
- make (for the provided Makefile targets)
- Doxygen (optional, for docs generation)
- Valgrind (optional, for memory-checking tests)

## Getting Started

> **Note:** After cloning this template, update the `CODEOWNERS` file to replace `@UniquesKernel` with your own GitHub username or team.

### Quick Start

1. **Build the C/C++ library and run basic tests:**
   ```bash
   make release      # Build optimized release
   make test         # Run differential tests comparing C/C++ to Lean specs
   ```

2. **Run the example executable:**
   ```bash
   ./build/example
   ```

3. **Build and run the Lean verification tests:**
   ```bash
   cd lean
   lake update       # Fetch Lean dependencies (mathlib, plausible)
   lake build        # Build Lean code and link to C/C++ library
   lake exe project-verification  # Run differential tests
   ```

### Build Options

- **Debug build:** `make debug`
- **With Address Sanitizer:** `make asan`
- **With Undefined Behavior Sanitizer:** `make ubsan`
- **With code coverage:** `make coverage` (see below for usage)
- **With Valgrind memory checking:** `make valgrind`
- **Generate documentation:** `make docs`
- **Clean build artifacts:** `make clean`

For more options, run `make help`.

#### Using Code Coverage

Code coverage shows which lines of your C/C++ code are executed during testing:

```bash
# 1. Create artifacts directory and clean build
mkdir -p coverage_artifacts && make clean

# 2. Build with coverage instrumentation
make coverage

# 3. Run your tests to generate coverage data
./build/example           # Run the executable
cd build && ctest         # Run CTest tests

# 4. Generate coverage reports and collect them
cd build
for f in CMakeFiles/example.dir/src/*.gcda; do 
  gcov "$f" -o $(dirname "$f")
done
mv *.gcov ../coverage_artifacts/

# 5. View results
cat coverage_artifacts/main.c.gcov       # Line-by-line coverage
ls coverage_artifacts/                    # All coverage files
```

All coverage artifacts (`.gcov` files with line-by-line execution counts) are stored in `coverage_artifacts/`. Each file shows execution count for every line (e.g., `1:` means executed once, `-:` means non-executable).

**Optional: HTML reports with lcov**

If you have `lcov` installed, generate prettier HTML reports:

```bash
cd build
lcov --capture --directory . --output-file ../coverage_artifacts/coverage.info
lcov --remove ../coverage_artifacts/coverage.info '/usr/*' --output-file ../coverage_artifacts/coverage.info
genhtml ../coverage_artifacts/coverage.info --output-directory ../coverage_artifacts/html
# Open coverage_artifacts/html/index.html in a browser
```

### Creating Your Own Lean Project

The template includes a setup script to help you create a new Lean project with the proper structure. The script:

- Checks for Lean 4 installation (installs via `elan` if missing)
- Initializes a new Lean project using `lake init`
- Creates organized folders: `{proof, specs, ffi, tests}`
- Sets up module structure with proper imports
- Converts your project name to PascalCase for modules (e.g., `my_project` → `MyProject`)

**To replace the example project:**

```bash
# Remove the existing example project
rm -rf lean/

# Create your own project (defaults to 'lean' folder)
./scripts/create_lean_project.sh my_project

# Or specify a custom folder
./scripts/create_lean_project.sh my_project my_lean_folder

# Then configure dependencies and FFI linking
cd lean  # or your custom folder
# Edit lakefile.toml to add:
# - mathlib and plausible dependencies
# - moreLinkArgs pointing to your C/C++ library
lake build
```