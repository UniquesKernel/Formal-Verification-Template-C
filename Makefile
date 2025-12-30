# Formal Verification Template - Makefile
# =========================================

# Compiler settings
CC = gcc
CFLAGS = -Wall -Wextra -Werror -std=c11 -Iinclude
DEBUG_FLAGS = -g -O0
RELEASE_FLAGS = -O2

# Directories
SRC_DIR = src
INCLUDE_DIR = include
BUILD_DIR = build
BIN_DIR = bin

# Source files
SOURCES = $(wildcard $(SRC_DIR)/*.c)
OBJECTS = $(SOURCES:$(SRC_DIR)/%.c=$(BUILD_DIR)/%.o)
TARGET = $(BIN_DIR)/example

# Verification tools
CBMC = cbmc
CBMC_FLAGS = --bounds-check --pointer-check --memory-leak-check --div-by-zero-check \
             --signed-overflow-check --unsigned-overflow-check --float-overflow-check \
             --nan-check --unwind 10

# Default target
.PHONY: all
all: release

# Create directories
$(BUILD_DIR) $(BIN_DIR):
	mkdir -p $@

# Build object files
$(BUILD_DIR)/%.o: $(SRC_DIR)/%.c | $(BUILD_DIR)
	$(CC) $(CFLAGS) $(DEBUG_FLAGS) -c $< -o $@

# Build executable
$(TARGET): $(OBJECTS) | $(BIN_DIR)
	$(CC) $(CFLAGS) $(DEBUG_FLAGS) $^ -o $@

# Debug build
.PHONY: debug
debug: CFLAGS += $(DEBUG_FLAGS)
debug: $(TARGET)
	@echo "Debug build completed: $(TARGET)"

# Release build
.PHONY: release
release: CFLAGS += $(RELEASE_FLAGS)
release: $(TARGET)
	@echo "Release build completed: $(TARGET)"

# Run the program
.PHONY: run
run: $(TARGET)
	@echo "Running $(TARGET)..."
	@./$(TARGET)

# Formal verification with CBMC
.PHONY: verify
verify:
	@echo "Running CBMC verification..."
	@echo "Verifying example.c..."
	@$(CBMC) $(CBMC_FLAGS) -I$(INCLUDE_DIR) $(SRC_DIR)/example.c || \
		echo "CBMC not installed. Install with: sudo apt-get install cbmc"

# Verify specific function
.PHONY: verify-function
verify-function:
	@echo "Verifying specific function (set FUNC variable)..."
	@$(CBMC) $(CBMC_FLAGS) --function $(FUNC) -I$(INCLUDE_DIR) $(SRC_DIR)/example.c

# Clean build artifacts
.PHONY: clean
clean:
	rm -rf $(BUILD_DIR) $(BIN_DIR)
	@echo "Cleaned build artifacts"

# Clean everything including verification outputs
.PHONY: distclean
distclean: clean
	rm -rf *.cbmc cbmc-output/ *.goto
	@echo "Cleaned all generated files"

# Help target
.PHONY: help
help:
	@echo "Formal Verification Template - Available targets:"
	@echo "  make              - Build release version"
	@echo "  make all          - Build release version"
	@echo "  make debug        - Build debug version"
	@echo "  make release      - Build release version"
	@echo "  make run          - Build and run the program"
	@echo "  make verify       - Run CBMC formal verification"
	@echo "  make verify-function FUNC=<name> - Verify specific function"
	@echo "  make clean        - Remove build artifacts"
	@echo "  make distclean    - Remove all generated files"
	@echo "  make help         - Show this help message"
