# Getting Started with Formal Verification

This guide will help you understand and use formal verification techniques for C code.

## Table of Contents

1. [What is Formal Verification?](#what-is-formal-verification)
2. [Why Use Formal Verification?](#why-use-formal-verification)
3. [Tools Overview](#tools-overview)
4. [Installation](#installation)
5. [Basic Workflow](#basic-workflow)
6. [Writing Verifiable Code](#writing-verifiable-code)
7. [Common Patterns](#common-patterns)
8. [Best Practices](#best-practices)

## What is Formal Verification?

Formal verification is a mathematical approach to proving the correctness of software. Unlike testing, which checks specific inputs, formal verification can prove properties hold for **all possible inputs** within a bounded execution.

## Why Use Formal Verification?

- **Exhaustive Coverage**: Tests all possible inputs (within bounds)
- **Bug Detection**: Finds edge cases that tests might miss
- **Security**: Proves absence of common vulnerabilities
- **Safety Critical**: Essential for medical, automotive, aerospace software
- **Documentation**: Assertions serve as executable specifications

## Tools Overview

### CBMC (C Bounded Model Checker)

- **Best for**: Finding bugs, proving safety properties
- **Approach**: Bounded model checking, SAT/SMT solving
- **Checks**: Array bounds, pointer safety, arithmetic overflow, assertions
- **Website**: https://www.cprover.org/cbmc/

### Frama-C

- **Best for**: Complex functional properties, code analysis
- **Approach**: Abstract interpretation, deductive verification
- **Features**: ACSL specification language, multiple analyzers
- **Website**: https://frama-c.com/

### TIS Interpreter

- **Best for**: Undefined behavior detection
- **Approach**: Abstract interpretation
- **Checks**: All undefined behaviors in C standard

## Installation

### CBMC

**Ubuntu/Debian:**
```bash
sudo apt-get install cbmc
```

**macOS:**
```bash
brew install cbmc
```

**From source:**
```bash
git clone https://github.com/diffblue/cbmc.git
cd cbmc
make -C src
```

### Frama-C

**Ubuntu/Debian:**
```bash
sudo apt-get install frama-c
```

**macOS:**
```bash
brew install frama-c
```

**Using OPAM:**
```bash
opam install frama-c
```

## Basic Workflow

### 1. Write Code with Assertions

```c
bool safe_add(int32_t a, int32_t b, int32_t *result) {
    __CPROVER_assert(result != NULL, "result must not be NULL");
    
    if (a > 0 && b > INT32_MAX - a) {
        return false;
    }
    
    *result = a + b;
    return true;
}
```

### 2. Run Verification

```bash
cbmc -I../include ../src/example.c
```

### 3. Analyze Results

- **VERIFICATION SUCCESSFUL**: All properties verified ✓
- **VERIFICATION FAILED**: Bug found with counterexample
- **Timeout/Memory**: Need to adjust bounds or simplify

### 4. Fix Issues and Reverify

If verification fails:
1. Examine the counterexample
2. Fix the bug or strengthen preconditions
3. Re-run verification

## Writing Verifiable Code

### Preconditions and Postconditions

```c
/**
 * @pre arr != NULL && size > 0
 * @post return value >= arr[i] for all i
 */
int32_t find_max(const int32_t *arr, size_t size) {
    __CPROVER_assert(arr != NULL, "precondition: arr not NULL");
    __CPROVER_assert(size > 0, "precondition: size > 0");
    
    int32_t max = arr[0];
    for (size_t i = 1; i < size; i++) {
        if (arr[i] > max) {
            max = arr[i];
        }
    }
    
    // Verify postcondition
    for (size_t i = 0; i < size; i++) {
        __CPROVER_assert(max >= arr[i], "postcondition: max >= all");
    }
    
    return max;
}
```

### Loop Invariants

```c
int sum_array(int *arr, size_t size) {
    int sum = 0;
    
    for (size_t i = 0; i < size; i++) {
        // Loop invariant: sum equals sum of arr[0..i-1]
        sum += arr[i];
        
        __CPROVER_assert(i < size, "i within bounds");
    }
    
    return sum;
}
```

### Handling Overflow

```c
bool safe_multiply(int32_t a, int32_t b, int32_t *result) {
    // Check for overflow before multiplication
    if (a > 0 && b > 0 && a > INT32_MAX / b) {
        return false;
    }
    if (a < 0 && b > 0 && a < INT32_MIN / b) {
        return false;
    }
    if (a > 0 && b < 0 && b < INT32_MIN / a) {
        return false;
    }
    if (a < 0 && b < 0 && a < INT32_MAX / b) {
        return false;
    }
    
    *result = a * b;
    return true;
}
```

## Common Patterns

### 1. Null Pointer Checks

```c
__CPROVER_assert(ptr != NULL, "pointer must not be NULL");
```

### 2. Array Bounds

```c
__CPROVER_assert(index >= 0 && index < size, "index in bounds");
```

### 3. Arithmetic Safety

```c
__CPROVER_assert(a <= INT32_MAX - b, "addition won't overflow");
```

### 4. Constraining Inputs

```c
// In verification harness
__CPROVER_assume(size > 0 && size < MAX_SIZE);
```

## Best Practices

### 1. Start Simple
- Verify small functions first
- Build up to complex systems
- Use modular verification

### 2. Use Meaningful Assertions
```c
// Bad: Generic message
__CPROVER_assert(x > 0, "assertion failed");

// Good: Specific property
__CPROVER_assert(x > 0, "balance must be positive");
```

### 3. Document Assumptions
- Use `__CPROVER_assume()` for preconditions in harnesses
- Document why assumptions are valid
- Don't over-constrain (hides bugs)

### 4. Manage Complexity
- Break large functions into smaller ones
- Use function contracts
- Limit loop bounds with `--unwind`

### 5. Combine with Testing
- Use formal verification for critical properties
- Use testing for integration and user scenarios
- Complement each other

## Resources

- [CBMC Documentation](https://www.cprover.org/cbmc/doc/)
- [NASA's Guide to FV](https://shemesh.larc.nasa.gov/fm/index.html)
- [SEI CERT C Coding Standard](https://wiki.sei.cmu.edu/confluence/display/c)
- [Formal Methods Europe](https://www.fmeurope.org/)

## Next Steps

1. Read through the example code in `src/example.c`
2. Try running `make verify` to see CBMC in action
3. Write your own verified function
4. Create a verification harness in `examples/`
5. Experiment with different CBMC flags

## Getting Help

- Check CBMC error messages carefully
- Start with `--bounds-check` only, add checks incrementally
- Use `--trace` to see counterexample execution
- Consult the CBMC manual for advanced features
