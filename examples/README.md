# Formal Verification with CBMC

This directory contains example formal verification harnesses for CBMC.

## What is CBMC?

CBMC (C Bounded Model Checker) is a formal verification tool for C programs that can:
- Prove the absence of bugs (for bounded executions)
- Find bugs with concrete counterexamples
- Check for array bounds violations, pointer safety, arithmetic overflow, and more

## Running Verification

### Verify all properties in a file:
```bash
cbmc -I../include ../src/example.c
```

### Verify with specific checks:
```bash
cbmc --bounds-check --pointer-check --memory-leak-check \
     --signed-overflow-check --unsigned-overflow-check \
     -I../include ../src/example.c
```

### Verify a specific function:
```bash
cbmc --function safe_add -I../include ../src/example.c
```

## Writing Verification Harnesses

Create a harness file that exercises your code with symbolic inputs:

```c
#include "example.h"

void verification_harness(void) {
    // Create symbolic inputs
    int32_t a, b, result;
    
    // Call the function under test
    bool success = safe_add(a, b, &result);
    
    // CBMC will verify all assertions in the function
    // for ALL possible values of a and b
}
```

## Assertions and Assumptions

- `__CPROVER_assert(condition, "message")` - Property to verify
- `__CPROVER_assume(condition)` - Constrain input space
- Pre/postconditions are checked automatically

## Example Verification Session

```bash
$ cbmc --function safe_add -I../include ../src/example.c
CBMC version 5.x
Parsing ../src/example.c
Converting
Type-checking safe_add
Generating GOTO Program
Starting Bounded Model Checking
...
VERIFICATION SUCCESSFUL
```

## Common Issues

1. **Unwinding assertions**: Increase unwind limit with `--unwind N`
2. **Timeout**: Reduce input space with assumptions
3. **Memory limits**: Simplify the code or use abstractions
