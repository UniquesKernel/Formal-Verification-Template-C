# Using This Template

This guide explains how to use this repository as a template for your own formal verification project.

## Creating Your Project from This Template

### On GitHub

1. Click the **"Use this template"** button at the top of this repository
2. Choose a name for your new repository
3. Select whether you want it to be public or private
4. Click **"Create repository from template"**

### Locally

If you've already created your repository from the template:

```bash
git clone https://github.com/yourusername/your-new-repo.git
cd your-new-repo
```

## Customizing the Template

### 1. Update Project Information

Edit the following files with your project information:

**README.md**
- Change the title to your project name
- Update the description
- Modify badges and links
- Add project-specific information

**CONTRIBUTING.md** (if needed)
- Add project-specific contribution guidelines
- Update contact information

### 2. Replace Example Code

The template includes example functions in `src/example.c`. You should:

1. **Keep the structure**: The directory layout is a good starting point
2. **Replace examples**: Remove or modify the example functions
3. **Add your code**: Create new `.c` and `.h` files for your project

### 3. Update the Makefile

Edit `Makefile` to match your project:

```makefile
# Change the target name
TARGET = $(BIN_DIR)/your_program_name

# Add your source files
SOURCES = $(wildcard $(SRC_DIR)/*.c)

# Adjust compiler flags if needed
CFLAGS = -Wall -Wextra -Werror -std=c11 -Iinclude
```

### 4. Customize CI/CD

Edit `.github/workflows/ci.yml`:

- Adjust build steps for your project
- Add or remove verification steps
- Configure deployment (if needed)

## Writing Your Verified Code

### Step-by-Step Workflow

1. **Create header file** (`include/yourmodule.h`)
   - Document preconditions with `@pre`
   - Document postconditions with `@post`

2. **Implement functions** (`src/yourmodule.c`)
   - Add `__CPROVER_assert()` for verification
   - Handle edge cases
   - Check for overflow, null pointers, etc.

3. **Write tests** (`tests/test_yourmodule.c`)
   - Test normal cases
   - Test edge cases
   - Test error conditions

4. **Create verification harness** (`examples/verify_yourmodule.c`)
   - Use symbolic inputs
   - Add necessary assumptions
   - Verify properties

5. **Build and test**
   ```bash
   make clean
   make
   make run
   ```

6. **Run verification**
   ```bash
   make verify
   ```

### Example: Adding a New Function

Here's how to add a safe string copy function:

**1. Header (`include/string_utils.h`):**

```c
#ifndef STRING_UTILS_H
#define STRING_UTILS_H

#include <stddef.h>
#include <stdbool.h>

/**
 * @brief Safe string copy with bounds checking
 * @pre dest != NULL && src != NULL && dest_size > 0
 * @post Destination is null-terminated
 */
bool safe_strcpy(char *dest, size_t dest_size, const char *src);

#endif
```

**2. Implementation (`src/string_utils.c`):**

```c
#include "string_utils.h"

bool safe_strcpy(char *dest, size_t dest_size, const char *src) {
    __CPROVER_assert(dest != NULL, "dest must not be NULL");
    __CPROVER_assert(src != NULL, "src must not be NULL");
    __CPROVER_assert(dest_size > 0, "dest_size must be positive");
    
    size_t i;
    for (i = 0; i < dest_size - 1 && src[i] != '\0'; i++) {
        dest[i] = src[i];
    }
    dest[i] = '\0';
    
    // Check if we copied the entire string
    return src[i] == '\0';
}
```

**3. Test (`tests/test_string_utils.c`):**

```c
#include "string_utils.h"
#include <assert.h>
#include <string.h>

void test_safe_strcpy(void) {
    char dest[10];
    
    // Test normal copy
    assert(safe_strcpy(dest, 10, "hello"));
    assert(strcmp(dest, "hello") == 0);
    
    // Test truncation
    assert(!safe_strcpy(dest, 5, "hello world"));
    assert(strcmp(dest, "hell") == 0);
}
```

**4. Verification harness (`examples/verify_string_utils.c`):**

```c
#include "string_utils.h"

void verify_safe_strcpy(void) {
    #define MAX_SIZE 10
    char dest[MAX_SIZE];
    char src[MAX_SIZE];
    size_t size;
    
    __CPROVER_assume(size > 0 && size <= MAX_SIZE);
    
    bool success = safe_strcpy(dest, size, src);
    
    // Verify destination is null-terminated
    __CPROVER_assert(dest[size-1] == '\0' || 
                     (success && dest[strlen(src)] == '\0'),
                     "destination must be null-terminated");
}
```

## Best Practices

### DO:
- ✅ Keep functions small and focused
- ✅ Document preconditions and postconditions
- ✅ Add assertions for critical properties
- ✅ Test both normal and edge cases
- ✅ Run verification regularly
- ✅ Handle errors gracefully

### DON'T:
- ❌ Make functions too complex
- ❌ Skip error checking
- ❌ Ignore verification failures
- ❌ Assume inputs are valid without checking
- ❌ Use unbounded loops without unwind limits
- ❌ Forget to document assumptions

## Common Patterns

### Pattern: Input Validation

```c
int process_data(int *data, size_t size) {
    // Validate inputs
    if (data == NULL || size == 0) {
        return -1;
    }
    
    __CPROVER_assert(data != NULL, "data validated");
    __CPROVER_assert(size > 0, "size validated");
    
    // Process data...
    return 0;
}
```

### Pattern: Overflow Checking

```c
bool safe_multiply(int a, int b, int *result) {
    __CPROVER_assert(result != NULL, "result pointer valid");
    
    // Check for overflow
    if (a > 0 && b > 0 && a > INT_MAX / b) {
        return false;
    }
    
    *result = a * b;
    return true;
}
```

### Pattern: Array Bounds

```c
int array_sum(int *arr, size_t size) {
    __CPROVER_assert(arr != NULL, "array not null");
    
    int sum = 0;
    for (size_t i = 0; i < size; i++) {
        __CPROVER_assert(i < size, "index in bounds");
        sum += arr[i];
    }
    
    return sum;
}
```

## Troubleshooting

### Build Issues

**Problem**: Compilation errors
- Check include paths in Makefile
- Verify all source files are listed
- Check C standard version (C11)

### Verification Issues

**Problem**: CBMC times out
- Reduce unwind limit
- Simplify function logic
- Add more assumptions to constrain inputs

**Problem**: Spurious verification failures
- Check loop bounds
- Verify assumptions are correct
- Review assertion logic

### Test Issues

**Problem**: Tests fail but code seems correct
- Check test expectations
- Verify edge cases
- Review error handling

## Getting Help

- Read the [Getting Started Guide](docs/GETTING_STARTED.md)
- Check the [examples](examples/) directory
- Review [CBMC documentation](https://www.cprover.org/cbmc/doc/)
- Open an issue on GitHub

## Next Steps

1. Replace example code with your own
2. Write comprehensive tests
3. Add verification properties
4. Run `make verify` regularly
5. Update documentation as you go

Happy coding! 🚀
