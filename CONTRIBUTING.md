# Contributing to Formal Verification Template

Thank you for your interest in contributing! This document provides guidelines for contributing to this project.

## Code of Conduct

- Be respectful and inclusive
- Welcome newcomers and help them learn
- Focus on what is best for the community
- Show empathy towards other community members

## How to Contribute

### Reporting Bugs

If you find a bug:

1. Check if the bug has already been reported in Issues
2. If not, create a new issue with:
   - Clear title and description
   - Steps to reproduce
   - Expected vs actual behavior
   - Your environment (OS, compiler version, etc.)
   - Relevant code snippets or error messages

### Suggesting Enhancements

For feature requests:

1. Check if it's already been suggested
2. Create an issue describing:
   - The enhancement and its benefits
   - Possible implementation approach
   - Any potential drawbacks or challenges

### Pull Requests

1. **Fork and clone** the repository
2. **Create a branch** for your changes:
   ```bash
   git checkout -b feature/your-feature-name
   ```

3. **Make your changes** following our coding standards:
   - Write clear, commented code
   - Add formal verification annotations
   - Include unit tests
   - Update documentation

4. **Test your changes**:
   ```bash
   make clean
   make
   make verify  # Must pass!
   ```

5. **Commit** with a clear message:
   ```bash
   git commit -m "Add feature: description of changes"
   ```

6. **Push** to your fork:
   ```bash
   git push origin feature/your-feature-name
   ```

7. **Open a Pull Request** with:
   - Clear description of changes
   - Reference to related issues
   - Screenshots (if applicable)
   - Test results

## Coding Standards

### C Code Style

- **Standard**: C11
- **Indentation**: 4 spaces (no tabs)
- **Line length**: Max 100 characters
- **Naming**:
  - Functions: `snake_case`
  - Variables: `snake_case`
  - Constants: `UPPER_CASE`
  - Types: `snake_case_t`

### Example:

```c
#define MAX_SIZE 100

typedef struct {
    int32_t value;
    bool is_valid;
} result_t;

bool calculate_result(int32_t input, result_t *output) {
    __CPROVER_assert(output != NULL, "output must not be NULL");
    
    // Clear implementation with verification
    if (input < 0) {
        return false;
    }
    
    output->value = input * 2;
    output->is_valid = true;
    
    return true;
}
```

### Verification Requirements

All new code must:

1. **Include preconditions**: Document and assert input requirements
2. **Include postconditions**: Verify outputs and side effects
3. **Pass CBMC verification**: `make verify` must succeed
4. **Handle edge cases**: Integer overflow, null pointers, etc.
5. **Be well-documented**: Clear comments and documentation

### Documentation

- Use Doxygen-style comments for functions
- Document preconditions with `@pre`
- Document postconditions with `@post`
- Explain complex algorithms
- Update relevant README files

### Testing

- Add unit tests for new functionality
- Ensure all tests pass
- Add verification harnesses for critical functions
- Test edge cases and error conditions

## Verification Guidelines

### Writing Verifiable Code

1. **Keep functions small**: Easier to verify
2. **Explicit bounds**: Don't rely on implicit assumptions
3. **Avoid complex loops**: Use simple, bounded iterations
4. **Document assumptions**: Use `__CPROVER_assume()` in harnesses

### CBMC Assertions

```c
// Good: Specific, clear assertion
__CPROVER_assert(index >= 0 && index < size, 
                 "array index must be within bounds");

// Bad: Vague assertion
__CPROVER_assert(valid, "check failed");
```

### Loop Invariants

```c
for (size_t i = 0; i < n; i++) {
    // State what should be true at this point
    __CPROVER_assert(i < n, "loop counter within bounds");
    __CPROVER_assert(sum >= 0, "sum should be non-negative");
    
    sum += arr[i];
}
```

## Project Structure

When adding new files:

```
src/        - Implementation files (.c)
include/    - Header files (.h)
tests/      - Unit tests
examples/   - Verification harnesses and examples
docs/       - Documentation
```

## Commit Messages

Format:
```
<type>: <subject>

<body>

<footer>
```

Types:
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation changes
- `test`: Adding or updating tests
- `verify`: Verification improvements
- `refactor`: Code refactoring
- `style`: Formatting changes
- `build`: Build system changes

Example:
```
feat: Add safe division function

Implements safe_div() with zero division check and overflow
protection. Includes CBMC verification and unit tests.

Closes #42
```

## Review Process

1. Automated checks must pass (CI/CD)
2. Code review by maintainer
3. CBMC verification must succeed
4. Tests must pass
5. Documentation must be updated

## Questions?

- Open an issue for questions
- Check existing documentation
- Review examples in the repository

## License

By contributing, you agree that your contributions will be licensed under the MIT License.

## Recognition

Contributors will be acknowledged in:
- README.md contributor section
- Release notes
- Project documentation

Thank you for contributing! 🎉
