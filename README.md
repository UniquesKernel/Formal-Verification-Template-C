# Formal Verification Template for C

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)

A comprehensive template repository for C projects with formal verification using CBMC (C Bounded Model Checker) and other verification tools. This template provides a starting point for writing formally verified C code with examples, build configuration, and documentation.

## 🎯 Features

- **Example Code**: Sample implementations with formal verification annotations
- **Build System**: Complete Makefile with compilation and verification targets
- **Test Suite**: Unit tests for validating functionality
- **Verification Harnesses**: CBMC harnesses for formal verification
- **Documentation**: Comprehensive guides on formal verification techniques
- **CI/CD Ready**: Prepared for continuous integration workflows

## 📋 Prerequisites

- GCC or Clang compiler
- Make
- CBMC (C Bounded Model Checker) - optional but recommended

### Installing CBMC

**Ubuntu/Debian:**
```bash
sudo apt-get install cbmc
```

**macOS:**
```bash
brew install cbmc
```

**From source:** See [CBMC website](https://www.cprover.org/cbmc/)

## 🚀 Quick Start

### 1. Use This Template

Click the "Use this template" button on GitHub to create your own repository from this template.

### 2. Clone Your Repository

```bash
git clone https://github.com/yourusername/your-repo-name.git
cd your-repo-name
```

### 3. Build the Example

```bash
make
```

### 4. Run the Example

```bash
make run
```

### 5. Run Verification (requires CBMC)

```bash
make verify
```

## 📁 Project Structure

```
.
├── src/                    # Source files
│   ├── example.c          # Example implementation with verification
│   └── main.c             # Main program
├── include/               # Header files
│   └── example.h          # Example API declarations
├── tests/                 # Test files
│   └── test_example.c     # Unit tests
├── examples/              # Verification examples
│   ├── README.md          # Verification guide
│   └── verification_harness.c  # CBMC harnesses
├── docs/                  # Documentation
│   └── GETTING_STARTED.md # Detailed guide
├── Makefile               # Build and verification targets
├── .gitignore            # Git ignore rules
└── README.md             # This file
```

## 🛠️ Available Make Targets

```bash
make                 # Build release version
make debug           # Build debug version
make release         # Build release version
make run             # Build and run the program
make verify          # Run CBMC verification
make verify-function FUNC=safe_add  # Verify specific function
make clean           # Remove build artifacts
make distclean       # Remove all generated files
make help            # Show all available targets
```

## 📚 What's Included

### Example Functions

1. **safe_add** - Integer addition with overflow detection
2. **find_max** - Find maximum value in an array
3. **find_binary_search** - Binary search in a sorted array

All functions include:
- Precondition and postcondition assertions
- CBMC verification annotations
- Comprehensive documentation
- Unit tests

### Verification Features

- **Bounds checking**: Array access verification
- **Pointer safety**: Null pointer dereference detection
- **Arithmetic overflow**: Integer overflow/underflow detection
- **Memory safety**: Memory leak detection
- **Assertions**: Custom property verification

## 📖 Documentation

- **[Getting Started Guide](docs/GETTING_STARTED.md)** - Comprehensive introduction to formal verification
- **[Examples README](examples/README.md)** - How to write and run verification harnesses
- **[Source Code](src/example.c)** - Annotated examples with best practices

## 🔍 Formal Verification Workflow

1. **Write Code** with preconditions, postconditions, and assertions
2. **Compile** normally to ensure syntactic correctness
3. **Run Tests** to validate expected behavior
4. **Run CBMC** to verify properties for all possible inputs
5. **Analyze Results** and fix any issues found
6. **Iterate** until verification succeeds

## 🧪 Testing

### Run Unit Tests

Build and run the test suite:

```bash
gcc -Wall -Wextra -Iinclude tests/test_example.c src/example.c -o test_runner
./test_runner
```

### Run Formal Verification

Verify all functions:

```bash
make verify
```

Verify a specific function:

```bash
make verify-function FUNC=safe_add
```

## 📝 Example Usage

Here's a simple example of using the verified functions:

```c
#include "example.h"

int main(void) {
    int32_t result;
    
    // Safe addition with overflow checking
    if (safe_add(100, 200, &result)) {
        printf("Result: %d\n", result);
    }
    
    // Find maximum in array
    int32_t arr[] = {3, 7, 1, 9, 2};
    int32_t max = find_max(arr, 5);
    printf("Maximum: %d\n", max);
    
    return 0;
}
```

## 🔒 Security

This template emphasizes writing secure, verified code:

- **No undefined behavior**: Verified with CBMC
- **Memory safety**: All pointer accesses checked
- **Arithmetic safety**: Overflow/underflow detection
- **Input validation**: Preconditions on all public functions

## 🤝 Contributing

Contributions are welcome! Here's how you can help:

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Add your changes with verification annotations
4. Ensure `make verify` passes
5. Commit your changes (`git commit -m 'Add amazing feature'`)
6. Push to the branch (`git push origin feature/amazing-feature`)
7. Open a Pull Request

## 📄 License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## 🌟 Acknowledgments

- [CBMC](https://www.cprover.org/cbmc/) - C Bounded Model Checker
- [NASA Formal Methods](https://shemesh.larc.nasa.gov/fm/) - Formal methods research
- [MISRA C](https://www.misra.org.uk/) - C coding standards

## 📚 Additional Resources

- [CBMC Documentation](https://www.cprover.org/cbmc/doc/)
- [Formal Methods Wiki](https://en.wikipedia.org/wiki/Formal_methods)
- [SEI CERT C Coding Standard](https://wiki.sei.cmu.edu/confluence/display/c)
- [NASA's Guide to Formal Verification](https://shemesh.larc.nasa.gov/fm/index.html)

## 💡 Tips for Success

1. **Start Small**: Verify simple functions first
2. **Incremental Verification**: Add assertions gradually
3. **Document Assumptions**: Make preconditions explicit
4. **Read Error Messages**: CBMC provides detailed counterexamples
5. **Combine Approaches**: Use both testing and verification

## 🆘 Getting Help

- Check the [Getting Started Guide](docs/GETTING_STARTED.md)
- Review the [examples](examples/)
- Consult [CBMC documentation](https://www.cprover.org/cbmc/doc/)
- Open an issue on GitHub

---

**Ready to write verified code?** Start by exploring the examples and documentation!

Happy verifying! 🎉