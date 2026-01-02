#include "multiply.hpp"

// C++ implementation with extern "C" to provide C ABI compatibility
// This allows the function to be called from C code and Lean FFI
extern "C" {
    uint32_t multiply(uint32_t a, uint32_t b) {
        return a * b;
    }
}
