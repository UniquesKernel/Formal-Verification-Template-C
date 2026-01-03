#ifndef MULTIPLY_HPP
#define MULTIPLY_HPP


#ifdef __cplusplus
extern "C" {
#endif

    #include <stdint.h>
    // C++ implementation with extern "C" to provide C ABI compatibility
    // This allows the function to be called from C code and Lean FFI
    uint32_t multiply(uint32_t a, uint32_t b);

#ifdef __cplusplus
}
#endif

#endif // MULTIPLY_HPP
