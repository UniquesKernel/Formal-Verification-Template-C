#include "example.h"
#include <stddef.h>
#include <limits.h>

// CBMC verification functions (no-ops when compiled normally)
#ifndef __CPROVER_assume
#define __CPROVER_assume(x) ((void)0)
#endif

#ifndef __CPROVER_assert
#define __CPROVER_assert(x, msg) ((void)0)
#endif

bool safe_add(int32_t a, int32_t b, int32_t *result) {
    // Precondition
    __CPROVER_assert(result != NULL, "result pointer must not be NULL");
    
    // Check for overflow
    if (a > 0 && b > INT32_MAX - a) {
        return false; // Would overflow
    }
    if (a < 0 && b < INT32_MIN - a) {
        return false; // Would underflow
    }
    
    *result = a + b;
    
    // Postcondition: verify the result is correct
    __CPROVER_assert(*result == a + b, "result should equal a + b");
    
    return true;
}

int32_t find_max(const int32_t *arr, size_t size) {
    // Preconditions
    __CPROVER_assert(arr != NULL, "array must not be NULL");
    __CPROVER_assert(size > 0, "array size must be positive");
    
    int32_t max = arr[0];
    
    for (size_t i = 1; i < size; i++) {
        if (arr[i] > max) {
            max = arr[i];
        }
        
        // Loop invariant: max is the maximum of arr[0..i]
        __CPROVER_assert(max >= arr[i], "max should be >= current element");
    }
    
    // Postcondition: verify max is indeed the maximum
    for (size_t i = 0; i < size; i++) {
        __CPROVER_assert(max >= arr[i], "max should be >= all elements");
    }
    
    return max;
}

int find_binary_search(const int32_t *arr, size_t size, int32_t target) {
    // Preconditions
    __CPROVER_assert(arr != NULL || size == 0, "array must not be NULL if size > 0");
    
    if (size == 0) {
        return -1;
    }
    
    size_t left = 0;
    size_t right = size - 1;
    
    while (left <= right) {
        // Prevent overflow in midpoint calculation
        size_t mid = left + (right - left) / 2;
        
        // Loop invariants
        __CPROVER_assert(mid < size, "mid must be within bounds");
        __CPROVER_assert(left <= right, "left must be <= right");
        
        if (arr[mid] == target) {
            // Postcondition: found element
            __CPROVER_assert(arr[mid] == target, "found element must equal target");
            return (int)mid;
        } else if (arr[mid] < target) {
            if (mid == SIZE_MAX) break; // Prevent overflow
            left = mid + 1;
        } else {
            if (mid == 0) break; // Prevent underflow
            right = mid - 1;
        }
        
        if (right == SIZE_MAX) break; // Handle wraparound
    }
    
    // Postcondition: target not found
    return -1;
}
