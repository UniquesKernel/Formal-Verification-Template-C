#include "example.h"
#include <stdint.h>

// CBMC harness for verifying safe_add function
void verify_safe_add(void) {
    // Create symbolic (non-deterministic) inputs
    // CBMC will check all possible values
    int32_t a, b, result;
    
    // Call the function under test
    bool success = safe_add(a, b, &result);
    
    // Verify properties:
    // 1. If successful, result should be mathematically correct
    //    (CBMC will verify this considering overflow)
    // 2. Function should detect overflow/underflow correctly
    
    // The assertions inside safe_add() will be verified
    // for ALL possible combinations of a and b
}

// CBMC harness for verifying find_max function
void verify_find_max(void) {
    #define MAX_ARRAY_SIZE 10
    
    // Create symbolic array
    int32_t arr[MAX_ARRAY_SIZE];
    size_t size;
    
    // Constrain size to reasonable bounds
    __CPROVER_assume(size > 0 && size <= MAX_ARRAY_SIZE);
    
    // Call function under test
    int32_t max = find_max(arr, size);
    
    // Verify postcondition: max is indeed maximum
    for (size_t i = 0; i < size; i++) {
        __CPROVER_assert(max >= arr[i], 
            "Maximum value should be >= all elements");
    }
    
    // Verify that max is actually in the array
    bool found = false;
    for (size_t i = 0; i < size; i++) {
        if (arr[i] == max) {
            found = true;
            break;
        }
    }
    __CPROVER_assert(found, "Maximum value should be in the array");
}

// CBMC harness for verifying binary search
void verify_binary_search(void) {
    #define SEARCH_ARRAY_SIZE 8
    
    // Create symbolic sorted array
    int32_t arr[SEARCH_ARRAY_SIZE];
    int32_t target;
    
    // Assume array is sorted (precondition)
    for (size_t i = 0; i < SEARCH_ARRAY_SIZE - 1; i++) {
        __CPROVER_assume(arr[i] <= arr[i + 1]);
    }
    
    // Call function under test
    int result = find_binary_search(arr, SEARCH_ARRAY_SIZE, target);
    
    // Verify postconditions:
    if (result >= 0) {
        // If found, the element at that index should equal target
        __CPROVER_assert(result < SEARCH_ARRAY_SIZE, 
            "Result index should be within bounds");
        __CPROVER_assert(arr[result] == target, 
            "Found element should equal target");
    } else {
        // If not found (-1), target should not be in array
        __CPROVER_assert(result == -1, 
            "Not found result should be -1");
        for (size_t i = 0; i < SEARCH_ARRAY_SIZE; i++) {
            __CPROVER_assert(arr[i] != target, 
                "Target should not be in array when not found");
        }
    }
}

// Main harness that can be used to verify all functions
void main_harness(void) {
    // Uncomment the function you want to verify
    // Or run CBMC with --function flag to specify
    
    verify_safe_add();
    // verify_find_max();
    // verify_binary_search();
}
