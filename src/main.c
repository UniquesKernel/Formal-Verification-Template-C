#include "example.h"
#include <stdio.h>
#include <stdlib.h>

int main(void) {
    printf("Formal Verification Template - Example Program\n");
    printf("==============================================\n\n");
    
    // Test safe_add
    printf("Testing safe_add:\n");
    int32_t result;
    if (safe_add(100, 200, &result)) {
        printf("  100 + 200 = %d\n", result);
    }
    if (safe_add(INT32_MAX, 1, &result)) {
        printf("  INT32_MAX + 1 = %d\n", result);
    } else {
        printf("  INT32_MAX + 1 would overflow (correctly detected)\n");
    }
    
    // Test find_max
    printf("\nTesting find_max:\n");
    int32_t arr[] = {3, 7, 1, 9, 2, 8};
    size_t arr_size = sizeof(arr) / sizeof(arr[0]);
    int32_t max = find_max(arr, arr_size);
    printf("  Max of {3, 7, 1, 9, 2, 8} = %d\n", max);
    
    // Test binary search
    printf("\nTesting find_binary_search:\n");
    int32_t sorted_arr[] = {1, 3, 5, 7, 9, 11, 13};
    size_t sorted_size = sizeof(sorted_arr) / sizeof(sorted_arr[0]);
    int idx = find_binary_search(sorted_arr, sorted_size, 7);
    printf("  Index of 7 in {1, 3, 5, 7, 9, 11, 13} = %d\n", idx);
    idx = find_binary_search(sorted_arr, sorted_size, 6);
    printf("  Index of 6 in {1, 3, 5, 7, 9, 11, 13} = %d (not found)\n", idx);
    
    printf("\nProgram completed successfully!\n");
    return 0;
}
