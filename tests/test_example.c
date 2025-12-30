#include "example.h"
#include <stdio.h>
#include <assert.h>
#include <limits.h>

#define TEST_PASS "\033[0;32m[PASS]\033[0m"
#define TEST_FAIL "\033[0;31m[FAIL]\033[0m"

static int tests_passed = 0;
static int tests_failed = 0;

void test_safe_add(void) {
    int32_t result;
    
    // Test normal addition
    if (safe_add(10, 20, &result) && result == 30) {
        printf("%s safe_add(10, 20) = 30\n", TEST_PASS);
        tests_passed++;
    } else {
        printf("%s safe_add(10, 20) failed\n", TEST_FAIL);
        tests_failed++;
    }
    
    // Test overflow detection
    if (!safe_add(INT32_MAX, 1, &result)) {
        printf("%s safe_add overflow detection\n", TEST_PASS);
        tests_passed++;
    } else {
        printf("%s safe_add overflow detection failed\n", TEST_FAIL);
        tests_failed++;
    }
    
    // Test underflow detection
    if (!safe_add(INT32_MIN, -1, &result)) {
        printf("%s safe_add underflow detection\n", TEST_PASS);
        tests_passed++;
    } else {
        printf("%s safe_add underflow detection failed\n", TEST_FAIL);
        tests_failed++;
    }
    
    // Test negative addition
    if (safe_add(-10, -20, &result) && result == -30) {
        printf("%s safe_add(-10, -20) = -30\n", TEST_PASS);
        tests_passed++;
    } else {
        printf("%s safe_add(-10, -20) failed\n", TEST_FAIL);
        tests_failed++;
    }
}

void test_find_max(void) {
    int32_t arr1[] = {1, 5, 3, 9, 2};
    if (find_max(arr1, 5) == 9) {
        printf("%s find_max with positive numbers\n", TEST_PASS);
        tests_passed++;
    } else {
        printf("%s find_max with positive numbers failed\n", TEST_FAIL);
        tests_failed++;
    }
    
    int32_t arr2[] = {-10, -5, -20, -3};
    if (find_max(arr2, 4) == -3) {
        printf("%s find_max with negative numbers\n", TEST_PASS);
        tests_passed++;
    } else {
        printf("%s find_max with negative numbers failed\n", TEST_FAIL);
        tests_failed++;
    }
    
    int32_t arr3[] = {42};
    if (find_max(arr3, 1) == 42) {
        printf("%s find_max with single element\n", TEST_PASS);
        tests_passed++;
    } else {
        printf("%s find_max with single element failed\n", TEST_FAIL);
        tests_failed++;
    }
}

void test_find_binary_search(void) {
    int32_t sorted[] = {1, 3, 5, 7, 9, 11, 13, 15};
    
    // Test finding existing elements
    if (find_binary_search(sorted, 8, 7) == 3) {
        printf("%s binary_search finds existing element\n", TEST_PASS);
        tests_passed++;
    } else {
        printf("%s binary_search finds existing element failed\n", TEST_FAIL);
        tests_failed++;
    }
    
    // Test finding first element
    if (find_binary_search(sorted, 8, 1) == 0) {
        printf("%s binary_search finds first element\n", TEST_PASS);
        tests_passed++;
    } else {
        printf("%s binary_search finds first element failed\n", TEST_FAIL);
        tests_failed++;
    }
    
    // Test finding last element
    if (find_binary_search(sorted, 8, 15) == 7) {
        printf("%s binary_search finds last element\n", TEST_PASS);
        tests_passed++;
    } else {
        printf("%s binary_search finds last element failed\n", TEST_FAIL);
        tests_failed++;
    }
    
    // Test not finding element
    if (find_binary_search(sorted, 8, 6) == -1) {
        printf("%s binary_search returns -1 for missing element\n", TEST_PASS);
        tests_passed++;
    } else {
        printf("%s binary_search returns -1 for missing element failed\n", TEST_FAIL);
        tests_failed++;
    }
    
    // Test empty array
    if (find_binary_search(sorted, 0, 5) == -1) {
        printf("%s binary_search on empty array\n", TEST_PASS);
        tests_passed++;
    } else {
        printf("%s binary_search on empty array failed\n", TEST_FAIL);
        tests_failed++;
    }
}

int main(void) {
    printf("Formal Verification Template - Test Suite\n");
    printf("==========================================\n\n");
    
    printf("Testing safe_add:\n");
    test_safe_add();
    
    printf("\nTesting find_max:\n");
    test_find_max();
    
    printf("\nTesting find_binary_search:\n");
    test_find_binary_search();
    
    printf("\n==========================================\n");
    printf("Tests passed: %d\n", tests_passed);
    printf("Tests failed: %d\n", tests_failed);
    printf("==========================================\n");
    
    return tests_failed > 0 ? 1 : 0;
}
