#ifndef EXAMPLE_H
#define EXAMPLE_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

/**
 * @brief Adds two integers with overflow checking
 * 
 * @param a First integer
 * @param b Second integer
 * @param result Pointer to store the result
 * @return true if addition succeeded without overflow, false otherwise
 * 
 * @pre result != NULL
 * @post If return value is true, *result == a + b (mathematically)
 */
bool safe_add(int32_t a, int32_t b, int32_t *result);

/**
 * @brief Finds the maximum value in an array
 * 
 * @param arr Array of integers
 * @param size Size of the array
 * @return Maximum value in the array
 * 
 * @pre arr != NULL && size > 0
 * @post Return value >= arr[i] for all 0 <= i < size
 */
int32_t find_max(const int32_t *arr, size_t size);

/**
 * @brief Binary search in a sorted array
 * 
 * @param arr Sorted array of integers
 * @param size Size of the array
 * @param target Value to search for
 * @return Index of target if found, -1 otherwise
 * 
 * @pre size == 0 || arr != NULL
 * @pre Array is sorted in ascending order
 * @post If return value >= 0, then arr[return value] == target
 * @post If return value == -1, then target is not in the array
 */
int find_binary_search(const int32_t *arr, size_t size, int32_t target);

#endif /* EXAMPLE_H */
