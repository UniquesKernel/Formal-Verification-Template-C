#include "example.h"
#include "multiply.hpp"
#include <stdio.h>
#include <stdint.h>

int main() {
    uint32_t a = 1;
    uint32_t b = 2;
    uint32_t sum = add(a, b);
    
    uint32_t c = 3;
    uint32_t d = 4;
    uint32_t product = multiply(c, d);

    printf("The sum of a = 1 and b = 2 is: %u\n", sum);
    printf("The product of c = 3 and d = 4 is: %u\n", product);
    
    return 0;
}