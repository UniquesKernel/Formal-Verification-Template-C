#include "example.h"
#include <stdio.h>
#include <stdint.h>

int main() {
    uint32_t a = 1;
    uint32_t b = 2;
    uint32_t sum = add(a, b);
    
    printf("The sum of a = 1 and b = 2 is: %u\n", sum);
    
    return 0;
}