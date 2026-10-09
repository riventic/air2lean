/* 64-bit arithmetic: multiply/divide/shift on uint64_t and int64_t, mixed with 32-bit values. */
#include <stdint.h>

unsigned entry(unsigned a, unsigned b) {
    uint64_t x = ((uint64_t)a << 32) | b;
    uint64_t y = x * 0x9e3779b97f4a7c15ull;      /* wraps */
    uint64_t z = (y >> 17) ^ (x << 5);
    int64_t s = (int64_t)(a % 1000u) - 500;
    int64_t t = s * 123456789LL / 7;
    uint64_t d = b ? x / b : x;
    uint64_t m = b ? x % (uint64_t)(b | 1u) : 0;
    return (uint32_t)z ^ (uint32_t)(z >> 32) ^ (uint32_t)t ^ (uint32_t)d ^ (uint32_t)m;
}
