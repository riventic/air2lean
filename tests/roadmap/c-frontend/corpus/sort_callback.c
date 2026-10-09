/* qsort-style generic insertion sort with a comparator callback and void* element access. */
#include <stddef.h>

typedef int (*cmp_fn)(const void *, const void *);

static void swap_bytes(unsigned char *x, unsigned char *y, size_t n) {
    while (n--) { unsigned char t = *x; *x++ = *y; *y++ = t; }
}

static void isort(void *base, size_t n, size_t size, cmp_fn cmp) {
    unsigned char *b = base;
    for (size_t i = 1; i < n; i++)
        for (size_t j = i; j > 0 && cmp(b + (j - 1) * size, b + j * size) > 0; j--)
            swap_bytes(b + (j - 1) * size, b + j * size, size);
}

static int by_value(const void *x, const void *y) {
    unsigned a = *(const unsigned *)x, b = *(const unsigned *)y;
    return (a > b) - (a < b);
}

unsigned entry(unsigned a, unsigned b) {
    unsigned v[7];
    for (unsigned i = 0; i < 7; i++) v[i] = (a * (i + 1u) ^ b) % 1000u;
    isort(v, 7, sizeof v[0], by_value);
    unsigned r = 0;
    for (unsigned i = 0; i < 7; i++) r = r * 31u + v[i];
    return r;
}
