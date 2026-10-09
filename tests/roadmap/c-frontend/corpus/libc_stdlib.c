/* Calls into libc <stdlib.h>: malloc/free, calloc, abs, qsort with a callback. */
#include <stdlib.h>

static int cmp(const void *x, const void *y) {
    unsigned a = *(const unsigned *)x, b = *(const unsigned *)y;
    return (a > b) - (a < b);
}

unsigned entry(unsigned a, unsigned b) {
    unsigned *v = malloc(6 * sizeof *v);
    if (!v) return 0;
    for (unsigned i = 0; i < 6; i++) v[i] = (a ^ (i * b)) % 97u;
    qsort(v, 6, sizeof *v, cmp);
    unsigned r = v[0] + v[5] * 100u;
    free(v);
    unsigned *z = calloc(4, sizeof *z);
    if (!z) return 1;
    r += z[3];
    free(z);
    r += (unsigned)abs((int)(a % 100u) - 50);
    return r;
}
