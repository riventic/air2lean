/* Variadic function definition using stdarg. */
#include <stdarg.h>

static unsigned sum(int n, ...) {
    va_list ap;
    va_start(ap, n);
    unsigned s = 0;
    for (int i = 0; i < n; i++) s += va_arg(ap, unsigned);
    va_end(ap);
    return s;
}

unsigned entry(unsigned a, unsigned b) { return sum(3, a, b, 7u) + sum(1, a ^ b) + sum(0); }
