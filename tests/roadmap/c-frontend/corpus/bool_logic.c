/* Short-circuit logic, comparisons as int values, _Bool conversions. */
#include <stdbool.h>

static unsigned calls;
static bool touch(bool v) { calls++; return v; }

unsigned entry(unsigned a, unsigned b) {
    calls = 0;
    bool p = a > b;
    bool q = (a & 1u) && touch(b != 0);
    bool r = (b & 1u) || touch(a == b);
    int as_int = (a == b) + (a != b) * 2 + !a * 4 + (p ^ q) * 8;
    _Bool from_int = (_Bool)(a & 6u);
    return (unsigned)as_int + q * 16u + r * 32u + from_int * 64u + calls * 128u;
}
