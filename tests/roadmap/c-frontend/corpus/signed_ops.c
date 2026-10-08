/* Signed division, remainder, shifts and comparisons (truncation toward zero). */
static int clamp_small(unsigned x) { return (int)(x % 2001u) - 1000; }

unsigned entry(unsigned a, unsigned b) {
    int x = clamp_small(a);
    int y = clamp_small(b);
    if (y == 0) y = 7;
    int q = x / y;
    int r = x % y;
    int sh = x >> 2;   /* right shift of a possibly negative value: implementation-defined, arithmetic */
    int l = (x & 0xff) << 3;
    long long w = (long long)x * (long long)y;
    unsigned res = (unsigned)q * 31u + (unsigned)r * 17u + (unsigned)sh + (unsigned)l;
    res ^= (unsigned)(w >> 3);
    res += (x < y) ? 1u : 0u;
    return res;
}
