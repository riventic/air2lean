/* [*c] pointer arithmetic: increment, offset, difference, comparison, indexing through pointers. */
static unsigned sum_range(const unsigned *begin, const unsigned *end) {
    unsigned s = 0;
    while (begin < end) s += *begin++;
    return s;
}

unsigned entry(unsigned a, unsigned b) {
    unsigned buf[8];
    for (int i = 0; i < 8; i++) buf[i] = a + (unsigned)i * b;
    unsigned *p = buf + 2;
    unsigned *q = &buf[7];
    long d = q - p;              /* pointer difference */
    p[1] ^= 0x55u;               /* indexing through a pointer */
    *(q - 1) += 3u;
    return sum_range(p, q) + (unsigned)d + (unsigned)(p[-1] == buf[1]);
}
