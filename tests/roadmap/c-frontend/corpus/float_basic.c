/* Floating point: arithmetic, int<->float conversion, comparisons. */
unsigned entry(unsigned a, unsigned b) {
    double x = (double)(a % 1000u) / 8.0;
    double y = (double)(b % 1000u) * 0.5;
    float f = (float)(x + y);
    double z = x * y - f;
    unsigned r = (unsigned)(z < 0 ? -z : z);
    r += (x > y) ? 1u : 0u;
    r += (unsigned)(f * 2.0f);
    return r;
}
