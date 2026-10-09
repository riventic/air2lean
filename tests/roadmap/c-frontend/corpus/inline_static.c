/* static inline helpers, const qualifiers, and a block-scope typedef. */
static inline unsigned rotl(unsigned x, unsigned r) { return (x << (r & 31u)) | (x >> ((32u - r) & 31u)); }
static inline unsigned mix(unsigned h, unsigned v) { return rotl(h ^ v, 13) * 5u + 0xe6546b64u; }

unsigned entry(unsigned a, unsigned b) {
    typedef unsigned word;
    const word seed = 0x12345678u;
    word h = mix(seed, a);
    h = mix(h, b);
    h ^= h >> 16;
    return h;
}
