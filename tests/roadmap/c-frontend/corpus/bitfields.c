/* Struct bitfields: read, write, truncation on store, mixed widths. */
struct flags {
    unsigned ready : 1;
    unsigned mode : 3;
    unsigned count : 12;
    unsigned tag : 16;
};

unsigned entry(unsigned a, unsigned b) {
    struct flags f = {0};
    f.ready = a & 1u;
    f.mode = b;              /* truncated to 3 bits */
    f.count = a >> 4;        /* truncated to 12 bits */
    f.tag = (unsigned)(a ^ b);
    f.count += 1;
    return f.ready + f.mode * 2u + f.count * 16u + ((unsigned)f.tag << 8);
}
