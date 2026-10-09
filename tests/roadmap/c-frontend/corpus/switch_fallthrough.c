/* switch with fallthrough between non-empty cases, and Duff's device (case labels inside a loop). */
static unsigned fall(unsigned v) {
    unsigned acc = 0;
    switch (v & 3u) {
    case 0: acc += 1;
    /* fallthrough */
    case 1: acc += 10;
    /* fallthrough */
    case 2: acc += 100; break;
    case 3: acc += 1000;
    }
    return acc;
}

static unsigned duff_sum(const unsigned char *p, unsigned n) {
    unsigned s = 0;
    unsigned rounds = (n + 3u) / 4u;
    if (n == 0) return 0;
    switch (n % 4u) {
    case 0: do { s += *p++;
    case 3:      s += *p++;
    case 2:      s += *p++;
    case 1:      s += *p++;
            } while (--rounds > 0);
    }
    return s;
}

unsigned entry(unsigned a, unsigned b) {
    unsigned char data[16];
    for (unsigned i = 0; i < 16; i++) data[i] = (unsigned char)(a + i * b);
    return fall(a) + fall(b) * 7u + duff_sum(data, (a ^ b) & 15u);
}
