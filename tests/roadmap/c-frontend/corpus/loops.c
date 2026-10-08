/* for / while / do-while with break and continue. */
unsigned entry(unsigned a, unsigned b) {
    unsigned acc = 0;
    for (unsigned i = 0; i < 20; i++) {
        if (i % 3 == 0) continue;
        if (i > (b & 15u) + 4u) break;
        acc += i * a;
    }
    unsigned j = 0;
    while (1) {
        j++;
        if (j >= 5) break;
        if (j == 2) continue;
        acc ^= j;
    }
    unsigned k = b & 7u;
    do {
        acc += k;
    } while (k-- > 0);
    for (unsigned x = 0; x < 3; x++)
        for (unsigned y = 0; y < 3; y++) {
            if (y == x) continue;
            acc += x * 10u + y;
        }
    return acc;
}
