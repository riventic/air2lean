/* switch with break in every case and a default. */
static unsigned classify(unsigned v) {
    switch (v % 6u) {
    case 0: return 10;
    case 1: v += 5; break;
    case 2:
    case 3: v *= 2; break;
    default: v = 1; break;
    }
    return v;
}

unsigned entry(unsigned a, unsigned b) {
    return classify(a) + classify(b) * 3u + classify(a + b);
}
