/* State machine written with goto labels: count words and digits in a byte buffer. */
static unsigned scan(const unsigned char *p, unsigned n) {
    unsigned words = 0, digits = 0, i = 0;
start:
    if (i >= n) goto done;
    if (p[i] == ' ') { i++; goto start; }
    words++;
in_word:
    if (i >= n) goto done;
    if (p[i] >= '0' && p[i] <= '9') digits++;
    if (p[i] == ' ') goto start;
    i++;
    goto in_word;
done:
    return words * 1000u + digits;
}

unsigned entry(unsigned a, unsigned b) {
    unsigned char buf[24];
    unsigned x = a ^ (b << 1);
    for (unsigned i = 0; i < 24; i++) {
        unsigned r = (x >> (i % 29u)) & 7u;
        buf[i] = r == 0 ? ' ' : r < 4 ? (unsigned char)('0' + r) : (unsigned char)('a' + r);
    }
    return scan(buf, 24);
}
