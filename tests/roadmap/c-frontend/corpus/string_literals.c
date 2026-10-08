/* String literals: arrays initialized from literals, pointers to literals, sizeof, escapes. */
static const char *names[] = {"zero", "one", "two", "three"};
static const char greeting[] = "hi\tthere\n";

static unsigned length(const char *s) { unsigned n = 0; while (s[n]) n++; return n; }

unsigned entry(unsigned a, unsigned b) {
    char local[] = "abc";
    local[1] = (char)('a' + (b & 7u));
    const char *p = names[a & 3u];
    unsigned r = length(p) * 100u + length(local) * 10u + (unsigned)sizeof greeting;
    r += (unsigned char)p[0] + (unsigned char)local[1] + (unsigned char)greeting[2];
    r += (unsigned char)"xyz"[b % 3u];
    return r;
}
