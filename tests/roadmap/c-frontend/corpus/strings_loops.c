/* Hand-written strlen/strcpy/strcmp/strrev loops over char pointers. */
static unsigned my_strlen(const char *s) { const char *p = s; while (*p) p++; return (unsigned)(p - s); }
static char *my_strcpy(char *d, const char *s) { char *r = d; while ((*d++ = *s++)) {} return r; }
static int my_strcmp(const char *a, const char *b) {
    while (*a && *a == *b) { a++; b++; }
    return (unsigned char)*a - (unsigned char)*b;
}
static void my_strrev(char *s) {
    char *e = s + my_strlen(s);
    while (s < e) { char t = *s; *s++ = *--e; *e = t; }
}

unsigned entry(unsigned a, unsigned b) {
    char buf[16];
    char src[9];
    for (unsigned i = 0; i < 8; i++) src[i] = (char)('a' + ((a >> (i * 3u)) + b) % 26u);
    src[(b & 7u) + 1u] = 0;
    src[8] = 0;
    my_strcpy(buf, src);
    my_strrev(buf);
    unsigned r = my_strlen(buf) * 1000u;
    r += (unsigned)(my_strcmp(buf, src) + 100) * 3u;
    return r + (unsigned char)buf[0];
}
