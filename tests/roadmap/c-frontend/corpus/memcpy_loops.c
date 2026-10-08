/* memcpy/memmove/memset style byte loops over void*, including overlapping moves. */
#include <stddef.h>

static void *my_memcpy(void *d, const void *s, size_t n) {
    unsigned char *dp = d; const unsigned char *sp = s;
    while (n--) *dp++ = *sp++;
    return d;
}
static void *my_memmove(void *d, const void *s, size_t n) {
    unsigned char *dp = d; const unsigned char *sp = s;
    if (dp < sp) while (n--) *dp++ = *sp++;
    else { dp += n; sp += n; while (n--) *--dp = *--sp; }
    return d;
}
static void *my_memset(void *d, int c, size_t n) {
    unsigned char *p = d;
    for (size_t i = 0; i < n; i++) p[i] = (unsigned char)c;
    return d;
}

unsigned entry(unsigned a, unsigned b) {
    unsigned char buf[32];
    my_memset(buf, (int)(a & 0xffu), sizeof buf);
    unsigned words[2] = {a, b};
    my_memcpy(buf + 4, words, sizeof words);
    my_memmove(buf + 6, buf + 4, 10);
    my_memmove(buf + 1, buf + 3, 8);
    unsigned h = 2166136261u;
    for (unsigned i = 0; i < 32; i++) h = (h ^ buf[i]) * 16777619u;
    return h;
}
