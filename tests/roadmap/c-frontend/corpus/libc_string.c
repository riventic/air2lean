/* Calls into libc <string.h>: strlen, memcpy, memset, memcmp, strcmp, strchr. */
#include <string.h>

unsigned entry(unsigned a, unsigned b) {
    char buf[32];
    memset(buf, 0, sizeof buf);
    const char *src = "hello world";
    memcpy(buf, src, strlen(src) + 1);
    buf[a % 11u] = (char)('A' + b % 26u);
    unsigned r = (unsigned)strlen(buf);
    r += (unsigned)(strcmp(buf, src) != 0) * 100u;
    r += (unsigned)(memcmp(buf, src, 5) == 0) * 1000u;
    const char *o = strchr(buf, 'o');
    r += o ? (unsigned)(o - buf) * 10000u : 7u;
    return r;
}
