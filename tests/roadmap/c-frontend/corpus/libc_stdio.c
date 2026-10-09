/* A call to a variadic libc function (snprintf) and character classification from <ctype.h>. */
#include <ctype.h>
#include <stdio.h>

unsigned entry(unsigned a, unsigned b) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%u-%x", a, b);
    unsigned digits = 0, alphas = 0;
    for (int i = 0; i < n && buf[i]; i++) {
        if (isdigit((unsigned char)buf[i])) digits++;
        else if (isalpha((unsigned char)buf[i])) alphas++;
    }
    return (unsigned)n * 10000u + digits * 100u + alphas;
}
