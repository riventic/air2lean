/* Calls into libc whose definitions in Zig's libc (lib/c/ctype.zig, lib/c/stdlib.zig) have the
   declared C types: isdigit, isalpha, isspace, toupper, tolower, abs, labs. The parentheses
   keep musl's <ctype.h> macros from replacing the calls. */
#include <ctype.h>
#include <stdlib.h>

unsigned entry(unsigned a, unsigned b) {
    static const char text[] = "Zig 0.17: libc in Zig, 42 symbols!";
    const unsigned n = sizeof text - 1;
    unsigned digits = 0, letters = 0, spaces = 0, sum = 0;
    for (unsigned i = 0; i < n; i++) {
        int c = (unsigned char)text[(i + a) % n];
        if ((isdigit)(c)) digits++;
        if ((isalpha)(c)) letters++;
        if ((isspace)(c)) spaces++;
        sum = sum * 31u + (unsigned)((i + b) % 2u ? (toupper)(c) : (tolower)(c));
    }
    int d = (int)(a % 1000u) - (int)(b % 1000u);
    long l = (long)(a % 100000u) - (long)(b % 77777u);
    return sum ^ (digits * 1000u + letters * 10u + spaces) ^ ((unsigned)abs(d) * 65537u) ^ (unsigned)labs(l);
}
