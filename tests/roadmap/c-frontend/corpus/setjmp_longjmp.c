/* Non-local exit with setjmp/longjmp. */
#include <setjmp.h>

static jmp_buf env;

static void check(unsigned v) {
    if (v % 5u == 3u) longjmp(env, 1);
}

unsigned entry(unsigned a, unsigned b) {
    volatile unsigned progress = 0;
    if (setjmp(env) != 0) return 1000u + progress;
    for (unsigned i = 0; i < 4; i++) {
        progress += i;
        check(a + b + i);
    }
    return progress;
}
