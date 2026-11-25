/* X01: extern calls whose values the C-ABI conversion does not cover (test_cli.py). */
#include <stdlib.h>
#include <string.h>
#include <wchar.h>

static int by_value(const void *a, const void *b) { return *(const int *)a - *(const int *)b; }

/* bsearch's comparator: a function pointer whose parameters differ (`?*const anyopaque` in the
 * declaration, `*const anyopaque` in Zig libc): each call through it would need a conversion. */
int search(int key) {
    int v[3] = {1, 2, 3};
    return bsearch(&key, v, 3, sizeof v[0], by_value) != 0;
}

/* wcschr: `[*:0]const wchar_t`, a sentinel of a 4-byte item, which the export does not record
 * as a value (`sentinel_byte` is for 8-bit items). */
int has_wide(const wchar_t *s, wchar_t c) { return wcschr(s, c) != 0; }

/* strcmp through a function pointer: the call passes the values unconverted. */
int via_pointer(const char *a, const char *b) {
    int (*f)(const char *, const char *) = strcmp;
    return f(a, b);
}
