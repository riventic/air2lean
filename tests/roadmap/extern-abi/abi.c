/* X01: C calls whose libc declaration (translate-c) and Zig libc definition agree only at the
 * C ABI. Each call passes its values through the C-ABI conversion at the bound extern call
 * (docs/c-frontend.md §libc boundary). Case `k` selects one call; the cases marked "illegal"
 * pass a value that the definition's type does not admit (Eval.lean). */
#define _GNU_SOURCE
#include <malloc.h>
#include <stdint.h>
#include <string.h>

/* strcmp: [*c]const u8 -> [*:0]const c_char (non-null, sentinel 0). */
int cmp_case(int k) {
    char s[4] = {'a', 'b', 'c', 0};
    char t[3] = {'a', 'b', 'c'};             /* no terminating 0 in its object */
    switch (k) {
    case 0: return strcmp(s, "abc");         /* 0 */
    case 1: return strcmp(s, "abd");         /* < 0 */
    case 2: return strcmp("b", s);           /* > 0 */
    case 3: return strcmp(t, "abc");         /* illegal: no sentinel */
    default: return strcmp(0, s);            /* illegal: null */
    }
}

/* strrchr: result ?[*:0]c_char -> [*c]u8 (null stays null). */
long last_case(int k, int c) {
    char words[17] = "alpha,beta,gamma";
    char *p = strrchr(k == 0 ? words : words + 6, c);
    return p ? (long)(p - words) : -1;
}

/* memrchr: ?*const anyopaque -> *const anyopaque (non-null). */
long rfind_case(int k) {
    char words[17] = "alpha,beta,gamma";
    const void *base = k == 0 ? (const void *)words : 0;
    const char *p = memrchr(base, 'a', k == 0 ? 16 : 0);  /* k != 0: illegal, null */
    return p ? (long)(p - words) : -1;
}

/* malloc_usable_size: ?*anyopaque -> ?[*]align(16) u8 (alignment 16, null admitted). The
 * block holds the header of Zig libc's malloc (lib/c/malloc.zig: alignment 4 = 16 bytes, size,
 * canary) 8 bytes before byte 16. */
unsigned long usable_case(int k, unsigned size) {
    _Alignas(16) uint64_t block[4] = {0, 4u | ((uint64_t)size << 6) | ((uint64_t)0x239 << 54), 0, 0};
    unsigned char *base = (unsigned char *)block + 16;
    switch (k) {
    case 0: return malloc_usable_size(0);     /* 0 */
    case 1: return malloc_usable_size(base);  /* size */
    default: return malloc_usable_size(base + 1);  /* illegal: misaligned */
    }
}
