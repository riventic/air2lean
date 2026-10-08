/* Heap-allocated dynamic array with realloc growth (malloc/realloc/free). */
#include <stdlib.h>

struct vec { unsigned *data; unsigned len, cap; };

static int vec_push(struct vec *v, unsigned x) {
    if (v->len == v->cap) {
        unsigned ncap = v->cap ? v->cap * 2u : 2u;
        unsigned *nd = realloc(v->data, ncap * sizeof *nd);
        if (!nd) return 0;
        v->data = nd;
        v->cap = ncap;
    }
    v->data[v->len++] = x;
    return 1;
}

unsigned entry(unsigned a, unsigned b) {
    struct vec v = {0, 0, 0};
    for (unsigned i = 0; i < 9; i++) if (!vec_push(&v, a ^ (i * b))) return 0;
    unsigned s = v.cap;
    for (unsigned i = 0; i < v.len; i++) s = s * 7u + v.data[i];
    free(v.data);
    return s;
}
