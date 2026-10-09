/* Fixed-capacity ring buffer with power-of-two masking and out-parameters. */
#include <stdbool.h>

#define CAP 8u
struct ring { unsigned data[CAP]; unsigned head, tail; };

static bool ring_push(struct ring *r, unsigned v) {
    if (r->tail - r->head == CAP) return false;
    r->data[r->tail++ & (CAP - 1u)] = v;
    return true;
}
static bool ring_pop(struct ring *r, unsigned *out) {
    if (r->head == r->tail) return false;
    *out = r->data[r->head++ & (CAP - 1u)];
    return true;
}

unsigned entry(unsigned a, unsigned b) {
    struct ring r = {{0}, 0, 0};
    unsigned acc = 0, v;
    for (unsigned i = 0; i < 11; i++) acc += ring_push(&r, a + i) ? 1u : 100u;
    for (unsigned i = 0; i < 5; i++) if (ring_pop(&r, &v)) acc += v * (b | 1u);
    for (unsigned i = 0; i < 3; i++) acc += ring_push(&r, b ^ i) ? 1u : 100u;
    while (ring_pop(&r, &v)) acc ^= v;
    return acc;
}
