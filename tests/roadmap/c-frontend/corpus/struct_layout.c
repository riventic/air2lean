/* Struct layout: padding, nested structs, arrays in structs, sizeof/_Alignof/offsetof, struct copy. */
#include <stddef.h>
#include <stdint.h>

struct inner { uint8_t a; uint32_t b; uint16_t c; };
struct outer { char tag; struct inner in[2]; uint64_t wide; };

static uint32_t total(const struct outer *o) {
    return o->in[0].a + o->in[0].b + o->in[1].c + (uint32_t)o->wide + (uint32_t)o->tag;
}

unsigned entry(unsigned a, unsigned b) {
    struct outer o = {'x', {{1, a, 3}, {4, b, (uint16_t)(a + b)}}, ((uint64_t)a << 32) | b};
    struct outer copy = o;     /* struct assignment */
    copy.in[1].c ^= 0xffu;
    unsigned layout = (unsigned)sizeof(struct inner) * 1000u + (unsigned)sizeof(struct outer) * 10u
                    + (unsigned)_Alignof(struct outer) + (unsigned)offsetof(struct outer, wide);
    return total(&o) + total(&copy) + layout;
}
