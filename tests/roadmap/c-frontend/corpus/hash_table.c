/* Small open-addressing hash table (FNV-1a, linear probing) with insert/lookup/update. */
#include <stdbool.h>
#include <stdint.h>

#define SLOTS 16u
struct entry_t { uint32_t key; uint32_t value; bool used; };
struct table { struct entry_t e[SLOTS]; unsigned count; };

static uint32_t fnv(uint32_t k) {
    uint32_t h = 2166136261u;
    for (int i = 0; i < 4; i++) { h ^= (k >> (i * 8)) & 0xffu; h *= 16777619u; }
    return h;
}

static bool put(struct table *t, uint32_t k, uint32_t v) {
    for (unsigned i = 0; i < SLOTS; i++) {
        struct entry_t *e = &t->e[(fnv(k) + i) % SLOTS];
        if (!e->used) { e->used = true; e->key = k; e->value = v; t->count++; return true; }
        if (e->key == k) { e->value = v; return true; }
    }
    return false;
}

static bool get(const struct table *t, uint32_t k, uint32_t *out) {
    for (unsigned i = 0; i < SLOTS; i++) {
        const struct entry_t *e = &t->e[(fnv(k) + i) % SLOTS];
        if (!e->used) return false;
        if (e->key == k) { *out = e->value; return true; }
    }
    return false;
}

unsigned entry(unsigned a, unsigned b) {
    struct table t = {0};
    for (unsigned i = 0; i < 10; i++) put(&t, a + i * 7u, b ^ i);
    put(&t, a, 12345u);
    uint32_t v = 0, r = t.count;
    for (unsigned i = 0; i < 12; i++) if (get(&t, a + i * 7u, &v)) r = r * 33u + v;
    return r;
}
