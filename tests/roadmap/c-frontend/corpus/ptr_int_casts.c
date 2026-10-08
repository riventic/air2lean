/* Pointer <-> integer casts: uintptr_t round trip, alignment test, NULL comparisons. */
#include <stddef.h>
#include <stdint.h>

static unsigned data[4];

unsigned entry(unsigned a, unsigned b) {
    for (unsigned i = 0; i < 4; i++) data[i] = a + i * b;
    uintptr_t addr = (uintptr_t)&data[1];
    unsigned aligned = (addr % _Alignof(unsigned)) == 0;
    unsigned *back = (unsigned *)(addr + sizeof(unsigned));   /* &data[2] */
    unsigned *none = NULL;
    unsigned r = *back + aligned * 1000u;
    if (none == NULL) r += 7u;
    if ((void *)back != (void *)0) r ^= 0x100u;
    return r;
}
