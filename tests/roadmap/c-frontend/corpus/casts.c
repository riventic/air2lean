/* Integer narrowing/widening and object-representation casts. */
#include <stdint.h>

unsigned entry(unsigned a, unsigned b) {
    int8_t s8 = (int8_t)(a & 0xff);           /* narrowing to signed: implementation-defined, two's complement */
    int32_t widened = s8;                      /* sign extension */
    uint16_t u16 = (uint16_t)b;               /* truncation */
    int64_t big = (int64_t)(int32_t)a;        /* bit reinterpretation then widen */
    uint32_t back = (uint32_t)big;
    uint32_t word = a ^ b;
    unsigned char *bytes = (unsigned char *)&word;   /* char view of an object */
    uint32_t bsum = 0;
    for (int i = 0; i < 4; i++) bsum += bytes[i];
    void *vp = &word;
    uint32_t *wp = (uint32_t *)vp;            /* void* round trip */
    return (uint32_t)widened + u16 + back + bsum + (*wp >> 1);
}
