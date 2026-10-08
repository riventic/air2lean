/* Packet header parser: bytes copied (memcpy) into a bitfield struct, then fields decoded. */
#include <string.h>

struct hdr {
    unsigned version : 4;
    unsigned ihl : 4;
    unsigned dscp : 6;
    unsigned ecn : 2;
    unsigned length : 16;
};

unsigned entry(unsigned a, unsigned b) {
    unsigned char bytes[4] = {(unsigned char)a, (unsigned char)(a >> 8),
                              (unsigned char)b, (unsigned char)(b >> 8)};
    struct hdr h;
    memcpy(&h, bytes, sizeof h);
    unsigned score = h.version + h.ihl * 16u + h.dscp * 256u + h.ecn * 65536u;
    return score ^ h.length;
}
