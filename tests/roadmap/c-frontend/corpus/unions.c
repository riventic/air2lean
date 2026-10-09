/* Unions: type punning between a word and its bytes, and a tagged-union pattern. */
union word { unsigned u; unsigned char b[4]; unsigned short h[2]; };

struct value { int kind; union { unsigned i; unsigned char c; } as; };

static unsigned eval(struct value v) { return v.kind == 0 ? v.as.i : v.as.c * 3u; }

unsigned entry(unsigned a, unsigned b) {
    union word w;
    w.u = a;
    w.b[0] ^= (unsigned char)b;
    unsigned r = w.u + w.h[1];
    struct value v0 = {0, {0}}, v1 = {1, {0}};
    v0.as.i = b;
    v1.as.c = (unsigned char)a;
    return r + eval(v0) + eval(v1);
}
