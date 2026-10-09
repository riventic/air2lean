/* Preprocessor macros: object-like, function-like, conditional compilation, and macros
   that translate-c cannot turn into Zig declarations (stringify, token paste). */
#define SCALE 3u
#define SQUARE(x) ((x) * (x))
#define MAX(a, b) ((a) > (b) ? (a) : (b))
#define STR(x) #x
#define CAT(a, b) a##b
#define FIELD(n) CAT(field_, n)
#if SCALE > 2
#define MODE 1
#else
#define MODE 0
#endif

struct s { unsigned field_1; unsigned field_2; };

unsigned entry(unsigned a, unsigned b) {
    struct s v = {a, b};
    unsigned r = SQUARE(a & 0xffu) + MAX(a, b) * SCALE + MODE;
    r += v.FIELD(1) == a ? 5u : 0u;
    r += v.FIELD(2);
    r += (unsigned)sizeof(STR(hello));
    return r;
}
