/* Function pointers: a constant table of operations, pointer passed as argument, typedef'd pointer. */
typedef unsigned (*binop)(unsigned, unsigned);

static unsigned add(unsigned x, unsigned y) { return x + y; }
static unsigned sub(unsigned x, unsigned y) { return x - y; }
static unsigned mul(unsigned x, unsigned y) { return x * y; }

static const binop table[3] = {add, sub, mul};

static unsigned apply(binop f, unsigned x, unsigned y) { return f(x, y); }

unsigned entry(unsigned a, unsigned b) {
    unsigned r = 0;
    for (unsigned i = 0; i < 3; i++) r += apply(table[i], a, b);
    binop g = (a & 1u) ? add : mul;
    return r ^ g(b, 3u);
}
