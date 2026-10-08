/* Designated initializers, compound literals and nested aggregate initialization. */
struct pt { int x, y; };
struct rect { struct pt lo, hi; unsigned tag[3]; };

static int area(struct rect r) { return (r.hi.x - r.lo.x) * (r.hi.y - r.lo.y); }

unsigned entry(unsigned a, unsigned b) {
    struct rect r = {.hi = {.y = (int)(b & 63u), .x = (int)(a & 63u)}, .tag = {[2] = 9}};
    unsigned arr[6] = {[1] = 4, [4] = 7};
    int s = area(r) + area((struct rect){.lo = {1, 1}, .hi = {4, 5}});
    const struct pt *p = &(struct pt){(int)(a % 10u), 3};
    return (unsigned)s + arr[1] + arr[4] + r.tag[2] + (unsigned)p->x * 100u;
}
