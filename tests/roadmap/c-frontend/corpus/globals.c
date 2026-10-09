/* Global and file-static state with constant tables and zero-initialized arrays. */
static const unsigned primes[6] = {2, 3, 5, 7, 11, 13};
static unsigned scratch[4];
unsigned global_total = 17;
struct point { int x, y; };
static struct point origin = {-1, 2};

unsigned entry(unsigned a, unsigned b) {
    global_total = 17;
    for (unsigned i = 0; i < 4; i++) scratch[i] = primes[(a + i) % 6u] * b;
    for (unsigned i = 0; i < 4; i++) global_total += scratch[i];
    origin.x += 1;
    unsigned r = global_total + (unsigned)origin.x + (unsigned)origin.y;
    origin.x -= 1;
    return r;
}
