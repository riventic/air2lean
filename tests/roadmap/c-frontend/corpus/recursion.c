/* Recursive and mutually recursive functions. */
static unsigned gcd(unsigned x, unsigned y) { return y == 0 ? x : gcd(y, x % y); }
static unsigned fib(unsigned n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
static int is_odd(unsigned n);
static int is_even(unsigned n) { return n == 0 ? 1 : is_odd(n - 1); }
static int is_odd(unsigned n) { return n == 0 ? 0 : is_even(n - 1); }

unsigned entry(unsigned a, unsigned b) {
    return gcd(a, b) + fib(a % 12u) * 3u + (unsigned)is_even(b % 9u) * 1000u;
}
