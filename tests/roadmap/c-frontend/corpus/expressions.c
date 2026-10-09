/* Ternaries, comma operator, compound assignment, pre/post increment inside expressions. */
unsigned entry(unsigned a, unsigned b) {
    unsigned i = a & 7u, j = b & 7u;
    unsigned arr[8] = {1, 2, 3, 4, 5, 6, 7, 8};
    unsigned x = arr[i++ & 7u] + arr[j];
    x += (i > j) ? i : j;
    unsigned y = (i++, j++, i + j);
    x <<= 2;
    x |= y;
    x -= arr[--i & 7u];
    x %= 1000003u;
    x *= 3u;
    unsigned z = ++j * 2u;
    x ^= z;
    x >>= 1;
    return x;
}
