/* Function-scope static variables that persist across calls. `entry` resets them first so
   every call is independent (the harness checks entry is idempotent per input). */
static unsigned counter(unsigned step, int reset) {
    static unsigned count;
    static unsigned history[4];
    static unsigned calls = 0;
    if (reset) {
        count = calls = 0;
        for (unsigned i = 0; i < 4; i++) history[i] = 0;
        return 0;
    }
    calls++;
    history[count & 3u] = step;
    count += step;
    return count + history[0] + calls;
}

unsigned entry(unsigned a, unsigned b) {
    unsigned r = counter(0, 1);
    r += counter(a & 15u, 0);
    r += counter(b & 15u, 0);
    r += counter(1, 0);
    return r;
}
