/* goto-based error cleanup (the common Linux-kernel idiom). */
static int step(unsigned v, unsigned bit) { return (v >> bit) & 1u; }

static unsigned run(unsigned v) {
    unsigned resources = 0;
    if (!step(v, 0)) goto fail0;
    resources |= 1;
    if (!step(v, 1)) goto fail1;
    resources |= 2;
    if (!step(v, 2)) goto fail2;
    resources |= 4;
    return resources * 100u;
fail2:
    resources &= ~2u;
fail1:
    resources &= ~1u;
fail0:
    return resources + v % 7u;
}

unsigned entry(unsigned a, unsigned b) { return run(a) + run(b) * 3u; }
