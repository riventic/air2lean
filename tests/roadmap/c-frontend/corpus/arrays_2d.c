/* Multi-dimensional arrays, row pointers and array parameters. */
static unsigned trace(unsigned m[3][3]) { return m[0][0] + m[1][1] + m[2][2]; }

unsigned entry(unsigned a, unsigned b) {
    unsigned m[3][3];
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++) m[i][j] = a * (unsigned)i + b * (unsigned)j;
    unsigned (*row)[3] = &m[1];
    (*row)[2] += 9u;
    unsigned *flat = &m[0][0];
    unsigned s = 0;
    for (int k = 0; k < 9; k++) s += flat[k];
    return trace(m) * 7u + s;
}
