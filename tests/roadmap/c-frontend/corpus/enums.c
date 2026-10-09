/* Enumerations: implicit and explicit values, switch over an enum, enum arithmetic. */
enum color { RED, GREEN = 5, BLUE, ALPHA = -2 };

static unsigned weight(enum color c) {
    switch (c) {
    case RED: return 1;
    case GREEN: return 2;
    case BLUE: return 3;
    default: return 4;
    }
}

unsigned entry(unsigned a, unsigned b) {
    enum color c = (a & 1u) ? GREEN : BLUE;
    enum color d = (enum color)(b % 3u == 0 ? RED : ALPHA);
    int sum = c + d + BLUE;
    return weight(c) * 10u + weight(d) + (unsigned)sum;
}
