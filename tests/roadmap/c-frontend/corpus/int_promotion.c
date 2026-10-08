/* Integer promotions and the usual arithmetic conversions. */
unsigned entry(unsigned a, unsigned b) {
    unsigned char c = (unsigned char)a;
    unsigned char d = (unsigned char)b;
    unsigned short s = (unsigned short)(a >> 8);
    int promoted = c + d;              /* unsigned char + unsigned char -> int, no wrap */
    unsigned char wrapped = (unsigned char)(c + d);   /* wraps on conversion */
    int neg = -1;
    unsigned r = 0;
    if ((unsigned)neg > a) r += 1;    /* -1 converted to UINT_MAX */
    if (c < -1) r += 2;                /* c promoted to int: never true */
    unsigned short ss = (unsigned short)(s * 3u);
    r += (unsigned)promoted * 7u + wrapped + ss;
    r += (unsigned)(~c & 0xffff);      /* ~ on promoted int */
    return r;
}
