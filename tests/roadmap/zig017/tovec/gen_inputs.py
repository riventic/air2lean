#!/usr/bin/env python3
"""Write inputs.txt for the `array_to_vector` differential: per function, arrays of edge items
(0, ±1, minInt, maxInt; for floats ±0, ±1, ±inf, the smallest subnormal, the largest finite) and
seeded random ones. A float item is its bit pattern; no NaN (a lane copy keeps any bit pattern,
but a native float register move may quiet a signalling NaN, outside this test). Deterministic."""
import random
from pathlib import Path

# name, lanes, kind ('u'/'i' width, 'bool', or float (exp bits, mantissa bits, explicit int bit)).
FUNCS = [('toVecU8', 16, ('u', 8)), ('toVecI16', 3, ('i', 16)), ('toVecU24', 3, ('u', 24)),
         ('toVecI32', 4, ('i', 32)), ('toVecU64', 2, ('u', 64)), ('toVecI128', 2, ('i', 128)),
         ('toVecU1', 8, ('u', 1)), ('toVecI7', 5, ('i', 7)), ('toVecBool', 5, ('bool',)),
         ('toVecF16', 3, ('f', 5, 10, False)), ('toVecF32', 4, ('f', 8, 23, False)),
         ('toVecF64', 2, ('f', 11, 52, False)), ('toVecF80', 2, ('f', 15, 64, True)),
         ('toVecF128', 2, ('f', 15, 112, False)), ('toVecZ8', 5, ('u', 8)), ('toVecZ16', 3, ('i', 16))]


def float_bits(exp_bits, man_bits, explicit, sign, exp, man):
    if explicit and exp != 0:
        man |= 1 << (man_bits - 1)  # f80: the integer bit of a normal number or infinity
    return (sign << (exp_bits + man_bits)) | (exp << man_bits) | man


def edges(kind):
    if kind[0] == 'bool':
        return [0, 1]
    if kind[0] in 'ui':
        bits = kind[1]
        lo, hi = (-(1 << (bits - 1)), (1 << (bits - 1)) - 1) if kind[0] == 'i' else (0, (1 << bits) - 1)
        return sorted({v for v in (0, 1, -1, lo, hi, hi // 2) if lo <= v <= hi})
    _, e, m, x = kind
    top = (1 << e) - 1
    one = (top >> 1, 0)
    vals = [(0, 0), one, (top, 0), (0, 1), (top - 1, (1 << m) - 1 if not x else (1 << (m - 1)) - 1)]
    return [float_bits(e, m, x, s, ex, mn) for s in (0, 1) for ex, mn in vals]


def random_item(rng, kind):
    if kind[0] == 'bool':
        return rng.randint(0, 1)
    if kind[0] == 'u':
        return rng.randint(0, (1 << kind[1]) - 1)
    if kind[0] == 'i':
        return rng.randint(-(1 << (kind[1] - 1)), (1 << (kind[1] - 1)) - 1)
    _, e, m, x = kind
    # Any exponent but all-ones (no NaN, no infinity); f80 normals keep their integer bit.
    return float_bits(e, m, x, rng.randint(0, 1), rng.randint(0, (1 << e) - 2),
                      rng.randint(0, (1 << (m - 1 if x else m)) - 1))


def main():
    rng = random.Random(17)
    lines = []
    for name, lanes, kind in FUNCS:
        vals = edges(kind)
        rows = [[vals[(i + j) % len(vals)] for j in range(lanes)] for i in range(len(vals))]
        rows += [[random_item(rng, kind) for _ in range(lanes)] for _ in range(20)]
        lines += [' '.join([name, *map(str, row)]) for row in rows]
    Path(__file__).with_name('inputs.txt').write_text('\n'.join(lines) + '\n')
    print(f'{len(lines)} inputs')


if __name__ == '__main__':
    main()
