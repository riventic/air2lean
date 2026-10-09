#!/usr/bin/env python3
"""Write inputs.txt for the `@divCeil` differential: per function, every pair of edge values
(0, ±1, ±2, ±3, minInt, minInt+1, maxInt, maxInt-1) and seeded random pairs. Deterministic."""
import random
from pathlib import Path

FUNCS = [('divCeilI8', True, 8), ('divCeilU8', False, 8), ('divCeilI32', True, 32),
         ('divCeilU32', False, 32), ('divCeilI64', True, 64), ('divCeilU64', False, 64),
         ('divCeilI13', True, 13)]


def edges(signed, bits):
    lo, hi = (-(1 << (bits - 1)), (1 << (bits - 1)) - 1) if signed else (0, (1 << bits) - 1)
    vals = {0, 1, 2, 3, 7, lo, lo + 1, hi, hi - 1, hi // 2}
    if signed:
        vals |= {-1, -2, -3, -7, lo // 2}
    return sorted(v for v in vals if lo <= v <= hi), lo, hi


def main():
    rng = random.Random(17)
    lines = []
    for name, signed, bits in FUNCS:
        vals, lo, hi = edges(signed, bits)
        pairs = [(a, b) for a in vals for b in vals]
        for _ in range(40):
            pairs.append((rng.randint(lo, hi), rng.randint(lo, hi)))
            small = min(hi, 50)
            pairs.append((rng.randint(lo, hi), rng.randint(-small if signed else 1, small)))
        lines += [f'{name} {a} {b}' for a, b in pairs]
    Path(__file__).with_name('inputs.txt').write_text('\n'.join(lines) + '\n')
    print(f'{len(lines)} inputs')


if __name__ == '__main__':
    main()
