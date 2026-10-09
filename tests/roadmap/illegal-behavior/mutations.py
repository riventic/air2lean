#!/usr/bin/env python3
"""Emitter-output mutants of the illegal-behaviour fixture (docs/illegal-behavior.md).

Each mutant rewrites the retained translation (`Gen.lean`) back to an emission that drops an op's
own illegal-behaviour check, as the translator did before. `check.sh` compiles each one and runs
`Cases.lean`, which must fail.

  python3 tests/roadmap/illegal-behavior/mutations.py GEN_LEAN OUT_DIR   # OUT_DIR/<name>/Gen.lean
"""
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True

# name -> (pattern, replacement): every one must match at least once.
MUTANTS = {
    'divexact-safe-truncates': (r'Zig\.Float\.divExactTrunc (\w+) (\w+) \(Zig\.Float\.div \1 \2\)',
                                r'pure (Zig.Float.divTrunc \1 \2)'),
    'divexact-unsafe-divides': (r'Zig\.Float\.divExactChk (\w+) (\w+) \(Zig\.Float\.div \1 \2\)',
                                r'pure (Zig.Float.div \1 \2)'),
    'memcpy-as-memmove': (r'Zig\.memcpy (\d+ \d+ \d+ \S+ \S+ \S+) \S+\)', r'Zig.memmove \1)'),
    'slice-index-unchecked': (r'Zig\.checkIndex \S+ \S+ >>= fun _ => ', ''),
    'shift-count-unchecked': (r'Zig\.shlChk (\w+) (\w+)', r'pure (Zig.shl \1 \2)'),
    'slice-end-unchecked': (r'Zig\.checkSliceEnd \S+ \S+ \S+ \d+ >>= fun _ => ', ''),
    'sentinel-unchecked': (r'Zig\.checkSentinelByte \S+ \S+ \(\d+ : BitVec 8\) >>= fun _ => ', ''),
    # The patched Sema's `for` length check (`if (!ok) unreachable`) branches to its block exit.
    'for-length-unchecked': (r'(if i\d+ then \(do\n\s+pure (\.br\d+)\)\n\s+else \(do\n\s+)throw \.illegal\)',
                             r'\1pure \2)'),
    'parent-unchecked': (r'Zig\.checkParent \d+ \d+ \(.*?\) >>= fun _ => ', ''),
}


def main():
    gen, out = Path(sys.argv[1]), Path(sys.argv[2])
    text = gen.read_text()
    for name, (pattern, repl) in MUTANTS.items():
        mutated, n = re.subn(pattern, repl, text)
        if n == 0:
            raise SystemExit(f'mutant {name}: pattern not found in {gen}')
        (out / name).mkdir(parents=True, exist_ok=True)
        (out / name / 'Gen.lean').write_text(mutated)
    return 0


if __name__ == '__main__':
    sys.exit(main())
