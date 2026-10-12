#!/usr/bin/env python3
"""F03 evidence check: the recorded native observations say what docs/research/F03.md claims.

  check.py            (needs no Zig; reads records/*.json written by observe.py)

For every record it requires, per optimize mode:
  * the strict case of every pair is the IEEE result (a NaN result is any NaN);
  * Debug and ReleaseSafe/ReleaseFast: the fast case differs from the strict case exactly for the
    cases the research note lists (`DIVERGES`), and agrees for the cases it lists as unaffected
    (`SAME`), with the documented exceptions per Zig version, target and mode (`EXCEPTIONS`);
  * a float division by zero is a trap in optimized mode wherever safety is on (Debug, ReleaseSafe).
It fails on a missing record, a missing case and any observation outside these lists.
"""
import json
import sys
from pathlib import Path

RECORDS = Path(__file__).with_name('records')

F64_NAN = 'nan'
# Strict results: the IEEE-754 binary64 result of each probe case (docs/research/F03.md).
STRICT = {
    'sum': 0x0, 'sum_cancel': 0x404f000000000000, 'fma_shape': 0x0, 'self_ne': 1, 'nan_lt': 0,
    'eq_inf': 1, 'gt_max': 1, 'mul_zero': 0x8000000000000000, 'mul_zero_nan': F64_NAN,
    'add_zero': 0x0, 'sub_self': F64_NAN, 'div_three': 0x4040aaab6cd8efb1,
    'div_zero': 0x7ff0000000000000, 'div_zero_zero': F64_NAN, 'sqrt_neg': F64_NAN,
    'mul_add': 0xbc90000000000000, 'div_trunc': 0x4040800000000000,
}
# Cases whose fast result differs from the strict one in every release mode (ReleaseSafe and
# ReleaseFast) on every record.
DIVERGES = {'sum', 'fma_shape', 'self_ne', 'nan_lt', 'eq_inf', 'mul_zero',
            'mul_zero_nan', 'sub_self', 'div_three'}
# Divergence that depends on how the optimizer vectorizes: `sum_cancel` is reassociated on
# aarch64-macos (62 -> 60) and kept in order on x86_64-linux. Both are permitted; the case shows a
# set of results, not a function.
DIVERGES_ON = {'sum_cancel': 'aarch64-macos'}
# Cases with no `_optimized` AIR tag or no flag that applies: same result (or same class of NaN).
SAME = {'gt_max', 'sqrt_neg', 'mul_add', 'div_trunc'}
# Zig 0.14.1 folds `x + 0.0` to `x` in Sema (docs/upstream/float-add-zero-fold.md): strict is -0.0.
ADD_ZERO_FOLDED = '0.14.1'
DIV_ZERO = ('div_zero', 'div_zero_zero')


def is_nan(word: int) -> bool:
    return (word >> 52) & 0x7ff == 0x7ff and word & ((1 << 52) - 1) != 0


def same(a, b) -> bool:
    if a == 'trap' or b == 'trap':
        return a == b
    ia, ib = int(a, 16), int(b, 16)
    return ia == ib or (is_nan(ia) and is_nan(ib))


def matches(word: str, want) -> bool:
    if word == 'trap':
        return False
    value = int(word, 16)
    return is_nan(value) if want == F64_NAN else value == want


def check(path: Path) -> list[str]:
    record = json.loads(path.read_text())
    zig = record['zig']
    errors = []
    for mode, results in sorted(record['results'].items()):
        where = f'{path.name}:{mode}'
        for case in STRICT:
            for variant in ('strict', 'fast'):
                if f'{case}.{variant}' not in results:
                    errors.append(f'{where}: missing {case}.{variant}')
        if errors:
            return errors
        for case, want in STRICT.items():
            strict, fast = results[f'{case}.strict'], results[f'{case}.fast']
            if case == 'add_zero' and zig == ADD_ZERO_FOLDED:
                want = 0x8000000000000000
            if case in DIV_ZERO and mode != 'ReleaseFast' and fast == 'trap':
                pass  # safety on: optimized float division by zero is a panic
            elif case in DIV_ZERO and not same(strict, fast):
                errors.append(f'{where}: {case} fast {fast} differs from strict {strict}')
            if not matches(strict, want):
                errors.append(f'{where}: {case}.strict is {strict}, IEEE says {want}')
            if case in DIV_ZERO and mode != 'ReleaseFast' and fast != 'trap':
                errors.append(f'{where}: {case}.fast should trap with safety on, got {fast}')
            if case in SAME and not same(strict, fast):
                errors.append(f'{where}: {case} differs in fast mode ({strict} vs {fast})')
            if mode == 'Debug':
                continue  # no LLVM optimizer: the rewrites below need one (but see self_ne)
            expect_diverge = case in DIVERGES or DIVERGES_ON.get(case) == record['target'] or (case == 'add_zero' and zig != ADD_ZERO_FOLDED)
            if expect_diverge and same(strict, fast):
                errors.append(f'{where}: {case} should diverge in fast mode, both are {strict}')
            if case == 'add_zero' and zig == ADD_ZERO_FOLDED and not same(strict, fast):
                errors.append(f'{where}: add_zero is folded away by Sema in 0.14.1, got {strict} / {fast}')
    return errors


def main() -> int:
    paths = sorted(RECORDS.glob('*.json'))
    if len(paths) < 10:
        print(f'only {len(paths)} records', file=sys.stderr)
        return 1
    errors = [e for p in paths for e in check(p)]
    for e in errors:
        print(e, file=sys.stderr)
    print(f'{len(paths)} records, {len(errors)} errors')
    return 1 if errors else 0


if __name__ == '__main__':
    sys.exit(main())
