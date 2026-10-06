#!/usr/bin/env python3
"""Produce standalone semantic mutations; only the root queue executes Lean."""
import argparse
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('output', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parents[3]
source = (root / 'ZigLean/Permutation.lean').read_text().split('@[simp] theorem bitReverse_bit')[0]
# Inline Vec to mutate the actual lane map used by the runtime assertions.
vec = (root / 'ZigLean/Vec.lean').read_text()
source = source.replace('import ZigLean.Vec', vec)
tests = (root / 'tests/roadmap/byte-permutation/Runtime.lean').read_text().replace('import ZigLean', '')
body = '(BitVec.ofBoolListLE (List.ofFn fun i : Fin n =>\n    a.getLsbD (byteSwapIndex n i.val))).cast (by simp)'
mutations = {
    'reverse_is_identity': ('a.reverse', 'a'),
    'swap_is_identity': (body, 'a'),
    'swap_reverses_bits': (body, 'bitReverse a'),
    'byte_index_off_by_one': ('n / 8 - 1 - i / 8', 'n / 8 - i / 8'),
    'reverse_negates_bits': ('a.reverse', '(~~~a).reverse'),
    'lane_order_reversed': ('⟨v.lanes.map f⟩', '⟨(v.lanes.map f).reverse⟩'),
}
args.output.mkdir(parents=True, exist_ok=True)
(args.output / 'control.lean').write_text(source + '\nend Zig\n' + tests)
for name, (before, after) in mutations.items():
    assert source.count(before) == 1, (name, before)
    (args.output / (name + '.lean')).write_text(source.replace(before, after) + '\nend Zig\n' + tests)
print(f'materialized {len(mutations)} permutation semantic mutants')
