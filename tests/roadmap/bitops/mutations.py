#!/usr/bin/env python3
"""Materialize standalone semantic mutants; the root validation queue compiles them.
No subprocess/compiler invocation occurs in this producer.
"""
import argparse
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("output", type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parents[3]
source = (root / "ZigLean/Bit.lean").read_text().split("private theorem resize_width_count")[0]
tests = (root / "tests/roadmap/bitops/Runtime.lean").read_text().replace("import ZigLean", "")
mutations = {
    "clz_is_ctz": ("a.clz.setWidth m", "a.ctz.setWidth m"),
    "ctz_is_clz": ("a.ctz.setWidth m", "a.clz.setWidth m"),
    "population_is_zero": ("a.cpop.setWidth m", "0"),
    "signed_shift_is_unsigned": ("shr s r b = a", "shr false r b = a"),
    "overflow_flag_inverted": ("then 0 else 1", "then 1 else 0"),
    "oversized_shift_allowed": ("if b.toNat < n ∨ b.toNat = 0 then", "if true then"),
}
args.output.mkdir(parents=True, exist_ok=True)
(args.output / "control.lean").write_text(source + "\nend Zig\n" + tests)
for name, (before, after) in mutations.items():
    assert source.count(before) == 1, (name, before)
    (args.output / (name + ".lean")).write_text(source.replace(before, after) + "\nend Zig\n" + tests)
print(f"materialized {len(mutations)} bitops semantic mutants")
