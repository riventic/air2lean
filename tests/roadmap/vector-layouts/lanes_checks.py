#!/usr/bin/env python3
"""Write Lanes/Checks.lean: the inputs and results that `lanes.zig`'s test checks natively, as
kernel-checked runs of the translated functions. `--check` compares with the committed file."""
import sys
from pathlib import Path

U9 = [(0, 0, 0), (0x1ff, 0, 0xaa), (0x155, 0x0aa, 0x1ff), (0xffff, 0x1234, 7)]
U3_SEEDS = [0, 0xffffff, 0x123456, 0xfac688]
U3_X = [0, 5, 7, 0xff]
U24_A = [0, 0xabcdef12, 0xffffffff]
U24_X = [0, 0x00fedcba, 0x12345678]


def u9(a, b, x):
    a9, b9, x9 = a & 0x1ff, b & 0x1ff, x & 0x1ff
    return a9 | b9 << 9 | x9 << 18 | b9 << 27 | x9 << 36


def u3(seed, x):
    x3 = x & 7
    return (seed & 0xffffff & ~(7 << 15)) | x3 << 15 | x3 << 24


def u24(a, x):
    lo, hi = a & 0xffffff, (a + 1) & 0xffffff
    return ((lo ^ hi) + (x & 0xffffff)) & 0xffffff


def checks():
    lines = [
        "import Lanes.Gen",
        "",
        "/-! The inputs and results of `lanes.zig`'s native test, as kernel-checked runs of the",
        "functions translated from the exported AIR (`lanes_checks.py` writes this file). -/",
        "",
        "private def memoryValue {α : Type} (r : Zig.MemM α) : Option α :=",
        "  ((r.run {}).run.bind Except.toOption).map Prod.fst",
        "",
    ]

    def check(call, value):
        lines.append(f"example : (memoryValue (Lanes.{call})).map BitVec.toNat = some {value} := by")
        lines.append("  decide +kernel")

    for a, b, x in U9:
        check(f"u9Lane {a:#x} {b:#x} {x:#x}", u9(a, b, x))
    for s in U3_SEEDS:
        for x in U3_X:
            check(f"u3Lane {s:#x} {x:#x}", u3(s, x))
    for a in U24_A:
        for x in U24_X:
            check(f"u24Lane {a:#x} {x:#x}", u24(a, x))
    for bits in range(32):
        check(f"boolLane {bits}", bits ^ 8)
    return "\n".join(lines) + "\n"


def main():
    path = Path(__file__).resolve().parent / "Lanes" / "Checks.lean"
    text = checks()
    if sys.argv[1:] == ["--check"]:
        if path.read_text() != text:
            sys.exit(f"{path} is stale: run {Path(__file__).name}")
        return
    if sys.argv[1:]:
        sys.exit("usage: lanes_checks.py [--check]")
    path.write_text(text)


if __name__ == "__main__":
    main()
