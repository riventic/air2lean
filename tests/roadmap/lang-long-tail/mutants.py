#!/usr/bin/env python3
"""Semantic mutants of the retained translations (`mutants.py <work dir>`).

Each mutant changes one rule of the emitted code, elaborates it as the module
LangLongTail.<Ns> and runs Model<Ns>.lean against the committed native output of 0.16.0. A
mutant is killed only by the model's mismatch report ("differs from the model"); an
elaboration or tool failure is an error, never a kill. Run from the repository root with the
translator's Lean libraries built (check.sh does).
"""
from pathlib import Path
import os
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
LIB = HERE.parents[2] / ".lake/build/lib/lean"

MUTANTS = {
    # L10: the one-name error passed on is replaced by another name.
    "error_param_constant": ("ErrorParams", "error_params",
                             r'Zig\.call \(orBoom p0 "Boom"\)', 'Zig.call (orBoom p0 "Bang")'),
    # L09: `[4]u8` → `@Vector(4, u8)` reverses the lanes.
    "lane_order_reversed": ("VectorCasts", "vector_casts",
                            r"pure \(⟨p0⟩ : Zig\.Vec \(BitVec 8\) 4\)",
                            "pure (⟨p0.reverse⟩ : Zig.Vec (BitVec 8) 4)"),
    # L09: a cast between different item types copied lane by lane instead of reinterpreting
    # memory (`@Vector(2, u16)` → `[4]u8` keeps the low byte of each lane).
    "item_cast_lanewise": ("VectorCasts", "vector_casts",
                           r"Zig\.reprCast \(Vector \(BitVec 8\) 4\) \(p0 : Zig\.Vec \(BitVec 16\) 2\)",
                           "pure (Vector.ofFn fun i : Fin 4 => if h : i.val < 2 then "
                           "(p0.lanes[i.val]'h).truncate 8 else 0)"),
}


def run(cmd, env):
    return subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=900)


def main():
    work = Path(sys.argv[1])
    for name, (ns, stem, pattern, replacement) in MUTANTS.items():
        source = (HERE / "LangLongTail" / f"{ns}.lean").read_text()
        mutated, count = re.subn(pattern, replacement, source)
        assert count == 1, f"{name}: the pattern matched {count} times"
        root = work / name
        (root / "LangLongTail").mkdir(parents=True, exist_ok=True)
        module = root / "LangLongTail" / f"{ns}.lean"
        module.write_text(mutated)
        env = dict(os.environ, LEAN_PATH=f"{root}:{LIB}")
        built = run(["lake", "env", "lean", "-R", str(root), "-o", str(module.with_suffix(".olean")),
                     str(module)], env)
        assert built.returncode == 0, f"{name}: the mutant does not elaborate\n{built.stdout}{built.stderr}"
        result = run(["lake", "env", "lean", "--run", str(HERE / f"Model{ns}.lean"),
                      str(HERE / "native" / f"{stem}-0.16.0.txt")], env)
        killed = result.returncode == 1 and "differs from the model" in result.stderr
        assert killed, f"{name}: the mutant survived or failed otherwise\n{result.stdout}{result.stderr}"
        print(f"lang-long-tail mutant killed: {name}")


if __name__ == "__main__":
    main()
