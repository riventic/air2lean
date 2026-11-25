#!/usr/bin/env python3
"""T02 mutants of the retained pointer-width translations (`PointerWidth/{Wasm32,X64}/Gen.lean`).

`run WORK` takes the directory `check.sh` built the clean `PointerWidth/*/Gen.olean` files in
(LEAN_PATH must reach the Lake libraries), builds one mutated Gen.lean per mutant below it and
elaborates `PointerWidth/Proofs.lean` against it. Each mutant is well-typed Lean that changes one
width-dependent fact of one translation (the in-memory layout of a pointer and a slice, the
`usize` overflow of an addition, a bounds check or an allocation size); it is killed only when the
proofs fail in exactly the theorems that state the fact (`broken`), never by an import or a type
error. Only then it reports the kill (`kill`). `--self-test` checks every anchor.
"""
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / "scripts"))
from lean_mutant import edit, reject, run as run_lean  # noqa: E402
from mutation_kill_log import killed as log_kill  # noqa: E402

PROOFS = HERE / "PointerWidth/Proofs.lean"

# name -> (namespace, edits, theorems of Proofs.lean that must fail). Each `old` occurs exactly once.
MUTANTS = {
    # A pointer stored with the 64-bit layout: the slice moves from offset 4 to 8, the view grows.
    "wasm32-view-uses-64-bit-pointer-layout": ("Wasm32", [
        ("  size := 12\n  align := 4\n", "  size := 16\n  align := 4\n"),
        ("Zig.Enc.fields 12 [(0, Zig.Enc.encode v.first), (4, Zig.Enc.encode v.rest)]",
         "Zig.Enc.fields 16 [(0, Zig.Enc.encode v.first), (8, Zig.Enc.encode v.rest)]"),
        ("rest := ← Zig.Enc.decodeAt bs 4 }", "rest := ← Zig.Enc.decodeAt bs 8 }"),
    ], ["view_layout", "restLen_w32"]),
    # The 32-bit layout on the 64-bit target: the slice at offset 4, inside the 8-byte pointer.
    "x64-view-uses-32-bit-pointer-layout": ("X64", [
        ("(8, Zig.Enc.encode v.rest)]", "(4, Zig.Enc.encode v.rest)]"),
        ("rest := ← Zig.Enc.decodeAt bs 8 }", "rest := ← Zig.Enc.decodeAt bs 4 }"),
    ], ["restLen_x64"]),
    # `usize` addition wraps instead of reporting overflow.
    "wasm32-usize-add-wraps": ("Wasm32", [
        ("let i1 ← Zig.add false p0 (1 : BitVec 32)", "let i1 ← pure (Zig.addWrap p0 (1 : BitVec 32))"),
    ], ["succ_w32", "succ_boundary"]),
    # The byte-count overflow flag is read the wrong way round.
    "x64-byte-count-overflow-flag-inverted": ("X64", [
        ("let i4 ← pure (i3 != (0 : BitVec 1))", "let i4 ← pure (i3 == (0 : BitVec 1))"),
    ], ["byteCount_x64", "byteCount_boundary"]),
    # `index == len` passes the bounds check.
    "wasm32-bounds-check-allows-length": ("Wasm32", [
        ("let i3 ← pure (Zig.lt false p1 i2)", "let i3 ← pure (Zig.le false p1 i2)"),
    ], ["at_w32"]),
    # The allocation is requested with one-byte items: the 32-bit size check never fires at 2^30.
    "wasm32-alloc-item-size-one": ("Wasm32", [
        ("Zig.Allocator.allocOf .w32 p0 4 4 p1", "Zig.Allocator.allocOf .w32 p0 1 4 p1"),
    ], ["zeros_overflow_w32", "zeros_boundary"]),
}


def build(name, work):
    namespace, edits, broken = MUTANTS[name]
    gen = f"PointerWidth/{namespace}/Gen.lean"
    target = Path(work) / "mutants" / name
    (target / gen).parent.mkdir(parents=True, exist_ok=True)
    (target / gen).write_text(edit((HERE / gen).read_text(encoding="utf-8"), edits, name), encoding="utf-8")
    rc, out = run_lean(["-R", target, "-o", (target / gen).with_suffix(".olean"), target / gen], target, work)
    if rc != 0:
        sys.stderr.write(out[-4000:])
        raise SystemExit(f"{name}: the mutated translation does not build (an invalid mutant)")
    return target, broken


def run(work):
    for name in MUTANTS:
        target, broken = build(name, work)
        rc, out = run_lean(["-R", HERE, PROOFS], target, work)
        reject(name, rc, out, PROOFS, broken)
        log_kill("tests/roadmap/pointer-width/mutations.py", name, "tests/roadmap/pointer-width/check.sh")


def main(argv):
    if argv[1:] == ["--self-test"]:
        for name, (namespace, edits, _) in MUTANTS.items():
            source = (HERE / f"PointerWidth/{namespace}/Gen.lean").read_text(encoding="utf-8")
            assert edit(source, edits, name) != source, name
        print(f"pointer-width mutant self-test: {len(MUTANTS)}")
    elif len(argv) == 3 and argv[1] == "run":
        run(argv[2])
    else:
        raise SystemExit("usage: mutations.py --self-test | run WORK")


if __name__ == "__main__":
    main(sys.argv)
