#!/usr/bin/env python3
"""Semantic mutants of the retained E02 translations (`Callbacks/Gen.lean`, `Callbacks/Async.lean`),
of A01's `asm-effects/AsmEnv/Gen.lean` and of M04's `interfaces/Interfaces/{Sentinel,Wide,Grow}.lean`.

`generate ROOT OUT` writes, per mutant of the fixture ROOT (`callbacks`, `asm-env`, `sentinel`), a mutated
copy of its module under `OUT/<name>/<Module path>` and prints `name:<Module path>:<Proofs path>`.
Each mutant is well-typed Lean that changes one semantic point. `classify NAME STATUS LOG PROOFS`
requires that Lean rejected the unchanged proofs, with every located error inside the targeted
theorems and at least one in each. `--self-test` checks every anchor.
"""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROADMAP = Path(__file__).resolve().parents[1]

# fixture -> name -> (module path, proofs path, [(scope, old, new)], must fail, may fail)
MUTANTS = {
    "callbacks": {
        # The registry model's arm dropped: a pointer to `ext_visit` no longer runs its contract.
        "model_arm_dropped": ("Callbacks/Gen.lean", "Callbacks/Proofs.lean",
            [("def evaluate", "if p0 == (⟨some 1, 0⟩ : Zig.Ptr) then Zig.callM (air2lean_model_0 p1 p2) else ", "")],
            {"evaluate_eq"}, {"evaluate_spec"}),
        # An unknown function pointer given an empty effect instead of `.illegal`.
        "unknown_admitted": ("Callbacks/Gen.lean", "Callbacks/Proofs.lean",
            [("def evaluate", "else throw .illegal)", "else pure true)")],
            {"evaluate_eq"}, {"evaluate_spec"}),
        # The asynchronous call without its footprint claim (EXT-04).
        "claim_dropped": ("Callbacks/Async.lean", "Callbacks/AsyncProofs.lean",
            [("def air2lean_model_0 ", "Zig.External.claim p0 .write *> ", "")],
            {"model_claims"}, {"worker_spec", "worker_eq"}),
    },
    "asm-env": {
        # rdtsc as one repeatable value: the counter read replaced by a constant.
        "env_read_constant": ("AsmEnv/Gen.lean", "AsmEnv/Proofs.lean",
            [("def ticks", "Zig.callM (Zig.Asm.envWord 64 >>= fun e0 => pure (e0))", "pure (0 : BitVec 64)")],
            {"elapsed_eq"}, {"elapsed_counter", "elapsed_not_repeatable"}),
        # The region write of `rep stosb` dropped.
        "region_write_dropped": ("AsmEnv/Gen.lean", "AsmEnv/Proofs.lean",
            [("def fill ", "    Zig.callM (Zig.Asm.writeRegion a7o0 ((a7o1).toNat) a7.2.2)\n", "")],
            {"fill_eq"}, {"fill_frame", "fill_zero"}),
        # The overlap guard of `rep movsb` dropped.
        "region_guard_dropped": ("AsmEnv/Gen.lean", "AsmEnv/Proofs.lean",
            [("def copy ", "    Zig.Asm.guard [(a9o0, (a9o2).toNat), (a9o1, (a9o2).toNat)]\n", "")],
            {"copy_eq"}, {"copy_frame", "copy_overlap"}),
    },
    # M04: the translated `std.mem.Allocator.allocSentinel` path (real std code, 0.17.1) under
    # `SentinelSpec`'s every-allocator contract proofs.
    "sentinel": {
        # `allocWithOptionsRetAddr` asks for `n` bytes instead of `n + 1`: no room for the sentinel.
        "sentinel-alloc-omits-extra-byte": ("Interfaces/Sentinel.lean", "Interfaces/SentinelSpec.lean",
            [("def mem_Allocator_allocWithOptionsRetAddr__", "    let i3 ← Zig.add false p1 (1 : BitVec 64)\n",
              "    let i3 ← pure p1\n")],
            {"make_spec"}, set()),
        # The sentinel is stored at item 0 instead of after the `n` items.
        "sentinel-stored-at-item-0": ("Interfaces/Sentinel.lean", "Interfaces/SentinelSpec.lean",
            [("def mem_Allocator_allocWithOptionsRetAddr__", "Zig.ptrProject v15.ptr (·.elem 1 p1))",
              "Zig.ptrProject v15.ptr (·.elem 1 0))")],
            {"make_spec"}, set()),
        # The same path for item types wider than a byte (`Interfaces/Wide.lean`: one copy of the
        # wrappers per item type) under `WideSpec`, where bytes and items differ.
        # `allocWithSizeAndAlignment` of `u32` asks for one byte per item instead of four.
        "wide-alloc-bytes-are-item-count": ("Interfaces/Wide.lean", "Interfaces/WideSpec.lean",
            [("def mem_Allocator_allocWithSizeAndAlignment__anon_7f4b76fbd810",
              "math_mul__anon_44faaf286c79 (4 : BitVec 64) p1", "math_mul__anon_44faaf286c79 (1 : BitVec 64) p1")],
            {"make32_spec"}, {"realloc32_spec"}),
        # `allocBytesAligned` of `u32` asks the allocator for alignment 1 instead of 4.
        "wide-alloc-alignment-is-one": ("Interfaces/Wide.lean", "Interfaces/WideSpec.lean",
            [("def mem_Allocator_allocBytesAligned__anon_c9141768de1a",
              "mem_Alignment.«4» p2", "mem_Alignment.«1» p2")],
            {"make32_spec"}, {"realloc32_spec"}),
        # The `u32` sentinel is stored at byte `n` instead of item `n` (byte `4 * n`).
        "wide-sentinel-at-byte-n": ("Interfaces/Wide.lean", "Interfaces/WideSpec.lean",
            [("def mem_Allocator_allocWithOptionsRetAddr__anon_e27387733d94",
              "Zig.ptrProject v16.ptr (·.elem 4 p1))", "Zig.ptrProject v16.ptr (·.elem 1 p1))")],
            {"make32_spec"}, set()),
        # `free` of a `[:0]u64` gives back `len + 1` bytes instead of `(len + 1) * 8`.
        "wide-free-bytes-are-item-count": ("Interfaces/Wide.lean", "Interfaces/WideSpec.lean",
            [("def mem_Allocator_free__anon_dddca57af15b",
              "let i5 ← Zig.mul false i4 (8 : BitVec 64) (safe := false)", "let i5 ← pure i4")],
            {"release64_spec"}, set()),
        # `reallocAdvanced` of `u16` asks for one byte per item instead of two.
        "wide-realloc-bytes-are-item-count": ("Interfaces/Wide.lean", "Interfaces/WideSpec.lean",
            [("def mem_Allocator_reallocAdvanced__anon_37f73f8446a2",
              "math_mul__anon_44faaf286c79 (2 : BitVec 64) p2", "math_mul__anon_44faaf286c79 (1 : BitVec 64) p2")],
            {"realloc16_spec"}, set()),
        # Growth of the sentinel slice itself (`Interfaces/Grow.lean`) under `GrowSpec`:
        # `mem.absorbSentinel` of a `[:0]u8` returns `len` items instead of `len + 1`, so `realloc`,
        # `remap`, `resize` and `free` hand the allocator one byte less than the grant (what the std
        # of Zig 0.15.2 and 0.14.1 does).
        "grow-absorb-omits-sentinel": ("Interfaces/Grow.lean", "Interfaces/GrowSpec.lean",
            [("def mem_absorbSentinel__anon_2445b0d558b2",
              "    let i7 ← Zig.add false i6 (1 : BitVec 64)\n", "    let i7 ← pure i6\n")],
            {"free8_spec", "realloc8_spec", "move8_grant", "fit8_grant"}, set()),
    },
}
ROOTS = {"callbacks": ROADMAP / "callbacks", "asm-env": ROADMAP / "asm-effects", "sentinel": ROADMAP / "interfaces"}
# The CI check that runs each fixture's mutants (the kill it reports: scripts/mutation_kill_log.py).
CHECKS = {"callbacks": "tests/roadmap/callbacks/check.sh", "asm-env": "tests/roadmap/asm-effects/check.sh",
          "sentinel": "tests/roadmap/interfaces/check.sh"}
sys.path.insert(0, str(ROADMAP.parents[1] / "scripts"))
from mutation_kill_log import killed as log_kill  # noqa: E402


def mutate(source, edits):
    for scope, old, new in edits:
        start = source.index(scope)
        at = source.index(old, start)
        source = source[:at] + new + source[at + len(old):]
    return source


def generate(root, out):
    for name, (module, proofs, edits, _, _) in MUTANTS[root].items():
        source = (ROOTS[root] / module).read_text(encoding="utf-8")
        target = Path(out) / name / module
        target.parent.mkdir(parents=True)
        target.write_text(mutate(source, edits), encoding="utf-8")
        print(f"{name}:{module}:{proofs}")


def theorem_at(lines, number):
    for line in reversed(lines[:number]):
        found = re.match(r"(?:private )?theorem (\S+)", line)
        if found:
            return found.group(1)
    return None


def classify(name, status, log, proofs):
    root = next(r for r, t in MUTANTS.items() if name in t)
    _, _, _, required, allowed = MUTANTS[root][name]
    if status != "1":
        raise SystemExit(f"{name}: Lean exit {status}, want 1 (the proofs must reject the mutant)")
    lines = Path(proofs).read_text(encoding="utf-8").splitlines()
    text = Path(log).read_text(encoding="utf-8", errors="replace")
    stem = Path(proofs).name
    failed = {theorem_at(lines, int(m.group(1)))
              for m in re.finditer(rf"{re.escape(stem)}:(\d+):\d+: error", text)}
    if not failed:
        raise SystemExit(f"{name}: no located proof error:\n{text[-2000:]}")
    if not required <= failed or not failed <= required | allowed:
        raise SystemExit(f"{name}: failing theorems {sorted(map(str, failed))}, want {sorted(required)} "
                         f"(allowed {sorted(allowed)})")
    print(f"{name}: rejected by {sorted(failed)}")
    log_kill("tests/roadmap/callbacks/mutants.py", name, CHECKS[root])


def self_test():
    count = 0
    for root, table in MUTANTS.items():
        for name, (module, proofs, edits, required, allowed) in table.items():
            source = (ROOTS[root] / module).read_text(encoding="utf-8")
            assert mutate(source, edits) != source, name
            text = (ROOTS[root] / proofs).read_text(encoding="utf-8")
            for theorem in required | allowed:
                assert re.search(rf"^theorem {theorem}\b", text, re.M), (name, theorem)
            count += 1
    print(f"E02/A01/M04 mutant self-test: {count}")


def main(argv):
    if argv[1:] == ["--self-test"]:
        self_test()
    elif len(argv) == 4 and argv[1] == "generate":
        generate(argv[2], argv[3])
    elif len(argv) == 6 and argv[1] == "classify":
        classify(*argv[2:])
    else:
        raise SystemExit("usage: mutants.py --self-test | generate ROOT OUT | classify NAME STATUS LOG PROOFS")


if __name__ == "__main__":
    main(sys.argv)
