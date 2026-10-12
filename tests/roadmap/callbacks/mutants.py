#!/usr/bin/env python3
"""Semantic mutants of the retained E02 translations (`Callbacks/Gen.lean`, `Callbacks/Async.lean`)
and of A01's `asm-effects/AsmEnv/Gen.lean`.

`generate ROOT OUT` writes, per mutant of the fixture ROOT (`callbacks` or `asm-env`), a mutated
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
}
ROOTS = {"callbacks": ROADMAP / "callbacks", "asm-env": ROADMAP / "asm-effects"}


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
    entry = next(t[name] for t in MUTANTS.values() if name in t)
    _, _, _, required, allowed = entry
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
    print(f"E02/A01 mutant self-test: {count}")


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
