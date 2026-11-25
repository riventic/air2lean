#!/usr/bin/env python3
"""C08 mutants of the retained futures translation (`Futures/Gen.lean`).

`run WORK` takes the directory `check.sh` built the clean `Futures/Gen.olean` in (LEAN_PATH must
reach the Lake libraries), builds one mutated Gen.lean per mutant below it and runs the fixture's
own checks against it: a `runtime` mutant is run by `Futures/Runtime.lean` (every schedule of each
program) and killed only by the `require` failure named in the table, a `proof` mutant by the
elaboration of `Futures/Proofs.lean`, killed only by errors in the named theorems. A mutant that
fails to build, or fails for another reason, aborts the run; a survivor is a finding. Only a
rejected mutant reports its kill (`kill`). `--self-test` checks every anchor.
"""
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / "scripts"))
from lean_mutant import edit, reject, run as run_lean  # noqa: E402
from mutation_kill_log import killed as log_kill  # noqa: E402

GEN = "Futures/Gen.lean"
RUNTIME = HERE / "Futures/Runtime.lean"
PROOFS = HERE / "Futures/Proofs.lean"
AWAIT_VALUE_END = ("let i6 ← Zig.awaitC (α := BitVec 32) p0 i2\n    pure (.ret i6)) : Zig.CM Tgt awaitValueLocals "
                   "awaitValueExit).run' { (default : awaitValueLocals) with f := s2 }\n  Zig.free s2\n")

# name -> (edits, ("runtime", message of the failing `require`) | ("proof", theorems that must fail)).
# Each `old` occurs exactly once in the retained translation.
MUTANTS = {
    # The task computes another function: the awaited value is not the task's result.
    "task-result-wrong": ([
        ("let i1 ← pure (Zig.mulWrap p0 p0)", "let i1 ← pure (Zig.addWrap p0 p0)"),
    ], ("runtime", "await did not return the task result for 1")),
    # The second `await` of a consumed future forgets the stored result.
    "second-await-result-dropped": ([
        ("let i8 ← pure (Zig.addWrap i6 i7)", "let i8 ← pure i6"),
    ], ("runtime", "a second await did not return the stored result for 1")),
    # The task stores another value through its captured pointer.
    "task-write-through-capture-lost": ([
        ("Zig.store (α := BitVec 32) 4 p0 p1\n", "Zig.store (α := BitVec 32) 4 p0 (0 : BitVec 32)\n"),
    ], ("runtime", "the task's write through its captured pointer was lost for 1")),
    # The task's `error.Zero` is turned into a success.
    "task-error-not-propagated": ([
        ("pure (.ret (.error \"Zero\" : Except Zig.ErrName (BitVec 32)))",
         "pure (.ret (.ok (0 : BitVec 32) : Except Zig.ErrName (BitVec 32)))"),
    ], ("runtime", "error not propagated")),
    # `cancel` only awaits: the request is never recorded, so no schedule delivers `Canceled`.
    "cancel-is-await": ([
        ("Zig.cancelC (α := Except Zig.ErrName (BitVec 32)) p0 i2)",
         "Zig.awaitC (α := Except Zig.ErrName (BitVec 32)) p0 i2)"),
    ], ("runtime", "no schedule observed Canceled for 0")),
    # The task never reaches its cancelation point.
    "cancel-point-skipped": ([
        ("let i2 ← Zig.checkCancelC p0\n", "let i2 ← pure (Except.ok () : Except Zig.ErrName Unit)\n"),
    ], ("runtime", "no schedule observed Canceled for 0")),
    # The future's storage in the awaiting frame is never released.
    "future-storage-leaked": ([
        (AWAIT_VALUE_END, AWAIT_VALUE_END.removesuffix("  Zig.free s2\n")),
    ], ("proof", ["awaitValue_wp", "awaitValue_result"])),
}


def build(name, work):
    edits, _ = MUTANTS[name]
    target = Path(work) / "mutants" / name
    (target / GEN).parent.mkdir(parents=True, exist_ok=True)
    (target / GEN).write_text(edit((HERE / GEN).read_text(encoding="utf-8"), edits, name), encoding="utf-8")
    rc, out = run_lean(["-R", target, "-o", (target / GEN).with_suffix(".olean"), target / GEN], target, work)
    if rc != 0:
        sys.stderr.write(out[-4000:])
        raise SystemExit(f"{name}: the mutated translation does not build (an invalid mutant)")
    return target


def run(work):
    for name, (_, how) in MUTANTS.items():
        target = build(name, work)
        if how[0] == "runtime":
            rc, out = run_lean(["-R", HERE, "--run", RUNTIME], target, work)
            if rc == 0 or f"uncaught exception: {how[1]}" not in out:
                sys.stderr.write(out[-3000:])
                raise SystemExit(f"{name}: SURVIVED or failed for another reason (expected {how[1]!r}, exit {rc})")
            print(f"{name}: rejected by the runtime schedules: {how[1]}")
        else:
            rc, out = run_lean(["-R", HERE, PROOFS], target, work)
            reject(name, rc, out, PROOFS, how[1])
        log_kill("tests/roadmap/futures/mutations.py", name, "tests/roadmap/futures/check.sh")


def main(argv):
    if argv[1:] == ["--self-test"]:
        source = (HERE / GEN).read_text(encoding="utf-8")
        for name, (edits, _) in MUTANTS.items():
            assert edit(source, edits, name) != source, name
        print(f"futures mutant self-test: {len(MUTANTS)}")
    elif len(argv) == 3 and argv[1] == "run":
        run(argv[2])
    else:
        raise SystemExit("usage: mutations.py --self-test | run WORK")


if __name__ == "__main__":
    main(sys.argv)
