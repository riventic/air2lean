#!/usr/bin/env python3
"""C10: wrong observations and mutants of Sc.lean's SC oracle and observation check (Q02).

    mutations.py WORK     (check.sh; needs the built imports of Sc.lean)

C10's `seq_cst` semantics is not implemented (docs/research/C10.md): the model's atomics cannot
tell `seq_cst` from release/acquire, which Sc.lean records as `#guard`s (premise ORD-03). So no
mutant of that semantics exists yet. What exists, and what the implementation will be checked
against, is Sc.lean's executable oracle of the sequentially consistent outcomes (`scExplore`) and
its check of the native observations (`main`). This file covers those two:

* `BAD_OBSERVATIONS`: a committed observation file with one line changed must be rejected by the
  unmutated Sc.lean with the named message (an SC-forbidden outcome of an all-`seq_cst` test, an
  outcome outside the model, a missing test).
* `MUTANTS`: one change of Sc.lean each, killed in the way its entry names:
  - `GUARD`: elaboration fails, every error is at a `#guard`, and the ORD-03 guard is among them
    (the oracle no longer forbids the outcomes RC11 forbids);
  - `OBSERVED`: the mutant elaborates and rejects a committed observation as not SC;
  - `(ACCEPTS, NAME)`: the mutant elaborates and accepts the wrong observation NAME, which the
    unmutated check rejects.
A mutant that survives, or fails for another reason, aborts the run. Kills are reported to
AIR2LEAN_MUTATION_KILL_LOG (scripts/mutation_kill_log.py).
"""
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from lean_mutant import ERROR, edit, error_decls, run as run_lean  # noqa: E402
from mutation_kill_log import killed as log_kill  # noqa: E402

SELF = "tests/roadmap/sc-order/mutations.py"
CHECK = "tests/roadmap/sc-order/check.sh"
SC = HERE / "Sc.lean"
OBSERVED = sorted((HERE / "observed").glob("*.txt"))
ORD03_GUARD = '#guard [("sb", "00"), ("2+2w", "11"), ("iriw", "1010")].all'
NOT_SC = "is not sequentially consistent"
GUARD, OBSERVED_KILL, ACCEPTS = "guard", "observed", "accepts"

# name -> (the line that starts with this, what is appended to it ('' drops the line), the
# message of the rejection).
BAD_OBSERVATIONS = {
    "sb-seq-cst-both-zero": ("litmus sb seq_cst ", " 00:1", f"sb seq_cst: outcome 00 (1 rounds) {NOT_SC}"),
    "2+2w-seq-cst-first-writes-last": ("litmus 2+2w seq_cst ", " 11:1", f"2+2w seq_cst: outcome 11 (1 rounds) {NOT_SC}"),
    "iriw-seq-cst-readers-disagree": ("litmus iriw seq_cst ", " 1010:1", f"iriw seq_cst: outcome 1010 (1 rounds) {NOT_SC}"),
    "sb-relaxed-outside-model": ("litmus sb relaxed ", " 22:1", "sb relaxed: outcome 22 (1 rounds) is not a model outcome"),
    "sb-mixed-line-missing": ("litmus sb mixed ", "", "no line for sb mixed"),
}

# `scExplore`'s choice of the next thread: every thread that has an operation left.
STEPS = "progs.zipIdx.filterMap fun (ops, k) => ops.head?.map (·, k)"
REST = "fun (op, k) =>\n    let rest"
# name -> (edits of Sc.lean, kill)
MUTANTS = {
    # The oracle: a load that ignores the store, a store that is lost, threads that never interleave.
    "sc-load-reads-initial": ([("regs.set! reg mem[loc]!", "regs.set! reg 0")], GUARD),
    "sc-store-dropped": ([("scExplore final (mem.set! loc v) regs rest", "scExplore final mem regs rest")], GUARD),
    "sc-threads-never-interleave": ([(f"({STEPS}).flatMap {REST}", f"(({STEPS}).take 1).flatMap {REST}")], OBSERVED_KILL),
    # The observation check: each of its three rejections removed.
    "sc-outcome-check-dropped": ([("else if t.allSc && !sc then", "else if false then")], (ACCEPTS, "sb-seq-cst-both-zero")),
    "model-outcome-check-dropped": ([("if !os.contains o then", "if false then")], (ACCEPTS, "sb-relaxed-outside-model")),
    "missing-test-accepted": ([('| [] => bad := bad ++ [s!"{file}: no line for {key t}"]', "| [] => pure ()")],
                              (ACCEPTS, "sb-mixed-line-missing")),
}


def fail(name, why, out):
    sys.stderr.write(out[-4000:])
    raise SystemExit(f"{name}: {why}")


def bad_observation(name, work):
    """The first committed observation file with the change NAME, written below WORK."""
    prefix, tail, _ = BAD_OBSERVATIONS[name]
    lines = OBSERVED[0].read_text(encoding="utf-8").splitlines()
    hits = [i for i, line in enumerate(lines) if line.startswith(prefix)]
    if len(hits) != 1:
        raise SystemExit(f"{name}: {OBSERVED[0].name} has no single line {prefix!r}")
    lines[hits[0]:hits[0] + 1] = [lines[hits[0]] + tail] if tail else []
    path = work / f"{name}.txt"
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def check(source, files):
    """Run SOURCE's `main` on FILES: (exit code, output, the lines of SOURCE with an elaboration
    error). An error in another file (an import) is no result of SOURCE: the run aborts."""
    rc, out = run_lean(["--run", source, *files])
    stray = error_decls(out, source)[1]
    if stray:
        fail(Path(source).stem, f"errors outside {Path(source).name}: {stray[:3]}", out)
    lines = Path(source).read_text(encoding="utf-8").splitlines()
    return rc, out, [lines[int(m["line"]) - 1] for m in ERROR.finditer(out)]


def main(argv):
    if len(argv) != 2:
        raise SystemExit(__doc__)
    work = Path(argv[1])
    work.mkdir(parents=True, exist_ok=True)
    bad = {name: bad_observation(name, work) for name in BAD_OBSERVATIONS}
    # One run of the unmutated check: every wrong file is rejected, each for its one reason.
    rc, out, errors = check(SC, list(bad.values()))
    wanted = {f"error: {path}: {BAD_OBSERVATIONS[name][2]}" for name, path in bad.items()}
    rejections = [line for line in out.splitlines() if line.startswith("error: ")]
    if rc != 1 or errors or len(rejections) != len(wanted) or any(
            not any(line.startswith(w) for line in rejections) for w in wanted):
        fail("wrong observations", "not rejected one by one with their messages", out)
    print(f"{len(bad)} wrong observations rejected: {', '.join(bad)}")
    for name, (edits, kill) in MUTANTS.items():
        mutant = work / f"{name}.lean"
        mutant.write_text(edit(SC.read_text(encoding="utf-8"), edits, name), encoding="utf-8")
        accepted = kill[1] if isinstance(kill, tuple) and kill[0] == ACCEPTS else None
        rc, out, errors = check(mutant, [bad[accepted]] if accepted else OBSERVED)
        if kill == GUARD:
            if rc == 0 or not errors or any(not e.startswith("#guard") for e in errors) or not any(
                    e.startswith(ORD03_GUARD) for e in errors):
                fail(name, f"SURVIVED or rejected for another reason (errors at {errors})", out)
        elif errors:
            fail(name, "the mutant does not elaborate (an invalid mutant)", out)
        elif kill == OBSERVED_KILL:
            if rc != 1 or NOT_SC not in out:
                fail(name, "SURVIVED: the committed observations are still accepted", out)
        elif accepted:
            if rc != 0:
                fail(name, f"the mutant still rejects {accepted}, so that observation does not detect it", out)
        else:
            raise SystemExit(f"{name}: unknown kill {kill!r}")
        log_kill(SELF, name, CHECK)
        print(f"{name}: killed ({kill if accepted is None else f'accepts {accepted}'})")
    print(f"sc-order: {len(BAD_OBSERVATIONS)} wrong observations rejected, {len(MUTANTS)} mutants killed")


if __name__ == "__main__":
    main(sys.argv)
