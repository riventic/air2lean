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
  - `guard`: elaboration fails, every error is at a `#guard`, and the ORD-03 guard is among them
    (the oracle no longer forbids the outcomes RC11 forbids);
  - `observed`: the mutant elaborates and rejects a committed observation with the message;
  - `accepts NAME`: the mutant elaborates and accepts the wrong observation NAME, which the
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
from lean_mutant import ERROR, edit, run as run_lean  # noqa: E402
from mutation_kill_log import killed as log_kill  # noqa: E402

SELF = "tests/roadmap/sc-order/mutations.py"
CHECK = "tests/roadmap/sc-order/check.sh"
SC = HERE / "Sc.lean"
OBSERVED = sorted((HERE / "observed").glob("*.txt"))
ORD03_GUARD = '#guard [("sb", "00"), ("2+2w", "11"), ("iriw", "1010")].all'
NOT_SC = "is not sequentially consistent"

# name -> (the line that starts with this, what replaces the line's end ('' drops the line), the
# message of the rejection).
BAD_OBSERVATIONS = {
    "sb-seq-cst-both-zero": ("litmus sb seq_cst ", " 00:1", f"sb seq_cst: outcome 00 (1 rounds) {NOT_SC}"),
    "2+2w-seq-cst-first-writes-last": ("litmus 2+2w seq_cst ", " 11:1", f"2+2w seq_cst: outcome 11 (1 rounds) {NOT_SC}"),
    "iriw-seq-cst-readers-disagree": ("litmus iriw seq_cst ", " 1010:1", f"iriw seq_cst: outcome 1010 (1 rounds) {NOT_SC}"),
    "sb-relaxed-outside-model": ("litmus sb relaxed ", " 22:1", "sb relaxed: outcome 22 (1 rounds) is not a model outcome"),
    "sb-mixed-line-missing": ("litmus sb mixed ", "", "no line for sb mixed"),
}

INTERLEAVE = "(progs.zipIdx.filterMap fun (ops, k) => ops.head?.map (·, k)).flatMap fun (op, k) =>\n    let rest"
# name -> (edits of Sc.lean, kill)
MUTANTS = {
    # The oracle: a load that ignores the store, a store that is lost, threads that never interleave.
    "sc-load-reads-initial": ([("regs.set! reg mem[loc]!", "regs.set! reg 0")], "guard"),
    "sc-store-dropped": ([("scExplore final (mem.set! loc v) regs rest", "scExplore final mem regs rest")], "guard"),
    "sc-threads-never-interleave": ([(INTERLEAVE, INTERLEAVE.replace(").flatMap", ").take 1).flatMap").replace("(progs", "((progs", 1))],
                                    "observed"),
    # The observation check: each of its three rejections removed.
    "sc-outcome-check-dropped": ([("else if t.allSc && !sc then", "else if false then")], "accepts sb-seq-cst-both-zero"),
    "model-outcome-check-dropped": ([("if !os.contains o then", "if false then")], "accepts sb-relaxed-outside-model"),
    "missing-test-accepted": ([('| [] => bad := bad ++ [s!"{file}: no line for {key t}"]', "| [] => pure ()")],
                              "accepts sb-mixed-line-missing"),
}


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
    """Run SOURCE's `main` on FILES: (exit code, output, the elaboration errors' line numbers)."""
    rc, out = run_lean(["--run", source, *files])
    return rc, out, [int(m["line"]) for m in ERROR.finditer(out)]


def fail(name, why, out):
    sys.stderr.write(out[-4000:])
    raise SystemExit(f"{name}: {why}")


def main(argv):
    if len(argv) != 2:
        raise SystemExit(__doc__)
    work = Path(argv[1])
    work.mkdir(parents=True, exist_ok=True)
    bad = {name: bad_observation(name, work) for name in BAD_OBSERVATIONS}
    for name, path in bad.items():
        rc, out, errors = check(SC, [path])
        if rc != 1 or errors or f"error: {path}: {BAD_OBSERVATIONS[name][2]}" not in out:
            fail(name, "the wrong observation was not rejected with its message", out)
        print(f"{name}: wrong observation rejected")
    for name, (edits, kill) in MUTANTS.items():
        mutant = work / f"{name}.lean"
        text = edit(SC.read_text(encoding="utf-8"), edits, name)
        mutant.write_text(text, encoding="utf-8")
        how, _, wrong = kill.partition(" ")
        rc, out, errors = check(mutant, [bad[wrong]] if wrong else OBSERVED)
        lines = text.splitlines()
        if how == "guard":
            guards = [lines[n - 1] for n in errors]
            if rc == 0 or not guards or any(not g.startswith("#guard") for g in guards) or not any(
                    g.startswith(ORD03_GUARD) for g in guards):
                fail(name, f"SURVIVED or rejected for another reason (errors at {guards})", out)
        elif errors:
            fail(name, "the mutant does not elaborate (an invalid mutant)", out)
        elif how == "observed":
            if rc != 1 or NOT_SC not in out:
                fail(name, "SURVIVED: the committed observations are still accepted", out)
        elif rc != 0:
            fail(name, f"the mutant still rejects {wrong}, so that observation does not detect it", out)
        log_kill(SELF, name, CHECK)
        print(f"{name}: killed ({kill})")
    print(f"sc-order: {len(BAD_OBSERVATIONS)} wrong observations rejected, {len(MUTANTS)} mutants killed")


if __name__ == "__main__":
    main(sys.argv)
