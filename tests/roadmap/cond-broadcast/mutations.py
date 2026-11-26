#!/usr/bin/env python3
"""C14 mutants of the broadcast client (`threadsync.handoffAll`, `Proofs/Threadsync/Gen.lean`).

`run` builds, per mutant, a check tree (scripts/check-tree.py) with one mutated copy of the
committed translation in place of `Proofs/Threadsync/Gen.lean`, and builds the client's proofs
there with Lake (so the precompiled `fsym` engine runs as in the real build). The mutant must be
valid Lean on which the contract proofs of the sync objects still build (`IMPORTS`: the mutant
changes only the client), and `Proofs.Threadsync.Handoff` must fail: Lake's failed targets are
that module alone, every error lies in its source, and each theorem the mutant must break
contains one. A mutant that still builds, or fails elsewhere, aborts the run: a survivor is a
finding. Only a rejected mutant reports its kill. `--self-test` checks every anchor.

The client has one waiter (the main thread), so `broadcast-is-signal` is a program that is still
correct: its kill is that the client's proof has no rule for a `signal` there (it is proved from
`CondImpl.broadcast_wp` alone), not a wrong result. `broadcast-dropped` is a wrong program (a
lost wake-up: the main thread can wait for good), which the proof and the kernel-computed run
`handoffAll_completes` both reject.
"""
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from lean_mutant import edit, error_decls  # noqa: E402
from mutation_kill_log import killed as log_kill  # noqa: E402

GEN = "Proofs/Threadsync/Gen.lean"
CLIENT = "Proofs.Threadsync.Handoff"
CLIENT_SOURCE = ROOT / "Proofs/Threadsync/Handoff.lean"
# The contract proofs of this program's sync objects: they must build on every mutant.
IMPORTS = ["Proofs.Threadsync.Cond", "Proofs.Threadsync.Event"]
# The one call of the broadcast in the translation (only `producerAll` calls it); the numbers of
# the temporaries are the translator's, so the line is found by its shape.
BROADCAST = re.compile(r"^ *let _i\d+ ← Zig\.callC \(Thread_Condition_broadcast i\d+\)\n", re.M)

# name -> (what replaces the broadcast's line, theorems of the client that must fail).
MUTANTS = {
    # `producerAll` signals instead of broadcasting.
    "broadcast-is-signal": (
        lambda line: line.replace("Thread_Condition_broadcast", "Thread_Condition_signal"),
        ["producerAll_spec"]),
    # `producerAll` wakes no waiter: the proof fails, and so does the kernel-computed run of
    # `handoffAll_completes` (under its schedule the main thread sleeps and is never woken).
    "broadcast-dropped": (lambda line: "", ["producerAll_spec", "handoffAll_completes"]),
}
# Lake prints a Lean error as `error: FILE:LINE:COL: message`; lean_mutant reads `FILE:LINE:COL: error`.
LAKE_ERROR = re.compile(r"^error: (\S+?):(\d+):(\d+): ", re.M)


def lake(tree, targets):
    done = subprocess.run(["lake", "build", *targets], cwd=tree, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, check=False)
    return done.returncode, done.stdout


def mutants():
    """(name, mutated translation, theorems that must fail) of every mutant."""
    source = (ROOT / GEN).read_text(encoding="utf-8")
    lines = BROADCAST.findall(source)
    if len(lines) != 1:
        raise SystemExit(f"{GEN}: {len(lines)} calls of Thread_Condition_broadcast, expected one")
    for name, (change, broken) in MUTANTS.items():
        yield name, edit(source, [(lines[0], change(lines[0]))], name), broken


def run(work):
    work = Path(work)
    for name, text, broken in mutants():
        mutated = work / f"{name}.Gen.lean"
        mutated.write_text(text, encoding="utf-8")
        tree = ROOT / ".lake/check-tree" / f"cond-broadcast-{name}"
        subprocess.run([sys.executable, "-B", str(ROOT / "scripts/check-tree.py"), "create", str(tree),
                        "--replace", f"{GEN}={mutated}"], cwd=ROOT, check=True)
        # One build: a contract proof that fails is among Lake's failed targets (an invalid mutant).
        rc, out = lake(tree, [*IMPORTS, CLIENT])
        failed = re.search(r"^Some required targets logged failures:\n((?:- .*\n?)*)", out, re.M)
        failed = {line[2:].strip() for line in failed.group(1).splitlines()} if failed else set()
        decls, stray = error_decls(LAKE_ERROR.sub(r"\1:\2:\3: error: ", out), CLIENT_SOURCE)
        problems = []
        if rc == 0:
            problems.append("the client's proofs still build")
        elif failed != {CLIENT}:
            problems.append(f"failed targets {sorted(failed)}, not {CLIENT} alone")
        if stray:
            problems.append(f"errors outside {CLIENT_SOURCE.name}: {stray[:3]}")
        if sorted(decls) != sorted(broken):
            problems.append(f"errors in {sorted(decls)}, expected in {sorted(broken)}")
        if problems:
            sys.stderr.write(out[-4000:])
            raise SystemExit(f"{name}: SURVIVED or rejected for another reason: " + "; ".join(problems))
        print(f"{name}: rejected, errors in {sorted(decls)}")
        log_kill("tests/roadmap/cond-broadcast/mutations.py", name, "tests/roadmap/cond-broadcast/check.sh")


def main(argv):
    if argv[1:] == ["--self-test"]:
        source = (ROOT / GEN).read_text(encoding="utf-8")
        for name, text, _ in mutants():
            assert text != source, name
        print(f"cond-broadcast mutant self-test: {len(MUTANTS)}")
    elif len(argv) == 3 and argv[1] == "run":
        run(argv[2])
    else:
        raise SystemExit("usage: mutations.py --self-test | run WORK")


if __name__ == "__main__":
    main(sys.argv)
