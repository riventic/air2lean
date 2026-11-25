#!/usr/bin/env python3
"""E03 mutants of the environment-boundary fixture.

`run WORK` takes the directory `check.sh` built the clean `EnvStd<NN>/Gen.olean` files and
`EnvStdIo.olean` in (LEAN_PATH must reach the Lake libraries) and builds each mutant below
`WORK/mutants/NAME`:

- `client` mutants change the scripted `Ops` instance of `WriteAll.lean`, the non-vacuous witness of
  the contract: the instance no longer satisfies the ENV-01 contract (a handle that stays open after
  `close`, a write that makes no progress or reports more than it was given, a monotonic clock that
  runs backwards, an error outside the allowed list). `WriteAll.lean` must then fail in the
  declarations that state the violated field, not elsewhere.
- `std` mutants change the retained translation of real std I/O (`expected/EnvStd15.lean`,
  `expected/EnvStd17.lean`): the proofs about that generated code (`StdIo.lean`,
  `ReadClose/EnvStd17.lean`) must fail in the theorems that walk the changed function.

A mutant that fails to build, or fails outside the named declarations, aborts the run; a survivor is
a finding. Only a rejected mutant reports its kill (`kill`). `--self-test` checks every anchor.
"""
from pathlib import Path
import shutil
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / "scripts"))
from lean_mutant import build_gen, edit, reject, run as run_lean  # noqa: E402
from mutation_kill_log import killed as log_kill  # noqa: E402

CLIENT = HERE / "WriteAll.lean"
GEN = {ns: HERE / f"expected/{ns}.lean" for ns in ("EnvStd15", "EnvStd16", "EnvStd17")}
# The proofs about each mutated translation (EnvStd16's proofs are EnvStd17's renamed).
PROOFS = {"EnvStd15": HERE / "StdIo.lean", "EnvStd17": HERE / "ReadClose/EnvStd17.lean"}

# client: name -> (edits of WriteAll.lean, declarations that must fail). Each `old` occurs once.
CLIENT_MUTANTS = {
    # `close` leaves the handle open.
    "close-keeps-handle-open": ([
        ("close s h := { s.tick with opened := fun h' => if h' = h then false else s.opened h' }",
         "close s h := s.tick"),
    ], ["scripted_contract"]),
    # A write may report zero bytes: the loop would not terminate.
    "write-reports-zero-progress": ([
        ("| .ok n :: rest => (.ok (max 1 (min n buf.length)), { s.tick with script := rest })",
         "| .ok n :: rest => (.ok (min n buf.length), { s.tick with script := rest })"),
    ], ["scripted_contract"]),
    # A write may report more bytes than it was given.
    "write-reports-more-than-given": ([
        ("| .ok n :: rest => (.ok (max 1 (min n buf.length)), { s.tick with script := rest })",
         "| .ok n :: rest => (.ok (max 1 n), { s.tick with script := rest })"),
    ], ["scripted_contract"]),
    # The monotonic clock moves backwards.
    "monotonic-clock-runs-backwards": ([
        ("{ s with mono := s.mono + 1, wall := s.wall - 1 }", "{ s with mono := s.mono - 1, wall := s.wall - 1 }"),
    ], ["scripted_contract"]),
    # A scripted error that the contract's allowed list does not contain.
    "error-outside-allowed-list": ([
        ("[.wouldBlock, .brokenPipe, .noSpaceLeft, .accessDenied, .inputOutput, .connectionReset]",
         "[.wouldBlock, .brokenPipe, .noSpaceLeft, .accessDenied, .inputOutput]"),
    ], ["mem_allErrors"]),
}

# std: name -> (translation, edits, theorems of StdIo.lean that must fail). Each `old` occurs once.
STD_MUTANTS = {
    # `writeAll` advances by one byte instead of the bytes the write reported.
    "write-all-advances-one-byte": ("EnvStd15", [
        ("let i38 ← Zig.add false i13 v34", "let i38 ← Zig.add false i13 (1 : BitVec 64)"),
    ], []),
    # `writeAllClose` returns without closing the handle after a complete write.
    "write-all-close-skipped": ("EnvStd15", [
        ("let _i8 ← Zig.callM (fs_File_close p0)", "let _i8 ← pure ()"),
    ], []),
    # `writeAll` turns a write error into success.
    "write-all-error-swallowed": ("EnvStd15", [
        ("let i36 ← pure ((.error i35) : Except Zig.ErrName (Unit))",
         "let i36 ← pure ((.ok ()) : Except Zig.ErrName (Unit))"),
    ], []),
    # `readClose` returns without closing the handle.
    "read-close-skipped": ("EnvStd17", [
        ("let _i3 ← Zig.callM (Io_Threaded_closeFd p0)", "let _i3 ← pure ()"),
    ], []),
    # `posix.read` reports EAGAIN as another error.
    "read-wouldblock-renamed": ("EnvStd17", [
        ("pure (.ret (.error \"WouldBlock\" : Except Zig.ErrName (BitVec 64)))",
         "pure (.ret (.error \"Unexpected\" : Except Zig.ErrName (BitVec 64)))"),
    ], []),
}


def run_client(name, work):
    edits, broken = CLIENT_MUTANTS[name]
    target = Path(work) / "mutants" / name / CLIENT.name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(edit(CLIENT.read_text(encoding="utf-8"), edits, name), encoding="utf-8")
    rc, out = run_lean([target], work)
    reject(name, rc, out, target, broken)


def run_std(name, work):
    namespace, edits, broken = STD_MUTANTS[name]
    target = Path(work) / "mutants" / name
    # Lean resolves a module by the first search-path entry that holds its root directory, so the
    # copy holds the other translations' oleans too.
    for other in GEN:
        shutil.copytree(Path(work) / other, target / other)
    build_gen(name, target, f"{namespace}/Gen.lean",
              edit(GEN[namespace].read_text(encoding="utf-8"), edits, name), work)
    proofs = PROOFS[namespace]
    rc, out = run_lean(["-R", HERE, proofs], target, work)
    reject(name, rc, out, proofs, broken)


def run(work):
    for name in CLIENT_MUTANTS:
        run_client(name, work)
    for name in STD_MUTANTS:
        run_std(name, work)
    log_kill("tests/roadmap/env-boundaries/mutations.py", [*CLIENT_MUTANTS, *STD_MUTANTS],
             "tests/roadmap/env-boundaries/check.sh")


def main(argv):
    if argv[1:] == ["--self-test"]:
        source = CLIENT.read_text(encoding="utf-8")
        for name, (edits, _) in CLIENT_MUTANTS.items():
            assert edit(source, edits, name) != source, name
        for name, (namespace, edits, _) in STD_MUTANTS.items():
            text = GEN[namespace].read_text(encoding="utf-8")
            assert edit(text, edits, name) != text, name
        print(f"env-boundaries mutant self-test: {len(CLIENT_MUTANTS) + len(STD_MUTANTS)}")
    elif len(argv) == 3 and argv[1] == "run":
        run(argv[2])
    else:
        raise SystemExit("usage: mutations.py --self-test | run WORK")


if __name__ == "__main__":
    main(sys.argv)
