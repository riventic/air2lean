#!/usr/bin/env python3
"""T03 byte-order mutants of the retained s390x translation (`BigEndian/S390x/Gen.lean`).

`generate OUT` writes one mutated copy per mutant under `OUT/<name>/BigEndian/S390x/Gen.lean` and
prints its name. Each mutant is well-typed Lean that changes only the byte order of a layout: a
bit-pointer access with the little-endian order, or the big-endian instances not opened (every
memory encoding little-endian under the s390x profile). check.sh compiles it and runs
`Diff.lean s390x` against it; `classify NAME STATUS MODEL OBSERVED` requires that the run
succeeded with as many lines as the committed s390x observation and that at least one line
differs from it: a mutant is killed only by a wrong observable value, never by a crash or a
truncated run. `--self-test` checks every anchor.
"""
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / "scripts"))
from mutation_kill_log import killed as log_kill  # noqa: E402
GEN = "BigEndian/S390x/Gen.lean"

# name -> (old, new): each `old` occurs exactly once in the retained s390x translation.
MUTANTS = {
    "bitptr-load-little-order": ("Zig.loadBitsOf .big (BitVec 12) 4 4 4 i16",
                                 "Zig.loadBitsOf .little (BitVec 12) 4 4 4 i16"),
    "bitptr-store-little-order": ("Zig.storeBitsOf .big (α := BitVec 12) 4 4 4 i5 p1",
                                  "Zig.storeBitsOf .little (α := BitVec 12) 4 4 4 i5 p1"),
    "big-endian-instances-dropped": ("\nopen scoped Zig.BigEndian\n", "\n"),
}


def mutate(source, name):
    old, new = MUTANTS[name]
    if source.count(old) != 1:
        raise SystemExit(f"{name}: mutation anchor not found exactly once: {old!r}")
    return source.replace(old, new)


def generate(out):
    source = (HERE / GEN).read_text(encoding="utf-8")
    for name in MUTANTS:
        target = Path(out) / name / GEN
        target.parent.mkdir(parents=True)
        target.write_text(mutate(source, name), encoding="utf-8")
        print(name)


def classify(name, status, model, observed):
    if name not in MUTANTS:
        raise SystemExit(f"unknown mutant {name}")
    if status != "0":
        raise SystemExit(f"{name}: Diff.lean exit {status}: a failed run is not a kill")
    got = Path(model).read_text(encoding="utf-8").splitlines()
    want = Path(observed).read_text(encoding="utf-8").splitlines()
    if not got or len(got) != len(want):
        raise SystemExit(f"{name}: {len(got)} model lines, {len(want)} observed: a truncated run is not a kill")
    differ = sum(a != b for a, b in zip(got, want))
    if not differ:
        raise SystemExit(f"{name}: mutant survived: the model still matches every s390x observation")
    print(f"{name}: killed ({differ} of {len(want)} s390x observations differ)")
    log_kill("tests/roadmap/big-endian/mutations.py", name, "tests/roadmap/big-endian/check.sh")


def main(argv):
    if argv[1:] == ["--self-test"]:
        source = (HERE / GEN).read_text(encoding="utf-8")
        for name in MUTANTS:
            assert mutate(source, name) != source, name
        print(f"big-endian mutant self-test: {len(MUTANTS)}")
    elif len(argv) == 3 and argv[1] == "generate":
        generate(argv[2])
    elif len(argv) == 6 and argv[1] == "classify":
        classify(*argv[2:])
    else:
        raise SystemExit("usage: mutations.py --self-test | generate OUT | classify NAME STATUS MODEL OBSERVED")


if __name__ == "__main__":
    main(sys.argv)
