#!/usr/bin/env python3
"""T03 byte-order mutants of the retained 0.17.1 s390x translation (`BigEndian/V0_17_1/S390x/Gen.lean`).

`generate OUT` copies the Lake library BigEndian to `OUT/<name>/BigEndian` with one mutation
applied and prints `<name>`. Each mutant is well-typed Lean that changes only the byte order of a
layout: a bit-pointer access with the little-endian order, or the big-endian instances not opened
(every memory encoding little-endian under the s390x profile). check.sh builds each copy with
`scripts/fixtures.py mutant NAME --src OUT/NAME --fails BigEndian.Proofs`: the translation builds
and the byte-order theorems of BigEndian.Proofs (`fieldFromBytes_orders_0_17`,
`setFieldBytes_orders_0_17`, `externToBytes_orders_0_17`) fail on it. Only then it reports the kill
(`kill NAME`). `--self-test` checks every anchor.
"""
from pathlib import Path
import shutil
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / "scripts"))
from mutation_kill_log import killed as log_kill  # noqa: E402
LIBRARY = "BigEndian"
GEN = "BigEndian/V0_17_1/S390x/Gen.lean"

# name -> (old, new): each `old` occurs exactly once in the retained translation.
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
        target = Path(out) / name
        shutil.copytree(HERE / LIBRARY, target / LIBRARY)
        (target / GEN).write_text(mutate(source, name), encoding="utf-8")
        print(name)


def kill(name):
    if name not in MUTANTS:
        raise SystemExit(f"unknown mutant {name}")
    log_kill("tests/roadmap/big-endian/mutations.py", name, "tests/roadmap/big-endian/check.sh")


def main(argv):
    if argv[1:] == ["--self-test"]:
        source = (HERE / GEN).read_text(encoding="utf-8")
        for name in MUTANTS:
            assert mutate(source, name) != source, name
        print(f"big-endian mutant self-test: {len(MUTANTS)}")
    elif len(argv) == 3 and argv[1] == "generate":
        generate(argv[2])
    elif len(argv) == 3 and argv[1] == "kill":
        kill(argv[2])
    else:
        raise SystemExit("usage: mutations.py --self-test | generate OUT | kill NAME")


if __name__ == "__main__":
    main(sys.argv)
