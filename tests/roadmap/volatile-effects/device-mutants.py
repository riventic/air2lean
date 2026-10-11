#!/usr/bin/env python3
"""L13 device-effect mutants of the generated UART driver and `rdtsc` client.

`generate OUT` writes one mutated copy of the committed `<Module>/Gen.lean` per mutant under
`OUT/<name>/<Module>/Gen.lean` and prints `name:Module` per mutant. Each mutant is still
well-typed Lean: it changes only the device semantics (a merged, reordered, dropped or ordinary
read, or a repeatable asm value). `classify NAME STATUS LOG PROOFS` requires that Lean rejected
the unchanged `<Module>/Proofs.lean` against that mutant, with every error inside the theorems
the mutant targets (`MUTANTS[name]`), at least one in each. `--self-test` checks the edits
against the committed `Gen.lean` files.
"""
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
VLOAD = "Zig.vload air2lean_device 32 4"
VASM = 'Zig.vasm air2lean_device "rdtsc\\n\\tshlq $32, %%rdx\\n\\torq %%rdx, %%rax" [] 64'

# name -> (module, edits [(old, new)], theorems that must fail, theorems that may also fail)
MUTANTS = {
    # Two volatile reads merged into one: the second read reuses the first value.
    "merge_reads": ("DeviceEffects", [(f"let i4 ← {VLOAD} i3", "let i4 ← pure i2")],
                    {"statusTwice_trace"}, {"statusTwice_not_merged"}),
    # The status read moved before the data write.
    "reorder_write_read": ("DeviceEffects", [(f"    Zig.vstore air2lean_device 32 4 i2 i3\n    let i5 ← pure p0\n"
                             f"    let i6 ← {VLOAD} i5\n",
                             f"    let i5 ← pure p0\n    let i6 ← {VLOAD} i5\n"
                             "    Zig.vstore air2lean_device 32 4 i2 i3\n")],
                           {"sendThenStatus_trace"}, set()),
    # An unused volatile read removed as dead code.
    "drop_unused_read": ("DeviceEffects", [(f"let _i2 ← {VLOAD} i1", "let _i2 ← pure (0 : BitVec 32)")],
                         {"clearStatus_trace"}, set()),
    # The status poll as an ordinary repeatable memory load.
    "ordinary_load": ("DeviceEffects", [(f"let i6 ← {VLOAD} i5\n    let i7", "let i6 ← Zig.load (BitVec 32) 4 i5\n    let i7")],
                      # The poll steps fail first; `putc_trace` builds on them.
                      {"loop_busy", "loop_ready"}, {"poll_run", "putc_trace"}),
    # The two `rdtsc` merged into one value.
    "merge_asm": ("DeviceAsm", [(f"let i1 ← {VASM}", "let i1 ← pure i0")],
                  {"elapsed_trace"}, {"elapsed_not_merged"}),
    # The M21 translation: `rdtsc` as one repeatable opaque value, no event.
    "repeatable_asm": ("DeviceAsm", [("def elapsed  :", "opaque tscValue : BitVec 64\n\ndef elapsed  :"),
                                     (f"let i0 ← {VASM}", "let i0 ← pure tscValue"),
                                     (f"let i1 ← {VASM}", "let i1 ← pure tscValue")],
                       {"elapsed_trace"}, {"elapsed_not_merged"}),
}


def mutate(source, edits):
    for old, new in edits:
        if source.count(old) != 1:
            raise SystemExit(f"mutation anchor not found exactly once: {old!r}")
        source = source.replace(old, new)
    return source


def generate(out):
    for name, (module, edits, _, _) in MUTANTS.items():
        source = (HERE / module / "Gen.lean").read_text(encoding="utf-8")
        target = Path(out) / name / module / "Gen.lean"
        target.parent.mkdir(parents=True)
        target.write_text(mutate(source, edits), encoding="utf-8")
        print(f"{name}:{module}")


def theorem_at(lines, number):
    for line in reversed(lines[:number]):
        found = re.match(r"(?:private )?theorem (\S+)", line)
        if found:
            return found.group(1)
    return None


def classify(name, status, log, proofs):
    _, _, required, allowed = MUTANTS[name]
    if status != "1":
        raise SystemExit(f"{name}: Lean exit {status}, want 1 (the proofs must reject the mutant)")
    lines = Path(proofs).read_text(encoding="utf-8").splitlines()
    text = Path(log).read_text(encoding="utf-8", errors="replace")
    failed = set()
    for match in re.finditer(r"Proofs\.lean:(\d+):\d+: error", text):
        failed.add(theorem_at(lines, int(match.group(1))))
    if not failed:
        raise SystemExit(f"{name}: no located proof error:\n{text[-2000:]}")
    if not required <= failed or not failed <= required | allowed:
        raise SystemExit(f"{name}: failing theorems {sorted(map(str, failed))}, want {sorted(required)} "
                         f"(allowed {sorted(allowed)})")
    print(f"{name}: rejected by {sorted(failed)}")


def self_test():
    for name, (module, edits, required, allowed) in MUTANTS.items():
        source = (HERE / module / "Gen.lean").read_text(encoding="utf-8")
        proofs = (HERE / module / "Proofs.lean").read_text(encoding="utf-8")
        assert mutate(source, edits) != source, name
        for theorem in required | allowed:
            assert re.search(rf"^theorem {theorem}\b", proofs, re.M), (name, theorem)
    print(f"device mutant self-test: {len(MUTANTS)}")


def main(argv):
    if argv[1:] == ["--self-test"]:
        self_test()
    elif len(argv) == 3 and argv[1] == "generate":
        generate(argv[2])
    elif len(argv) == 6 and argv[1] == "classify":
        classify(*argv[2:])
    else:
        raise SystemExit("usage: device-mutants.py --self-test | generate OUT | "
                         "classify NAME STATUS LOG PROOFS")


if __name__ == "__main__":
    main(sys.argv)
