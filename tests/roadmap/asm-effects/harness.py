#!/usr/bin/env python3
"""A01: run the generated effect-contract asm wrappers and cross-check their definitions.

AsmEffects/Gen.lean is the translator's checked output for air/0.16.0. Every inline-asm
statement in it is a defined function over the x86_64 instruction model (`def
airIsaFx_<hash>`/`airIsa_<hash>`, A02, premise ASM-07), so the generated text runs as it is; only
the profile header, the `import` and the namespace lines change. Each definition is bound to the
AIR `assembly` instruction with the same translator hash and compared, on sampled operands, with
A03's test-only interpretation of that instruction's template text (the old values of read-write
outputs are trailing arguments). Runner.lean then runs the wrappers on model memory and checks
each written location, every other byte of the block (the frame), the alias case and the local
operands. Mutants alter the generated text in memory; each must elaborate and fail with a named
wrapper mismatch.
"""
from __future__ import annotations

import argparse
import importlib.util
from pathlib import Path
import re
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from mutation_kill_log import killed as log_kill  # noqa: E402
GEN = HERE / "AsmEffects/Gen.lean"
AIR = HERE / "air/0.16.0"
A03 = ROOT / "tests/roadmap/asm-wrappers"
FUNCTIONS = ("incm", "setm", "swapm", "addr", "incLocal", "barrier")


def load_a03():
    spec = importlib.util.spec_from_file_location("asm_wrappers_harness", A03 / "harness.py")
    module = importlib.util.module_from_spec(spec)
    sys.dont_write_bytecode = True
    spec.loader.exec_module(module)
    return module


a03 = load_a03()


def asm_ops(air_dir: Path = AIR) -> dict[str, dict]:
    return a03.asm_ops(air_dir)


def rebind(gen: str, ops: dict[str, dict]) -> str:
    return a03.rebind(gen, ops, "AsmEffects")


def program(gen: str, ops: dict[str, dict]) -> str:
    by_function = {op["function"] for op in ops.values()}
    if sorted(by_function) != sorted(FUNCTIONS):
        raise ValueError("expected one asm statement in each of " + ", ".join(FUNCTIONS))
    return "\n".join(["import ZigLean", (A03 / "Interp.lean").read_text(), rebind(gen, ops),
                      a03.cross(gen, ops), (HERE / "Runner.lean").read_text()])


def alter(gen: str, fn: str, before: str, after: str) -> str:
    start = gen.index(f"\ndef {fn} ") + 1
    end = gen.find("\nstructure ", start)
    end = end if end >= 0 else gen.index("\nend AsmEffects", start)
    body = gen[start:end]
    if body.count(before) != 1:
        raise ValueError(f"generated shape changed: {fn}: {before!r}")
    return gen[:start] + body.replace(before, after) + gen[end:]


def mutants(gen: str) -> dict[str, tuple[str, str]]:
    """Mutant name -> (generated text, check that must fail)."""
    def call(fn: str) -> re.Match:
        start = gen.index(f"\ndef {fn} ")
        match = re.compile(r"let (a\d+) := (airIsaFx_\d+)((?: \w+)*)\n").search(gen, start)
        if match is None:
            raise ValueError(f"generated shape changed: {fn} asm call")
        return match

    inc, swap, loc = call("incm"), call("swapm"), call("incLocal")
    t, s = inc.group(1), swap.group(1)
    a, b = swap.group(3).split()
    guard = "    Zig.Asm.guard [(p0, 4), (p1, 4)]\n"
    return {
        "store_wrong_location": (alter(gen, "incm", f"4 p0 {t}\n", f"4 (p0.add 4) {t}\n"), "incm"),
        "rw_read_dropped": (alter(gen, "incm", inc.group(0), inc.group(0).replace(
            inc.group(3), " (0#32)")), "incm"),
        "swap_targets": (alter(alter(gen, "swapm", f"4 p0 {s}.1", f"4 p0 {s}.2"), "swapm",
                               f"4 p1 {s}.2", f"4 p1 {s}.1"), "swapm"),
        "rw_order": (alter(gen, "swapm", f" {a} {b}\n", f" {b} {a}\n"), "swapm"),
        "guard_dropped": (alter(gen, "swapm", guard, ""), "swapm-alias"),
        "local_store_dropped": (alter(gen, "incLocal",
                                      f"    modify (fun s => {{ s with local1 := {loc.group(1)} }})\n", ""),
                                "incLocal"),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--work", type=Path, help="keep generated programs and logs in this fresh directory")
    parser.add_argument("--control-only", action="store_true", help="skip the mutants")
    args = parser.parse_args()
    gen, ops = GEN.read_text(), asm_ops()
    cases: dict[str, tuple[str, str | None]] = {"control": (gen, None)}
    if not args.control_only:
        cases.update(mutants(gen))
    if args.work:
        args.work.mkdir(parents=True, exist_ok=False)
        work = args.work
    else:
        holder = tempfile.TemporaryDirectory(prefix="air2lean-asm-effects-")
        work = Path(holder.name)
    failed = False
    for case, (text, expected) in cases.items():
        status, output = a03.run_program(program(text, ops), work / f"{case}.lean")
        (work / f"{case}.log").write_text(output)
        try:
            a03.classify(status, output, expected)
            print(f"{case}: {'passed' if expected is None else 'killed'} (exit {status})")
            if expected is not None:
                log_kill("tests/roadmap/asm-effects/harness.py", case, "tests/roadmap/asm-effects/check.sh")
        except ValueError as error:
            failed = True
            print(f"{case}: {error} (exit {status})\n{output}", file=sys.stderr)
    print(f"asm-effects: {len(cases)} programs")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
