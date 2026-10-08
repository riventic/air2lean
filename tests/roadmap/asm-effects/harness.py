#!/usr/bin/env python3
"""A01: run the generated effect-contract asm wrappers under the A03 test-only interpretation.

AsmEffects/Gen.lean is the translator's checked output for air/0.16.0. Each `opaque
airAsmFx_<hash>`/`airAsm_<hash>` is bound to the AIR `assembly` instruction with the same
translator hash and rewritten into a `def` that runs `AsmHarness.Interp.run` (with the old
values of read-write outputs as trailing arguments). Every wrapper line stays verbatim.
Runner.lean then runs the wrappers on model memory and checks each written location, every
other byte of the block (the frame), the alias case and the local operands. Mutants alter the
generated text in memory; each must elaborate and fail with a named wrapper mismatch.
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
GEN = HERE / "AsmEffects/Gen.lean"
AIR = HERE / "air/0.16.0"
A03 = ROOT / "tests/roadmap/asm-wrappers"
NAMESPACE = "AsmHarness.Wrappers"
OPAQUE = re.compile(r"opaque (airAsm(?:Fx)?_\d+)((?: \(i\d+ : BitVec \d+\))*) : (.+)")
PARAM = re.compile(r" \((i\d+) : BitVec (\d+)\)")
FUNCTIONS = ("incm", "setm", "swapm", "addr", "incLocal", "barrier")


def load_a03():
    spec = importlib.util.spec_from_file_location("asm_wrappers_harness", A03 / "harness.py")
    module = importlib.util.module_from_spec(spec)
    sys.dont_write_bytecode = True
    spec.loader.exec_module(module)
    return module


a03 = load_a03()


def is_effect(op: dict) -> bool:
    """`Air2Lean/AsmContract.lean`'s `asmIsEffect`: a read-write or memory output, or a
    `"memory"` clobber (registry-approved, else the translator rejects it)."""
    return "memory" in op["clobbers"] or any(
        c.startswith("+") or c[1:] == "m" for c, _, _ in op["outputs"])


def asm_ops(air_dir: Path = AIR) -> dict[str, dict]:
    """A03's hash binding, with the effect-form name for effect-contract ops."""
    ops = {}
    for name, op in a03.asm_ops(air_dir).items():
        if is_effect(op):
            name = "airAsmFx_" + name[len("airAsm_"):]
        ops[name] = op
    return ops


def binding(name: str, params: str, ret: str, op: dict) -> str:
    """The `def` replacing one opaque line: inputs, then the old value of each `+` output."""
    args = [(p, int(w)) for p, w in PARAM.findall(params)]
    rw = [w for c, _, w in op["outputs"] if c.startswith("+")]
    if [w for _, w in args] != [w for _, _, w in op["inputs"]] + rw:
        raise ValueError(f"{name}: parameter widths differ from AIR inputs and read-write outputs")
    widths = [w for _, _, w in op["outputs"]]
    expected = "Unit" if not widths else " × ".join(f"BitVec {w}" for w in widths)
    if ret != expected:
        raise ValueError(f"{name}: result type differs from AIR outputs")
    spec = (f"{{ source := {a03.lean_string(op['source'])}, outputs := {a03.lean_operands(op['outputs'])}, "
            f"inputs := {a03.lean_operands(op['inputs'])}, "
            f"clobbers := [{', '.join(map(a03.lean_string, op['clobbers']))}] }}")
    run = f"AsmHarness.Interp.run {spec} [{', '.join(f'{p}.toNat' for p, _ in args)}]"
    if not widths:
        value = "()"
    elif len(widths) == 1:
        value = f"BitVec.ofNat {widths[0]} (o.getD 0 0)"
    else:
        value = "(" + ", ".join(f"BitVec.ofNat {w} (o.getD {k} 0)" for k, w in enumerate(widths)) + ")"
    if not params:
        return f"def {name} : {ret} :=\n  let _o := {run}\n  {value}"
    return f"def {name}{params} : {ret} :=\n  let o := {run}\n  {value}"


def rebind(gen: str, ops: dict[str, dict]) -> str:
    """Change only the profile header, `import`, namespace and opaque lines."""
    lines, seen, out = gen.split("\n"), set(), []
    if lines.count("namespace AsmEffects") != 1 or lines.count("end AsmEffects") != 1:
        raise ValueError("generated namespace shape changed")
    for line in lines:
        if line.startswith("-- air2lean-profile:"):
            continue
        if line.startswith("import "):
            if line != "import ZigLean":
                raise ValueError(f"unexpected generated import: {line}")
            continue
        if line == "namespace AsmEffects":
            line = f"namespace {NAMESPACE}"
        elif line == "end AsmEffects":
            line = f"end {NAMESPACE}"
        elif line.startswith("opaque "):
            match = OPAQUE.fullmatch(line)
            if match is None or match.group(1) not in ops or match.group(1) in seen:
                raise ValueError(f"opaque without one AIR assembly binding: {line}")
            seen.add(match.group(1))
            line = binding(*match.groups(), ops[match.group(1)])
        elif "opaque" in line or "axiom" in line:
            raise ValueError(f"unexpected uninterpreted declaration: {line}")
        out.append(line)
    if seen != set(ops):
        raise ValueError(f"AIR assembly without generated opaque: {sorted(set(ops) - seen)}")
    return "\n".join(out)


def program(gen: str, ops: dict[str, dict]) -> str:
    by_function = {op["function"] for op in ops.values()}
    if sorted(by_function) != sorted(FUNCTIONS):
        raise ValueError("expected one asm statement in each of " + ", ".join(FUNCTIONS))
    return "\n".join(["import ZigLean", (A03 / "Interp.lean").read_text(), rebind(gen, ops),
                      (HERE / "Runner.lean").read_text()])


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
        match = re.compile(r"let (a\d+) := (airAsmFx_\d+)((?: \w+)*)\n").search(gen, start)
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
        except ValueError as error:
            failed = True
            print(f"{case}: {error} (exit {status})\n{output}", file=sys.stderr)
    print(f"asm-effects: {len(cases)} programs")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
