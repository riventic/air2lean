#!/usr/bin/env python3
"""A03: run the real generated asm wrappers against a test-only executable interpretation.

Proofs/Asm/Gen.lean is the translator's checked output for examples/asm/asm.zig. This script
binds each `opaque airAsm_<hash>` to the AIR `assembly` instruction with the same translator
hash (tests/golden/asm/air), rewrites only those opaque lines and the namespace lines, appends
Interp.lean, the bindings, sampled inputs and Runner.lean, and runs the program with
`lake env lean --run`. Mutants alter the generated wrapper text in memory before the rewrite;
each must elaborate and then fail with a named wrapper mismatch.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
GEN = ROOT / "Proofs/Asm/Gen.lean"
AIR = ROOT / "tests/golden/asm/air"
DIFF_INPUTS = ROOT / "tests/diff/asm/inputs"
NAMESPACE = "AsmHarness.Wrappers"
FUNCTIONS = ("bswap32", "popcnt64", "lzcnt64", "divmod")
OPAQUE = re.compile(r"opaque (airAsm_\d+)((?: \(i\d+ : BitVec \d+\))*) : (.+)")
PARAM = re.compile(r" \((i\d+) : BitVec (\d+)\)")
LEAN_ERROR = re.compile(r"^\S.*:\d+:\d+: error")


def fnv1a(text: str) -> int:
    """`Air2Lean/Emit.lean`'s `asmDefName` hash: FNV-1a over code points, mod 2^32."""
    h = 0x811C9DC5
    for c in text:
        h = ((h ^ ord(c)) * 0x01000193) & 0xFFFFFFFF
    return h


def asm_ops(air_dir: Path = AIR) -> dict[str, dict]:
    """Each AIR `assembly` instruction keyed by the opaque name the translator gives it."""
    ops: dict[str, dict] = {}
    for path in sorted(air_dir.glob("*.json")):
        func = json.loads(path.read_text())
        types, insts = func["types"], {i["id"]: i for i in func["body"]}

        def bits(ty: int) -> int:
            return types[ty]["bits"] if types[ty]["k"] == "int" else 0

        for inst in func["body"]:
            if inst["tag"] != "assembly":
                continue
            inputs = [bits(insts[o["ref"]["inst"]]["ty"]) for o in inst["inputs"]]
            outputs = [bits(types[insts[o["ref"]["inst"]]["ty"]]["child"]) if "ref" in o else bits(inst["ty"])
                       for o in inst["outputs"]]
            outs = ("none" if not outputs else f"(some {outputs[0]})" if len(outputs) == 1
                    else "[" + ", ".join(map(str, outputs)) + "]")
            constraints = [o["constraint"] for o in inst["outputs"] + inst["inputs"]]
            # `asmKey`: the constraints are one field (empty when there are none).
            key = "\x01".join([inst["source"], "\x01".join(constraints),
                                "[" + ", ".join(map(str, inputs)) + "]", outs])
            name = f"airAsm_{fnv1a(key)}"
            op = {"function": func["name"].rsplit(".", 1)[-1], "source": inst["source"],
                  "outputs": [[o["constraint"], o["name"], w] for o, w in zip(inst["outputs"], outputs)],
                  "inputs": [[o["constraint"], o["name"], w] for o, w in zip(inst["inputs"], inputs)],
                  "clobbers": list(inst["clobbers"])}
            if ops.setdefault(name, op) != op:
                raise ValueError(f"hash collision for {name}")
    return ops


def lean_string(text: str) -> str:
    return json.dumps(text)


def lean_operands(operands: list) -> str:
    return "[" + ", ".join(f"⟨{lean_string(c)}, {lean_string(n)}, {w}⟩" for c, n, w in operands) + "]"


def binding(name: str, params: str, ret: str, op: dict) -> str:
    """The `def` replacing one opaque line: same name, parameters and type."""
    args = [(p, int(w)) for p, w in PARAM.findall(params)]
    if [w for _, w in args] != [w for _, _, w in op["inputs"]]:
        raise ValueError(f"{name}: parameter widths differ from AIR inputs")
    widths = [w for _, _, w in op["outputs"]]
    expected = "Unit" if not widths else " × ".join(f"BitVec {w}" for w in widths)
    if ret != expected:
        raise ValueError(f"{name}: result type differs from AIR outputs")
    spec = (f"{{ source := {lean_string(op['source'])}, outputs := {lean_operands(op['outputs'])}, "
            f"inputs := {lean_operands(op['inputs'])}, clobbers := [{', '.join(map(lean_string, op['clobbers']))}] }}")
    run = f"AsmHarness.Interp.run {spec} [{', '.join(f'{p}.toNat' for p, _ in args)}]"
    if not widths:
        value = "()"
    elif len(widths) == 1:
        value = f"BitVec.ofNat {widths[0]} (o.getD 0 0)"
    else:
        value = "(" + ", ".join(f"BitVec.ofNat {w} (o.getD {k} 0)" for k, w in enumerate(widths)) + ")"
    return f"def {name}{params} : {ret} :=\n  let o := {run}\n  {value}"


def rebind(gen: str, ops: dict[str, dict]) -> str:
    """Change only `import`, namespace and opaque lines; every wrapper line stays verbatim."""
    lines, seen = gen.split("\n"), set()
    if lines.count("namespace Asm") != 1 or lines.count("end Asm") != 1:
        raise ValueError("generated namespace shape changed")
    out = []
    for line in lines:
        if line.startswith("import "):
            if line != "import ZigLean":
                raise ValueError(f"unexpected generated import: {line}")
            continue
        if line == "namespace Asm":
            line = f"namespace {NAMESPACE}"
        elif line == "end Asm":
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


def bound(ops: dict[str, dict]) -> str:
    by_function = {op["function"]: name for name, op in ops.items()}
    if sorted(by_function) != sorted(FUNCTIONS) or len(by_function) != len(ops):
        raise ValueError("expected exactly one asm statement in each of " + ", ".join(FUNCTIONS))
    body = "".join(f"abbrev {fn} := {NAMESPACE}.{by_function[fn]}\n" for fn in FUNCTIONS)
    return f"namespace AsmHarness.Bound\n{body}end AsmHarness.Bound\n"


def lcg(seed: int, count: int, bits: int) -> list[int]:
    values, state = [], seed
    for _ in range(count):
        state = (state * 6364136223846793005 + 1442695040888963407) % 2 ** 64
        values.append(state >> (64 - bits))
    return values


def unique(values: list) -> list:
    return list(dict.fromkeys(values))


def sampled_inputs(diff_dir: Path = DIFF_INPUTS) -> dict[str, list]:
    """Diff-test inputs, edge values and deterministic pseudo-random values per function."""
    def read(fn: str) -> list:
        return [json.loads(line) for line in (diff_dir / f"{fn}.jsonl").read_text().splitlines() if line]

    edges32 = [0, 1, 2, 0xFF, 0x12345678, 0x7FFFFFFF, 0x80000000, 0x80000001, 0xFFFFFFFE, 0xFFFFFFFF]
    edges64 = [0, 1, 0b1011, 1 << 31, 1 << 32, (1 << 63) - 1, 1 << 63, 2 ** 64 - 2, 2 ** 64 - 1]
    randoms64 = lcg(0xA03, 400, 64)
    inputs = {
        "bswap32": unique(edges32 + [x for [x] in read("bswap32")] + lcg(0xA031, 400, 32)),
        "popcnt64": unique(edges64 + [int(x) for [x] in read("popcnt64")] + randoms64),
        "lzcnt64": unique(edges64 + [int(x) for [x] in read("lzcnt64")]
                          + [x >> (x % 64) for x in randoms64]),
    }
    pairs = ([(a, b) for a in edges32 for b in edges32] + [tuple(p) for p in read("divmod")]
             + list(zip(lcg(0xA032, 400, 32), lcg(0xA033, 400, 32)))
             + list(zip(lcg(0xA034, 200, 32), lcg(0xA035, 200, 8))))
    # A zero operand is a #DE fault in the operand-swapped mutant; it is not a wrapper result.
    inputs["divmod"] = unique([p for p in pairs if p[0] and p[1]])
    return inputs


def inputs_module(inputs: dict[str, list]) -> str:
    def nats(values: list[int]) -> str:
        return lean_string(" ".join(map(str, values)))

    pairs = lean_string(" ".join(f"{a}:{b}" for a, b in inputs["divmod"]))
    return (
        "namespace AsmHarness.Inputs\n"
        "def nats (s : String) : List Nat := (s.splitOn \" \").map String.toNat!\n"
        "def pairs (s : String) : List (Nat × Nat) :=\n"
        "  (s.splitOn \" \").map fun p => match p.splitOn \":\" with\n"
        "    | [a, b] => (a.toNat!, b.toNat!)\n"
        "    | _ => panic! s!\"bad pair {p}\"\n"
        f"def bswap32 : List Nat := nats {nats(inputs['bswap32'])}\n"
        f"def popcnt64 : List Nat := nats {nats(inputs['popcnt64'])}\n"
        f"def lzcnt64 : List Nat := nats {nats(inputs['lzcnt64'])}\n"
        f"def divmod : List (Nat × Nat) := pairs {pairs}\n"
        "end AsmHarness.Inputs\n")


def program(gen: str, ops: dict[str, dict], inputs: dict[str, list]) -> str:
    return "\n".join(["import ZigLean", (HERE / "Interp.lean").read_text(), rebind(gen, ops),
                      bound(ops), inputs_module(inputs), (HERE / "Runner.lean").read_text()])


def function_span(gen: str, fn: str) -> tuple[int, int]:
    start = gen.index(f"\ndef {fn} ") + 1
    end = gen.find("\nstructure ", start)
    return start, (end if end >= 0 else gen.index("\nend Asm", start))


def alter(gen: str, fn: str, before: str, after: str) -> str:
    start, end = function_span(gen, fn)
    body = gen[start:end]
    if body.count(before) != 1:
        raise ValueError(f"generated shape changed: {fn}: {before!r}")
    return gen[:start] + body.replace(before, after) + gen[end:]


def divmod_shape(gen: str, ops: dict[str, dict]) -> tuple[str, str]:
    """The divmod opaque name and the tuple variable its outputs are bound to."""
    name = next(n for n, op in ops.items() if op["function"] == "divmod")
    start, end = function_span(gen, "divmod")
    # S7: the divisor-zero fault guard (`Zig.asmTrap`) wraps the call.
    match = re.search(rf"let (a\d+) ← Zig\.asmTrap \(p1 = 0\) \({name} p0 p1\)\n", gen[start:end])
    if match is None:
        raise ValueError("generated shape changed: divmod asm call")
    return name, match.group(1)


def mutants(gen: str, ops: dict[str, dict]) -> dict[str, tuple[str, str]]:
    """Mutant name -> (generated text, function whose wrapper check must fail)."""
    name, tup = divmod_shape(gen, ops)
    store = f"modify (fun s => {{ s with rem := {tup}.2 }})"
    return {
        "operand_order": (alter(gen, "divmod", f"{name} p0 p1", f"{name} p1 p0"), "divmod"),
        "result_placement": (alter(gen, "divmod", f"pure {tup}.1", f"pure {tup}.2"), "divmod"),
        "store_dropped": (alter(gen, "divmod", f"    {store}\n", ""), "divmod"),
        "store_misplaced": (alter(gen, "divmod", store, store.replace(f"{tup}.2", f"{tup}.1")), "divmod"),
        "single_result_placement": (alter(gen, "bswap32", "pure (.ret i1)", "pure (.ret p0)"), "bswap32"),
    }


def classify(status: int, output: str, expected: str | None) -> None:
    """Control: exit 0 with PASS. Mutant: exit 1, runner verdict, a wrapper mismatch in `expected`."""
    lines = output.splitlines()
    if any(LEAN_ERROR.match(line) for line in lines):
        raise ValueError("program did not elaborate")
    if expected is None:
        if status != 0 or not any(line.startswith("PASS asm-wrappers ") for line in lines):
            raise ValueError("control did not pass")
        return
    if status != 1 or not any(line.startswith("FAIL asm-wrappers: ") for line in lines):
        raise ValueError("mutant did not elaborate and fail at the runner verdict")
    if any("PANIC" in line or line.startswith("INTERNAL PANIC") for line in lines):
        raise ValueError("mutant faulted instead of producing a wrong result")
    if not any(line.startswith(f"MISMATCH wrapper {expected} ") for line in lines):
        raise ValueError(f"mutant did not fail the {expected} wrapper check")


def run_program(text: str, path: Path) -> tuple[int, str]:
    path.write_text(text)
    env = dict(os.environ, LEAN_ABORT_ON_PANIC="1")
    result = subprocess.run(["lake", "env", "lean", "--run", str(path)], cwd=ROOT, env=env,
                            text=True, capture_output=True)
    return result.returncode, result.stdout + result.stderr


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--work", type=Path, help="keep generated programs and logs in this fresh directory")
    parser.add_argument("--control-only", action="store_true", help="skip the mutants")
    args = parser.parse_args()
    gen, ops, inputs = GEN.read_text(), asm_ops(), sampled_inputs()
    cases: dict[str, tuple[str, str | None]] = {"control": (gen, None)}
    if not args.control_only:
        cases.update(mutants(gen, ops))
    if args.work:
        args.work.mkdir(parents=True, exist_ok=False)
        work = args.work
    else:
        holder = tempfile.TemporaryDirectory(prefix="air2lean-asm-wrappers-")
        work = Path(holder.name)
    failed = False
    for case, (text, expected) in cases.items():
        status, output = run_program(program(text, ops, inputs), work / f"{case}.lean")
        (work / f"{case}.log").write_text(output)
        try:
            classify(status, output, expected)
            print(f"{case}: {'passed' if expected is None else 'killed'} (exit {status})")
        except ValueError as error:
            failed = True
            print(f"{case}: {error} (exit {status})\n{output}", file=sys.stderr)
    counts = {fn: len(v) for fn, v in inputs.items()}
    print(f"asm-wrappers: {len(cases)} programs, inputs {counts}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
