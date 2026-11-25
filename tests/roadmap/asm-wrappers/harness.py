#!/usr/bin/env python3
"""A03: run the real generated asm wrappers and cross-check their instruction-model definitions.

Proofs/Asm/Gen.lean is the translator's checked output for examples/asm/asm.zig. Every inline-asm
statement in it is a defined function over the x86_64 instruction model (`def airIsa_<hash>`,
A02, premise ASM-07), so the generated text runs as it is: this script changes only the `import`
and the namespace lines. It binds each `airIsa_<hash>` to the AIR `assembly` instruction with the
same translator hash (tests/golden/asm/air) and adds, for each, the test-only interpretation of
that instruction's template text (Interp.lean, an implementation that shares no code with the
model or the translator's decoder). `lake env lean --run` then checks

* each wrapper against the Zig source semantics (Runner.lean), and
* each `airIsa_<hash>` against the interpretation on sampled operands (`AsmHarness.Cross`).

Mutants alter the generated wrapper text in memory; each must elaborate and then fail with a
named wrapper mismatch.
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
sys.path.insert(0, str(ROOT / "scripts"))
from mutation_kill_log import killed as log_kill  # noqa: E402
GEN = ROOT / "Proofs/Asm/Gen.lean"
AIR = ROOT / "tests/golden/asm/air"
DIFF_INPUTS = ROOT / "tests/diff/asm/inputs"
NAMESPACE = "AsmHarness.Wrappers"
FUNCTIONS = ("bswap32", "popcnt64", "lzcnt64", "divmod")
ISA_DEF = re.compile(r"def (airIsa(?:Fx)?_\d+)((?: \(i\d+ : BitVec \d+\))*) : (.+) :=")
PARAM = re.compile(r" \((i\d+) : BitVec (\d+)\)")
LEAN_ERROR = re.compile(r"^\S.*:\d+:\d+: error")


def fnv1a(text: str) -> int:
    """`Air2Lean/Emit.lean`'s `asmDefName` hash: FNV-1a over code points, mod 2^32."""
    h = 0x811C9DC5
    for c in text:
        h = ((h ^ ord(c)) * 0x01000193) & 0xFFFFFFFF
    return h


def asm_ops(air_dir: Path = AIR) -> dict[str, dict]:
    """Each AIR `assembly` instruction keyed by the name the translator gives its definition."""
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
            op = {"function": func["name"].rsplit(".", 1)[-1], "source": inst["source"],
                  "outputs": [[o["constraint"], o["name"], w] for o, w in zip(inst["outputs"], outputs)],
                  "inputs": [[o["constraint"], o["name"], w] for o, w in zip(inst["inputs"], inputs)],
                  "clobbers": list(inst["clobbers"])}
            name = ("airIsaFx_" if is_effect(op) else "airIsa_") + str(fnv1a(key))
            if ops.setdefault(name, op) != op:
                raise ValueError(f"hash collision for {name}")
    return ops


def is_effect(op: dict) -> bool:
    """`Air2Lean/AsmContract.lean`'s `asmIsEffect`: a read-write or memory output, or a
    `"memory"` clobber (registry-approved, else the translator rejects it)."""
    return "memory" in op["clobbers"] or any(
        c.startswith("+") or c[1:] == "m" for c, _, _ in op["outputs"])


def lean_string(text: str) -> str:
    return json.dumps(text)


def lean_operands(operands: list) -> str:
    return "[" + ", ".join(f"⟨{lean_string(c)}, {lean_string(n)}, {w}⟩" for c, n, w in operands) + "]"


def interpretation(name: str, params: str, ret: str, op: dict) -> str:
    """The interpreted counterpart of one `def airIsa_<hash>`: same name, parameters (the
    inputs, then the old value of each `+` output) and type."""
    args = [(p, int(w)) for p, w in PARAM.findall(params)]
    rw = [w for c, _, w in op["outputs"] if c.startswith("+")]
    if [w for _, w in args] != [w for _, _, w in op["inputs"]] + rw:
        raise ValueError(f"{name}: parameter widths differ from AIR inputs and read-write outputs")
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
    return f"def {name}{params} : {ret} :=\n  let {'o' if widths else '_o'} := {run}\n  {value}"


def isa_defs(gen: str, ops: dict[str, dict]) -> dict[str, tuple[str, str]]:
    """Name -> (parameters, type) of each generated `def airIsa_<hash>`; exactly the AIR ops."""
    defs: dict[str, tuple[str, str]] = {}
    for line in gen.split("\n"):
        match = ISA_DEF.fullmatch(line)
        if match is None:
            continue
        name, params, ret = match.groups()
        if name not in ops or name in defs:
            raise ValueError(f"asm definition without one AIR assembly binding: {line}")
        defs[name] = (params, ret)
    if set(defs) != set(ops):
        raise ValueError(f"AIR assembly without a generated definition: {sorted(set(ops) - set(defs))}")
    return defs


def rebind(gen: str, ops: dict[str, dict], namespace: str = "Asm") -> str:
    """Change only the profile header, `import` and namespace lines; every generated declaration
    stays verbatim. An uninterpreted declaration (the opaque fallback of a statement the
    instruction model does not cover) cannot run and is refused."""
    lines, out = gen.split("\n"), []
    if lines.count(f"namespace {namespace}") != 1 or lines.count(f"end {namespace}") != 1:
        raise ValueError("generated namespace shape changed")
    isa_defs(gen, ops)
    for line in lines:
        if line.startswith("-- air2lean-profile:"):
            continue
        if line.startswith("import "):
            if line != "import ZigLean":
                raise ValueError(f"unexpected generated import: {line}")
            continue
        if line == f"namespace {namespace}":
            line = f"namespace {NAMESPACE}"
        elif line == f"end {namespace}":
            line = f"end {NAMESPACE}"
        elif re.match(r"\s*(?:opaque|axiom)\b", line):
            raise ValueError(f"unexpected uninterpreted declaration: {line}")
        out.append(line)
    return "\n".join(out)


def cross(gen: str, ops: dict[str, dict]) -> str:
    """`AsmHarness.Cross`: each `airIsa_<hash>` against the interpretation of its template on
    sampled operands. Operands on which the model reports a fault are skipped (the
    interpretation panics there; the wrapper checks and the differential test cover faults)."""
    defs = isa_defs(gen, ops)
    body, checks = [], []
    for name, (params, ret) in defs.items():
        body.append(interpretation(name, params, ret, ops[name]))
        args = PARAM.findall(params)
        call = " ".join(p for p, _ in args)
        shown = " ".join(f"{{{p}.toNat}}" for p, _ in args)
        agree = f"{NAMESPACE}.{name} {call} == {name} {call}".replace("  ", " ")
        if f"def {name}_fault" in gen:
            agree = f"({NAMESPACE}.{name}_fault {call}).isSome || {agree}"
        check = f'if {agree} then [] else [s!"MISMATCH model {name} {shown}"]'
        for p, w in reversed(args):
            check = f"(samples {w}).flatMap fun {p} => {check}"
        checks.append(f"  ({check})")
    return ("namespace AsmHarness.Cross\n"
            "def lcg (seed count : Nat) : List Nat :=\n"
            "  (List.range count).foldl (init := ([], seed)) (fun (acc, s) _ =>\n"
            "    let s := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64\n"
            "    (acc ++ [s], s)) |>.1\n"
            "def samples (w : Nat) : List (BitVec w) :=\n"
            "  ([0, 1, 2, 0xFF, 2 ^ (w - 1) - 1, 2 ^ (w - 1), 2 ^ (w - 1) + 1, 2 ^ w - 2, 2 ^ w - 1]\n"
            "    ++ lcg (0xA02 + w) 24).map (BitVec.ofNat w)\n"
            + "\n".join(body) + "\n"
            "def failures : List String :=\n" + " ++\n".join(checks or ["  []"]) + "\n"
            "end AsmHarness.Cross\n")


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
    functions = sorted(op["function"] for op in ops.values())
    if functions != sorted(FUNCTIONS):
        raise ValueError("expected exactly one asm statement in each of " + ", ".join(FUNCTIONS))
    return "\n".join(["import ZigLean", (HERE / "Interp.lean").read_text(), rebind(gen, ops),
                      cross(gen, ops), inputs_module(inputs), (HERE / "Runner.lean").read_text()])


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
    """The divmod definition's name and the tuple variable its outputs are bound to."""
    name = next(n for n, op in ops.items() if op["function"] == "divmod")
    start, end = function_span(gen, "divmod")
    # The call is guarded by the model's own fault condition (`Zig.Asm.isaFault`).
    match = re.search(rf"let (a\d+) ← Zig\.Asm\.isaFault \({name}_fault p0 p1\) \({name} p0 p1\)\n",
                      gen[start:end])
    if match is None:
        raise ValueError("generated shape changed: divmod asm call")
    return name, match.group(1)


def mutants(gen: str, ops: dict[str, dict]) -> dict[str, tuple[str, str]]:
    """Mutant name -> (generated text, function whose wrapper check must fail)."""
    name, tup = divmod_shape(gen, ops)
    store = f"modify (fun s => {{ s with rem := {tup}.2 }})"
    return {
        "operand_order": (alter(gen, "divmod", f"({name} p0 p1)", f"({name} p1 p0)"), "divmod"),
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
    if any(line.startswith("MISMATCH model ") for line in lines):
        raise ValueError("the instruction model disagrees with the interpretation")
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
            if expected is not None:
                log_kill("tests/roadmap/asm-wrappers/harness.py", case, "tests/roadmap/asm-wrappers/harness.py")
        except ValueError as error:
            failed = True
            print(f"{case}: {error} (exit {status})\n{output}", file=sys.stderr)
    counts = {fn: len(v) for fn, v in inputs.items()}
    print(f"asm-wrappers: {len(cases)} programs, inputs {counts}")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
