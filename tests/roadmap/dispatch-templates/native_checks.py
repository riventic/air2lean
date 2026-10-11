#!/usr/bin/env python3
"""Check the exported tokenizer's dispatch inventory, write target mutants and value checks.

usage: native_checks.py AIR_DIR VERSION CHECKS_OUT MUTANTS_DIR

Each mutant directory holds the real exported AIR with one `switch_dispatch` target replaced
by an ID that is not an enclosing loop-switch; check.sh requires air2lean to reject it.
"""
import copy
import json
from pathlib import Path
import sys


def nested(body):
    for inst in body:
        yield inst
        for field in ("body", "then", "else"):
            yield from nested(inst.get(field, []))
        for case in inst.get("cases", []):
            yield from nested(case.get("body", []))


SAMPLES = {"sampleA": 3, "sampleB": 4, "sampleC": 0, "sampleD": 6}


def main():
    air, version, output, mutants = sys.argv[1:]
    functions = {}
    for path in Path(air).glob("*.json"):
        raw = json.loads(path.read_text())
        assert raw["zig_version"] == version, path
        functions[raw["name"]] = (path, raw)
    required = {"source.countTokens"} | {f"source.{name}" for name in SAMPLES}
    assert required <= functions.keys(), (sorted(functions), sorted(required))

    path, tok = functions["source.countTokens"]
    insts = list(nested(tok["body"]))
    loops = [i["id"] for i in insts if i["tag"] == "loop_switch_br"]
    assert len(loops) == 1, f"expected one loop-switch, got {loops}"
    dispatches = [i for i in insts if i["tag"] == "switch_dispatch"]
    # start -> {done, ident, number, start}, ident -> {ident, start}, number -> {number, start}.
    assert len(dispatches) >= 8, f"dispatch edges were lowered away: {len(dispatches)}"
    assert all(d["target"] == loops[0] for d in dispatches), "dispatch to a foreign target"

    blocks = [i["id"] for i in insts if i["tag"] == "block"]
    absent = max(i["id"] for i in insts) + 1000
    for name, target in [("block", blocks[0]), ("absent", absent), ("self", dispatches[0]["id"])]:
        raw = copy.deepcopy(tok)
        victim = next(i for i in nested(raw["body"]) if i["tag"] == "switch_dispatch")
        victim["target"] = target
        out = Path(mutants) / name
        out.mkdir(parents=True, exist_ok=True)
        for other, (other_path, other_raw) in functions.items():
            text = json.dumps(raw if other == "source.countTokens" else other_raw)
            (out / other_path.name).write_text(text)
        (out / "target").write_text(f"{target}\n")

    checks = ["\nprivate def tokResult (x : Zig.MemM (BitVec 32)) : Option Nat :=",
              "  match (x.run (Tok.mem0 .fresh)).run with",
              "  | some (.ok (v, _)) => some v.toNat",
              "  | _ => none"]
    for name, expected in SAMPLES.items():
        checks.append(f"example : tokResult Tok.{name} = some {expected} := by native_decide")
    Path(output).write_text("\n".join(checks) + "\n")


if __name__ == "__main__":
    main()
