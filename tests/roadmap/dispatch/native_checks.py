#!/usr/bin/env python3
"""Validate real AIR control-flow inventory and append semantic checks to translated source."""
import json
from pathlib import Path
import sys


def nested_insts(body):
    for inst in body:
        yield inst
        for field in ("body", "then", "else"):
            yield from nested_insts(inst.get(field, []))
        for case in inst.get("cases", []):
            yield from nested_insts(case.get("body", []))


def main():
    air, version, output = sys.argv[1:]
    functions = {}
    for path in Path(air).glob("*.json"):
        raw = json.loads(path.read_text())
        assert raw["zig_version"] == version, path
        functions[raw["name"]] = raw
    required = {"source.walk", "source.nested", "source.fixedCapture", "source.ranges", "source.enumStep", "source.unionWalk"}
    assert required <= functions.keys(), (functions.keys(), required)
    for name in required:
        tags = {i["tag"] for i in nested_insts(functions[name]["body"])}
        assert {"loop_switch_br", "switch_dispatch"} <= tags, (name, tags)
    nested = list(nested_insts(functions["source.nested"]["body"]))
    assert sum(i["tag"] == "loop_switch_br" for i in nested) >= 2, "native nested dispatch lowered away"
    targets = {i["target"] for i in nested if i["tag"] == "switch_dispatch"}
    assert len(targets) >= 2, "native inner/outer targets were not both exercised"
    checks = ["\nprivate def successful {α : Type} (r : Zig.Result α) : Option α := Option.bind r Except.toOption"]
    for n, base in [(0,0),(3,7),(15,19),(255,0)]:
        expected = (base+n*(n+1)//2)%256
        checks.append(f"example : successful ((DispatchNative.walk {n} {base}).map BitVec.toNat) = some {expected} := by native_decide")
    for mode,n,expected in [(0,2,77),(0,1,88),(0,0,77),(2,0,88),(3,4,99)]:
        checks.append(f"example : successful ((DispatchNative.nested {mode} {n}).map BitVec.toNat) = some {expected} := by native_decide")
    for n,expected in [(0,0),(1,1),(2,9)]:
        checks.append(f"example : successful ((DispatchNative.fixedCapture {n}).map BitVec.toNat) = some {expected} := by native_decide")
    for n,expected in [(2,17),(5,17),(6,23),(10,17)]:
        checks.append(f"example : successful ((DispatchNative.ranges {n}).map BitVec.toNat) = some {expected} := by native_decide")
    for n in [0,1,2]:
        checks.append(f"example : successful ((DispatchNative.enumStep {n}).map BitVec.toNat) = some 42 := by native_decide")
    for n in [0,1,7,255]:
        checks.append(f"example : successful ((DispatchNative.unionWalk {n}).map BitVec.toNat) = some 42 := by native_decide")
    Path(output).write_text("\n".join(checks)+"\n")


if __name__ == "__main__":
    main()
