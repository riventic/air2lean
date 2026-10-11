#!/usr/bin/env python3
"""Require fresh indirect-call AIR, then produce checks of translated source behavior."""
import importlib.util
import json
from pathlib import Path
import sys


# Share the existing traversal contract for nested AIR bodies and switch cases.
spec = importlib.util.spec_from_file_location("dispatch_native_checks",
    Path(__file__).resolve().parent.parent / "dispatch" / "native_checks.py")
dispatch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(dispatch)
nested_insts = dispatch.nested_insts

# Functions whose body must keep a call through a runtime function pointer.
INDIRECT = ["source.viaTable", "source.viaGlobal", "source.viaField", "source.twice",
            "source.viaMemory"]
REQUIRED = set(INDIRECT) | {"source.fieldCaller", "source.viaParam", "source.memoryCaller",
                            "source.double", "source.succ", "source.square"}
TARGETS = {"source.double", "source.succ", "source.square"}


def function_globals(raw):
    return {g["init"]["func"] for g in raw.get("globals", [])
            if isinstance(g.get("init"), dict) and "func" in g["init"]}


def check_inventory(directory, version):
    functions = {}
    for path in Path(directory).glob("*.json"):
        raw = json.loads(path.read_text())
        assert raw["zig_version"] == version, path
        assert raw["name"] not in functions, "duplicate exported function"
        functions[raw["name"]] = raw
    assert REQUIRED <= functions.keys(), (REQUIRED, functions.keys())
    for name in INDIRECT:
        calls = [i for i in nested_insts(functions[name]["body"]) if i["tag"].startswith("call")]
        assert any("inst" in i.get("callee", {}) for i in calls), (name, "indirect call disappeared")
    # The table of address-taken functions must declare every target.
    declared = set()
    for raw in functions.values():
        declared |= function_globals(raw)
    assert TARGETS <= declared, ("address-taken targets disappeared", declared)


def checks():
    lines = ["\nprivate def memoryValue (r : Zig.MemM α) : Option α := "
             "((r.run (IndirectCallsNative.mem0 .fresh)).run.bind Except.toOption).map Prod.fst"]
    m = 2 ** 32
    for n in [0, 3, 255, 0xffffffff]:
        cases = [
            ("viaTable 0", n * 2), ("viaTable 1", n + 1), ("viaTable 5", n * n),
            ("viaGlobal false", n + 1), ("viaGlobal true", n * n),
            ("fieldCaller", n * n + 4), ("viaParam true", (n * n % m) ** 2),
            ("viaParam false", n * 4), ("memoryCaller", (n + 1) + n * 2)]
        for call, value in cases:
            lines.append(f"example : (memoryValue (IndirectCallsNative.{call} {n})).map BitVec.toNat"
                         f" = some {value % m} := by decide +kernel")
    return "\n".join(lines) + "\n"


def main():
    directory, version, output = sys.argv[1:]
    check_inventory(directory, version)
    Path(output).write_text(checks())


if __name__ == "__main__":
    main()
