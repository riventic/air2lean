#!/usr/bin/env python3
"""Require fresh local projection AIR, then produce checks of translated source behavior."""
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


def check_inventory(directory, version):
    functions = {}
    for path in Path(directory).glob("*.json"):
        raw = json.loads(path.read_text())
        assert raw["zig_version"] == version, path
        assert raw["name"] not in functions, "duplicate exported function"
        functions[raw["name"]] = raw
    required = {"source.direct", "source.nested", "source.castAlias", "source.escaped", "source.write",
                "source.arrayItem"}
    assert required <= functions.keys(), (required, functions.keys())
    for name in required - {"source.write"}:
        insts = list(nested_insts(functions[name]["body"]))
        tags = [i["tag"] for i in insts]
        assert "alloc" in tags, (name, "local alloc disappeared")
        assert "field_parent_ptr" in tags, (name, "parent operation disappeared")
        assert any(t.startswith("struct_field_ptr") for t in tags), (name, "field projection disappeared")
    nested = list(nested_insts(functions["source.nested"]["body"]))
    assert sum(i["tag"] == "field_parent_ptr" for i in nested) >= 2, "nested recovery disappeared"
    assert any(i["tag"] == "bitcast" for i in nested_insts(functions["source.castAlias"]["body"])), "const alias cast disappeared"
    assert any(i["tag"] == "call" for i in nested_insts(functions["source.escaped"]["body"])), "escape call disappeared"
    # L11: recovery from a field of an array element inside a struct, then of the struct.
    item = list(nested_insts(functions["source.arrayItem"]["body"]))
    assert sum(i["tag"] == "field_parent_ptr" for i in item) >= 2, "array-element recovery disappeared"
    assert any(i["tag"] in ("ptr_elem_ptr", "array_elem_ptr") for i in item), "array element projection disappeared"


def checks():
    lines = ["\nprivate def successful {α : Type} (r : Zig.Result α) : Option α := Option.bind r Except.toOption",
             "private def memoryValue (r : Zig.MemM α) : Option α := ((r.run {}).run.bind Except.toOption).map Prod.fst"]
    for name, delta in [("direct", 12), ("nested", 18), ("castAlias", 33), ("escaped", 42)]:
        for n in [0, 3, 255, 0xffffffff]:
            expr = f"LocalParentNative.{name} {n}"
            observe = "memoryValue" if name == "escaped" else "successful"
            lines.append(f"example : ({observe} ({expr})).map BitVec.toNat = some {(n + delta) % 2**32} := by decide +kernel")
    for n in [0, 3, 255, 0xffffffff]:
        for i, value in [(1, 6 + n + 27 + 5), (0, 6 + 30 + 9), (5, 6 + n + 27 + 5)]:
            lines.append(f"example : (memoryValue (LocalParentNative.arrayItem {n} {i})).map BitVec.toNat = some {value % 2**32} := by decide +kernel")
    return "\n".join(lines) + "\n"


def main():
    directory, version, output = sys.argv[1:]
    check_inventory(directory, version)
    Path(output).write_text(checks())


if __name__ == "__main__":
    main()
