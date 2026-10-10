#!/usr/bin/env python3
"""CLI regressions for the translated `ArenaAllocator` (`--allocator-model translated`).

The retained exports (air/0.16.0) are accepted only in translated mode, and each admission that
the arena needs fails closed in its neighbouring case: a pointer cast over a cyclic type graph
that can reach error storage, and an `unordered` load of a type other than an integer, a packed
struct or a pointer. Never builds or invokes compilers.
"""
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "alloc-translated"))
import test_cli as base  # noqa: E402

base.AIR = Path(__file__).resolve().parent / "air" / "0.16.0"
CYCLIC = "a pointer cast has unresolved or cyclic symbolic storage provenance"


def main(binary):
    linux = base.load("arena-linux")
    base.accept(binary, linux, "arena.")
    base.accept(binary, base.load("arena-macos"), "arena.")

    # Std mode keeps the built-in allocator model and its strict cast rule.
    for flags in ([], ["--allocator-model", "std"]):
        result, report, _ = base.run(binary, linux, flags, "arena.")
        assert result.returncode == 1 and report["status"] == "rejected", flags
        assert any(CYCLIC in d["message"] for d in report["diagnostics"]), flags

    # The `Node` graph is cyclic (`next: ?*Node`). With an error union in it, the cast between
    # `*Node` and its bytes would expose symbolic error storage: rejected.
    mutated = json.loads(json.dumps(linux))
    doc = base.find(mutated, "heap.ArenaAllocator.Node.allocatedSliceUnsafe.json")
    types = doc["types"]
    types.append({"k": "error_set", "errors": ["Oops"], "abi_size": 2, "abi_align": 2})
    types.append({"k": "error_union", "error": len(types) - 1, "payload": 10,
                  "abi_size": 16, "abi_align": 8})
    node = next(t for t in types if t.get("name") == "heap.ArenaAllocator.Node")
    next(f for f in node["fields"] if f["name"] == "end_index")["ty"] = len(types) - 1
    base.reject(binary, mutated, CYCLIC, "arena.")

    # An `unordered` load of a `bool` (an atomic type, but neither an integer, a packed struct nor
    # a pointer) stays rejected.
    mutated = json.loads(json.dumps(linux))
    doc = base.find(mutated, "heap.ArenaAllocator.Node.endResize.json")
    types = doc["types"]
    types.append({"k": "bool", "abi_size": 1, "abi_align": 1})
    types.append({"k": "ptr", "size": "one", "const": False, "child": len(types) - 1, "ptr_align": 8,
                  "volatile": False, "allowzero": False, "sentinel": False, "host_size": 0,
                  "abi_size": 8, "abi_align": 8})
    insts = {i["id"]: i for i in base.walk(doc["body"])}
    hit = False
    for inst in base.walk(doc["body"]):
        if inst.get("tag") == "atomic_load" and inst.get("order") == "unordered":
            operand = insts[inst["args"][0]["inst"]]
            operand["ty"] = len(types) - 1
            inst["ty"] = len(types) - 2
            hit = True
    assert hit
    base.reject(binary, mutated, "an `unordered` load of a type other than an integer, a packed "
                "struct or a pointer is outside the subset", "arena.")
    print("alloc-arena CLI regressions passed")


if __name__ == "__main__":
    main(Path(sys.argv[1]))
