#!/usr/bin/env python3
"""CLI regressions for the translated `ArenaAllocator` (`--allocator-model translated`).

The retained exports (air/0.16.0) are accepted only in translated mode, and each admission that
the arena needs fails closed in its neighbouring case: a pointer cast over a cyclic type graph
that can reach error storage, and an `unordered` load of a type other than an integer, a packed
struct or a pointer. Never builds or invokes compilers.
"""
import copy
import importlib.util
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
# The shared harness of `alloc-translated`, loaded by path (both files are named `test_cli`).
_spec = importlib.util.spec_from_file_location(
    "alloc_translated_cli", HERE.parent / "alloc-translated" / "test_cli.py")
base = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(base)
base.AIR = HERE / "air" / "0.16.0"
CYCLIC = "a pointer cast has unresolved or cyclic symbolic storage provenance"


def edit(documents, name):
    """`documents` with a deep copy of document `name`, to mutate."""
    doc = copy.deepcopy(documents[name])
    return {**documents, name: doc}, doc


def main(binary):
    linux = base.load("arena-linux")
    base.accept(binary, linux, "arena.")
    base.accept(binary, base.load("arena-macos"), "arena.")

    # Std mode keeps the built-in allocator model and its strict cast rule.
    for flags in ([], ["--allocator-model", "std"]):
        result, report, _ = base.run(binary, linux, flags, "arena.")
        assert result.returncode == 1 and report["status"] == "rejected", flags
        assert any(CYCLIC in d["message"] for d in report["diagnostics"]), flags

    # The `Node` graph is cyclic (`next: ?*Node`). With an error set in it, the cast between
    # `*Node` and its bytes would expose symbolic error storage: rejected.
    mutated, doc = edit(linux, "heap.ArenaAllocator.Node.allocatedSliceUnsafe.json")
    types = doc["types"]
    types.append({"k": "error_set", "errors": ["Oops"], "abi_size": 2, "abi_align": 2})
    node = next(t for t in types if t.get("name") == "heap.ArenaAllocator.Node")
    next(f for f in node["fields"] if f["name"] == "end_index")["ty"] = len(types) - 1
    base.reject(binary, mutated, CYCLIC, "arena.")

    # An `unordered` load of a `bool` (an atomic type, but neither an integer, a packed struct nor
    # a pointer) stays rejected.
    mutated, doc = edit(linux, "heap.ArenaAllocator.Node.endResize.json")
    types = doc["types"]
    types.append({"k": "bool", "abi_size": 1, "abi_align": 1})
    bool_ty = len(types) - 1
    insts = {i["id"]: i for i in base.walk(doc["body"])}
    hit = False
    for inst in base.walk(doc["body"]):
        if inst.get("tag") == "atomic_load" and inst.get("order") == "unordered":
            operand = insts[inst["args"][0]["inst"]]
            # The operand's pointer type, retargeted to the `bool`.
            types.append(dict(types[operand["ty"]], child=bool_ty))
            operand["ty"] = len(types) - 1
            inst["ty"] = bool_ty
            hit = True
    assert hit
    base.reject(binary, mutated, "an `unordered` load of a type other than an integer, a packed "
                "struct or a pointer is outside the subset", "arena.")
    print("alloc-arena CLI regressions passed")


if __name__ == "__main__":
    main(Path(sys.argv[1]))
