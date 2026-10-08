#!/usr/bin/env python3
"""Representation casts the translator must reject through the CLI, each with its diagnostic.

Pointer-bearing repr casts fail closed: the model's pointer bytes carry provenance and are
not integer bits, so `@bitCast([1]*u32 -> u64)` could not give Zig's address.

usage: negatives.py TRANSLATOR
"""
import copy
import json
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
MESSAGE = "representation `@bitCast` involving a pointer"
PTR = {"k": "ptr", "size": "one", "const": False, "child": 0, "ptr_align": 4, "volatile": False,
       "allowzero": False, "sentinel": False, "host_size": 0, "abi_size": 8, "abi_align": 8}


def cast_to_u64(source):
    """`pairToU64` (an extern pair to u64) with its source replaced by `source(types)`'s type."""
    doc = copy.deepcopy(json.loads((HERE / "air/0.16.0/aggregate_casts.pairToU64.json").read_text()))
    src = source(doc["types"])
    doc["params"] = [src]
    doc["body"][0]["ty"] = src
    return doc


def pointer_array(types):
    types.append(dict(PTR))
    types.append({"k": "array", "len": 1, "child": len(types) - 1, "sentinel": False,
                  "abi_size": 8, "abi_align": 8})
    return len(types) - 1


def optional_pointer_field(types):
    types.append(dict(PTR))
    types.append({"k": "optional", "child": len(types) - 1, "abi_size": 8, "abi_align": 8})
    types.append({"k": "struct", "name": "aggregate_casts.Opt", "layout": "extern",
                  "fields": [{"name": "p", "ty": len(types) - 1, "offset": 0}],
                  "abi_size": 8, "abi_align": 8})
    return len(types) - 1


CASES = {"[1]*u32 -> u64": cast_to_u64(pointer_array),
         "extern struct { p: ?*u32 } -> u64": cast_to_u64(optional_pointer_field)}


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    for name, doc in CASES.items():
        with tempfile.TemporaryDirectory(prefix="air2lean-aggregate-casts-") as temp:
            air = Path(temp) / "air"
            air.mkdir()
            (air / f"{doc['name']}.json").write_text(json.dumps(doc))
            out = Path(temp) / "Gen.lean"
            result = subprocess.run([sys.argv[1], str(air), "-o", str(out), "--namespace",
                                     "AggregateCastsNegative", "--prefix", "aggregate_casts."],
                                    capture_output=True, text=True, timeout=300)
            output = result.stdout + result.stderr
            if result.returncode == 0 or MESSAGE not in output:
                raise SystemExit(f"{name}: expected rejection containing {MESSAGE!r}, "
                                 f"got exit {result.returncode}: {output[-2000:]}")
            if out.exists():
                raise SystemExit(f"{name}: a rejected cast wrote Gen.lean")
    print(f"aggregate-casts CLI negatives rejected: {len(CASES)}")


if __name__ == "__main__":
    main()
