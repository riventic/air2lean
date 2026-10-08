#!/usr/bin/env python3
"""Fill an `air2lean --model-registry-template` with the ZigLean.Env.Linux bindings (ENV-03).

usage: fill_registry.py TEMPLATE.json OUTPUT.json
Only os.linux.read/write/close are bound; any other missing symbol is an error.
"""
import json
import sys

sys.dont_write_bytecode = True

# symbol: (implementation, contract, evidence, safety errors, footprint)
BINDINGS = {
    "os.linux.close": ("close", "closeContract", "closeEvidence", ["illegal"], None),
    "os.linux.write": ("write", "writeContract", "writeEvidence", ["illegal", "unspecified"],
                       {"reads": [1], "writes": []}),
    "os.linux.read": ("read", "readContract", "readEvidence", ["illegal"],
                      {"reads": [], "writes": [1]}),
}


def fill(template: dict) -> dict:
    models = []
    for entry in template["models"]:
        symbol = entry["symbol"]
        if symbol not in BINDINGS:
            raise SystemExit(f"fill_registry: no ENV-03 binding for {symbol}")
        impl, contract, proof, errors, footprint = BINDINGS[symbol]
        entry = dict(entry, **{
            "import": "ZigLean.Env.Linux",
            "implementation": f"Zig.Env.Linux.{impl}",
            "contract": f"Zig.Env.Linux.{contract}",
            "trust": "proved",
            "proof": f"Zig.Env.Linux.{proof}",
            "termination": "total",
            "errors": errors,
            "effects": "tracked",
            "dependencies": [],
        })
        if footprint is not None:
            entry["footprint"] = footprint
        models.append(entry)
    return {"schema": template["schema"], "models": models}


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    with open(sys.argv[1]) as stream:
        registry = fill(json.load(stream))
    with open(sys.argv[2], "w") as stream:
        json.dump(registry, stream, indent=1, sort_keys=True)
        stream.write("\n")
