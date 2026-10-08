#!/usr/bin/env python3
"""T02: exercise a previously built translator on the retained wasm32/x86_64 AIR.

Accepts the real wasm32 exports with the 32-bit model, checks that the layout checker
uses the profile's pointer width (an exporter size of the other width is rejected), that
a 32-bit translation names only width-parameterized runtime terms, and that the
operations which are not width-parameterized are rejected with a reason. Never builds
or runs a compiler.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
AIR = HERE / "air" / "0.16.0"
TARGETS = ("wasm32-freestanding", "wasm32-wasi", "x86_64-linux")


def load(target):
    return {p.name: json.loads(p.read_text()) for p in sorted((AIR / target).glob("*.json"))}


def run(binary, documents, error=None):
    with tempfile.TemporaryDirectory(prefix="air2lean-pointer-width-") as directory:
        directory = Path(directory)
        air = directory / "air"
        air.mkdir()
        for name, doc in documents.items():
            (air / name).write_text(json.dumps(doc))
        out = directory / "out.lean"
        out.write_text("sentinel\n")
        result = subprocess.run([str(binary), str(air), "-o", str(out), "--namespace", "PW",
                                 "--prefix", "pointer_width."], text=True, capture_output=True, check=False)
        if error is not None:
            assert result.returncode != 0, (error, result.stdout)
            assert error in result.stderr, (error, result.stderr)
            assert out.read_text() == "sentinel\n", "a rejection overwrote the previous output"
            return None
        assert result.returncode == 0, result.stderr
        return out.read_text()


def one(docs, name):
    return {name: copy.deepcopy(docs[name])}


def main():
    binary = Path(sys.argv[1]).resolve(strict=True)
    checks = 0
    for target in TARGETS:
        docs = load(target)
        wasm = target.startswith("wasm32")
        bits = 32 if wasm else 64
        assert all(d["profile"]["pointer_bits"] == bits for d in docs.values()), target
        text = run(binary, docs)
        header = json.loads(text.splitlines()[0].removeprefix("-- air2lean-profile: "))
        assert header["profile"]["pointer_bits"] == bits
        assert header["profile"]["target_triple"].startswith(target.replace("-linux", "-linux."))
        if wasm:
            assert "open scoped Zig.Wasm32" in text
            for term in ("Zig.Slice32", "Zig.Allocator.allocOf .w32", "Zig.Allocator.freeOf",
                         "Zig.ptrAddrOf .w32", "Zig.memsetOf", "Zig.memmoveOf", ".elemOf",
                         "Zig.indexOf", "(4 : BitVec 32)"):
                assert term in text, (target, term)
            for term in ("Zig.Slice ", "Zig.Slice)", "BitVec 64", "Zig.Allocator.alloc ", ".elem "):
                assert term not in text, (target, term)
        else:
            assert "Zig.Wasm32" not in text and "Zig.Slice32" not in text and "Of " not in text
            assert "Zig.Allocator.alloc " in text and "BitVec 64" in text
        checks += 1

        # The model's pointer size comes from the profile, not from the exporter: an
        # exported layout of the other width is rejected.
        other = 8 if wasm else 4
        bad = one(docs, "pointer_width.restLen.json")
        doc = bad["pointer_width.restLen.json"]
        for ty in doc["types"]:
            if ty.get("k") == "ptr":
                ty["abi_size"] = 2 * other if ty["size"] == "slice" else other
                ty["abi_align"] = other
            if ty.get("k") == "struct" and ty.get("name") == "pointer_width.View":
                ty["abi_size"] = 3 * other
                ty["abi_align"] = other
                ty["fields"][1]["offset"] = other
        run(binary, bad, error="the memory model gives type")
        checks += 1

        # `pointer_bits` must be the triple's own width.
        bad = one(docs, "pointer_width.succ.json")
        bad["pointer_width.succ.json"]["profile"]["pointer_bits"] = 64 if wasm else 32
        run(binary, bad, error="pointer width")
        checks += 1

    # Real wasm32 exports of operations that stay 64-bit only (`reject.zig`).
    rejects = load("wasm32-reject")
    for name, error in [
        ("reject.atomicRead.json", "an atomic op is outside the 32-bit pointer model"),
        ("reject.colorName.json", "`@tagName` is outside the 32-bit pointer model"),
        ("reject.copyOf.json", "is outside the 32-bit pointer model (only create, alloc"),
    ]:
        run(binary, one(rejects, name), error=error)
        checks += 1

    print(f"pointer-width CLI checks passed ({checks})")


if __name__ == "__main__":
    main()
