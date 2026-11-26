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
import re
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
TARGETS = ("wasm32-freestanding", "wasm32-wasi", "x86_64-linux")
# The AIR directories of pointer_width.zig and reject.zig per exported Zig version (0.16.0 by
# check.sh --export, 0.17.1 by exports.json).
POINTER_WIDTH = {"0.16.0": "{target}", "0.17.1": "pointer_width/{target}"}
REJECT = {"0.16.0": "wasm32-reject", "0.17.1": "reject/wasm32-freestanding"}


def load(target, version="0.16.0"):
    return {p.name: json.loads(p.read_text()) for p in sorted((HERE / "air" / version / target).glob("*.json"))}


def run(binary, documents, error=None, prefix="pointer_width."):
    with tempfile.TemporaryDirectory(prefix="air2lean-pointer-width-") as directory:
        directory = Path(directory)
        air = directory / "air"
        air.mkdir()
        for name, doc in documents.items():
            (air / name).write_text(json.dumps(doc))
        out = directory / "out.lean"
        out.write_text("sentinel\n")
        result = subprocess.run([str(binary), str(air), "-o", str(out), "--namespace", "PW",
                                 "--prefix", prefix], text=True, capture_output=True, check=False)
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
    for version, target in [(v, t) for v in POINTER_WIDTH for t in TARGETS]:
        docs = load(POINTER_WIDTH[version].format(target=target), version)
        wasm = target.startswith("wasm32")
        bits = 32 if wasm else 64
        assert all(d["profile"]["pointer_bits"] == bits for d in docs.values()), (version, target)
        text = run(binary, docs)
        header = json.loads(text.splitlines()[0].removeprefix("-- air2lean-profile: "))
        assert header["profile"]["zig_version"] == version, (version, target)
        assert header["profile"]["pointer_bits"] == bits
        assert header["profile"]["target_triple"].startswith(target.replace("-linux", "-linux."))
        if wasm:
            assert "open scoped Zig.Wasm32" in text
            for term in ("Zig.Slice32", "Zig.Allocator.allocOf .w32", "Zig.Allocator.freeOf",
                         "Zig.ptrAddrOf .w32", "Zig.memsetOf", "Zig.memcpyOf", ".elemOf",
                         "Zig.indexOf", "(4 : BitVec 32)"):
                assert term in text, (target, term)
            for term in ("Zig.Slice ", "Zig.Slice)", "BitVec 64", "Zig.Allocator.alloc ", ".elem "):
                assert term not in text, (target, term)
        else:
            for term in ("Zig.Wasm32", "Zig.Slice32", "allocOf", "freeOf", "elemOf", "indexOf",
                         "lenOf", "memsetOf", "memmoveOf", "ptrAddrOf"):
                assert term not in text, (target, term)
            assert "Zig.Allocator.alloc " in text and "BitVec 64" in text
        checks += 1

        # The model's pointer size comes from the profile, not from the exporter: an
        # exported layout of the other width is rejected.
        other = 8 if wasm else 4
        bad = one(docs, "pointer_width.setFirst.json")
        doc = bad["pointer_width.setFirst.json"]
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

    # `@tagName` and `@errorName` (names.zig, every exported version): the name is a slice of the
    # profile's width; a 32-bit translation names no 64-bit slice.
    for version in sorted(p.name for p in (HERE / "air").iterdir() if (p / "names").is_dir()):
        for target in TARGETS:
            wasm = target.startswith("wasm32")
            text = run(binary, load(f"names/{target}", version), prefix="names.")
            slice_ty = "Zig.Slice32" if wasm else "Zig.Slice"
            for term in (f"def Color.tagName (e : Color) : Zig.Result {slice_ty} :=",
                         f"def Level.tagName (e : Level) : Zig.Result {slice_ty} :=",
                         f"def errorNameOf (e : Zig.ErrName) : Zig.Result {slice_ty} :="):
                assert term in text, (version, target, term)
            if wasm:
                assert not re.search(r"\bZig\.Slice\b", text), (version, target)
            checks += 1

    # The C integer types (c_ints.zig, every exported version): `c_long`, `c_ulong` and `isize`
    # take the profile's pointer width, the fixed-width C types keep theirs on every target, and
    # `long double` is `f128` on wasm32 and `f80` on x86_64.
    for version in sorted(p.name for p in (HERE / "air").iterdir() if (p / "c_ints").is_dir()):
        for target in TARGETS:
            wasm = target.startswith("wasm32")
            bits = 32 if wasm else 64
            docs = load(f"c_ints/{target}", version)
            text = run(binary, docs, prefix="c_ints.")
            for term in (f"def longSucc (p0 : BitVec {bits}) : Zig.Result (BitVec {bits})",
                         f"def ulongSucc (p0 : BitVec {bits}) : Zig.Result (BitVec {bits})",
                         f"def isizeSucc (p0 : BitVec {bits}) : Zig.Result (BitVec {bits})",
                         f"def longToInt (p0 : BitVec {bits}) : Zig.Result (BitVec 32)",
                         "def charSucc (p0 : BitVec 8) : Zig.Result (BitVec 8)",
                         "def ushortSucc (p0 : BitVec 16) : Zig.Result (BitVec 16)",
                         "def uintSucc (p0 : BitVec 32) : Zig.Result (BitVec 32)",
                         "def longlongSucc (p0 : BitVec 64) : Zig.Result (BitVec 64)",
                         "  ll : BitVec 64\n",
                         f"  size := {24 if wasm else 32}\n  align := 8\n",
                         f"  v : Zig.{'F128' if wasm else 'F80'}\n",
                         "Zig.Enc.fields 32 [(0, Zig.Enc.encode v.tag), (16, Zig.Enc.encode v.v)]"):
                assert term in text, (version, target, term)
            checks += 1

            # A `long long` loaded with the i386 System V alignment (4) is rejected: the model's
            # 64-bit integers are 8-aligned on every profile, wasm32 included.
            bad = one(docs, "c_ints.mixedLl.json")
            for ty in bad["c_ints.mixedLl.json"]["types"]:
                if ty.get("k") == "int" and ty["bits"] == 64:
                    ty["abi_align"] = 4
            run(binary, bad, error="the memory model gives type", prefix="c_ints.")
            checks += 1

    # `extern` struct and union layouts (layouts.zig, every exported version and target): the
    # compiler's layouts pass the C layout rule, also with explicit field alignments, and a
    # changed type table does not: fields out of declaration order, a size that is not the
    # rounded-up end, an alignment that is no power of two, and a field type whose model layout
    # is not the exporter's although the function never loads that field.
    def named(doc, name):
        return next(t for t in doc["types"] if t.get("name") == name)

    def swap(doc):
        fields = named(doc, "layouts.Plain")["fields"]
        fields[1]["offset"], fields[2]["offset"] = fields[2]["offset"], fields[1]["offset"]

    def grow(name):
        def change(doc):
            entry = named(doc, name)
            entry["abi_size"] += entry["abi_align"]
        return change

    def odd_align(doc):
        named(doc, "layouts.Under")["abi_align"] = 3

    def unloaded_field(doc):
        # `n: c_long` of `Plain`: `plainT` loads only `t`.
        entry = doc["types"][named(doc, "layouts.Plain")["fields"][2]["ty"]]
        entry["abi_align"] //= 2

    not_c = "is not a C layout: "
    layout_cases = [
        ("layouts.plainN.json", swap, "`extern` struct 'layouts.Plain' " + not_c + "a field at offset"),
        ("layouts.plainN.json", grow("layouts.Plain"), "`extern` struct 'layouts.Plain' " + not_c + "its size"),
        ("layouts.underC.json", odd_align, "`extern` struct 'layouts.Under' " + not_c + "its alignment 3"),
        ("layouts.eitherB.json", grow("layouts.Either"), "`extern` union 'layouts.Either' " + not_c + "its size"),
        ("layouts.plainT.json", unloaded_field, ", a field of struct 'layouts.Plain', size"),
    ]
    for version in sorted(p.name for p in (HERE / "air").iterdir() if (p / "layouts").is_dir()):
        for target in TARGETS:
            if not (HERE / "air" / version / "layouts" / target).is_dir():
                continue
            docs = load(f"layouts/{target}", version)
            run(binary, docs, prefix="layouts.")
            checks += 1
            for name, change, error in layout_cases:
                bad = one(docs, name)
                change(bad[name])
                run(binary, bad, error=error, prefix="layouts.")
                checks += 1

    # Real wasm32 exports of operations that stay 64-bit only (`reject.zig`), every version.
    for version, directory in REJECT.items():
        rejects = load(directory, version)
        for name, error in [
            ("reject.atomicRead.json", "an atomic op is outside the 32-bit pointer model"),
            ("reject.copyOf.json", "is outside the 32-bit pointer model (only create, alloc"),
        ]:
            run(binary, one(rejects, name), error=error)
            checks += 1

    print(f"pointer-width CLI checks passed ({checks})")


if __name__ == "__main__":
    main()
