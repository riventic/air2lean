#!/usr/bin/env python3
"""CLI regressions for nested constant pointer bases (L06), for a root-built translator.

Nested constant pointers (elements of payloads of fields of a global, constant slices whose
pointer is such a base) translate to the global's block and the exact total offset. Unbacked,
comptime-only, unknown and out-of-object provenance stay explicit errors, and the LLVM backend's
misplaced `eu_payload` constants are rejected on the `stage2_llvm` profile. Never builds or
invokes compilers: air/0.16.0 is hand-written AIR in the exporter's schema.
"""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
AIR = HERE / "air" / "0.16.0"
FRESH_ROOT = HERE / "air-fresh"
VERSIONS = ["0.16.0", "0.15.2", "0.14.1"]
CONSTANTS = ["resElemPtr", "maybeElemPtr", "maybeBytePtr", "maybeSlice", "resCodePtr"]
GEN = HERE / "ConstBases" / "Gen.lean"
ARGS = ["--namespace", "ConstBases", "--prefix", "const_bases."]
UNBACKED = "a pointer constant without a global ({}) is outside the subset"
LLVM = "such constants are outside the stage2_llvm profile"
LEGACY = "outside the unverified profile (a legacy profile names no backend, so the LLVM backend cannot be excluded)"


def fixtures(directory=AIR):
    return {p.name: json.loads(p.read_text()) for p in sorted(directory.glob("*.json"))}


def pointers(value):
    """Every global pointer constant in an AIR body, in order."""
    if isinstance(value, dict):
        if isinstance(value.get("ptr"), dict) and "global" in value["ptr"]:
            yield value["ptr"]
        for child in value.values():
            yield from pointers(child)
    elif isinstance(value, list):
        for child in value:
            yield from pointers(child)


def definition(text, name):
    """The generated definition of `name`: its Locals structure through its body."""
    start = text.index(f"structure {name}Locals where")
    end = text.find("\nstructure ", start + 1)
    return text[start:] if end < 0 else text[start:end]


def translate(binary, documents, directory):
    air = directory / "air"
    air.mkdir()
    for name, document in documents.items():
        (air / name).write_text(json.dumps(document))
    out = directory / "Gen.lean"
    out.write_text("sentinel\n")
    result = subprocess.run([str(binary), str(air), "-o", str(out), *ARGS], text=True,
                            capture_output=True, check=False, timeout=60)
    return result, out


def accept(binary, documents):
    with tempfile.TemporaryDirectory(prefix="air2lean-const-bases-") as d:
        result, out = translate(binary, documents, Path(d))
        assert result.returncode == 0, result.stderr
        return out.read_text()


def reject(binary, documents, marker, code="CONSTANT_FAILURE", cli=True):
    """CLI rejection (with `marker` unless `cli` is false: an earlier check may fail first);
    `--diagnostics-json` reports `marker` under `code`."""
    with tempfile.TemporaryDirectory(prefix="air2lean-const-bases-") as d:
        result, out = translate(binary, documents, Path(d))
        assert result.returncode == 1, (marker, result.returncode, result.stderr)
        assert not cli or marker in result.stderr, (marker, result.stderr)
        assert out.read_text() == "sentinel\n", "a rejected input replaced the output"
        diagnostics = subprocess.run([str(binary), "--diagnostics-json", str(Path(d) / "air")],
                                     text=True, capture_output=True, check=False, timeout=60)
        assert diagnostics.returncode == 1, diagnostics.stderr
        report = json.loads(diagnostics.stdout)
        hits = [e for e in report["diagnostics"] if marker in e["message"]]
        assert hits and all(e["code"] == code for e in hits), (marker, code, hits)
    return 1


def program(edit=None, name=None):
    """Every fixture; `edit(document)` applied to `name` (or to every document)."""
    documents = copy.deepcopy(fixtures())
    if edit:
        for key, document in documents.items():
            if name is None or key == name:
                edit(document)
    return documents


def ret_value(document):
    return document["body"][-1]["args"][0]


def llvm(document):
    document["profile"]["backend"] = "stage2_llvm"


def legacy(document):
    """A schema 1-11 file: no profile, so no backend (`unverified`)."""
    document["schema"] = 11
    document.pop("profile", None)


def main():
    binary = Path(sys.argv[1] if len(sys.argv) > 1 else HERE.parents[2] / ".lake/build/bin/air2lean")
    checks = 0

    # Positive: the retained translation, byte-identical; each nested base is block 0 plus
    # the total offset, never a fresh block.
    text = accept(binary, fixtures())
    assert text == GEN.read_text(), "fresh translation differs from ConstBases/Gen.lean"
    for function, value in [("resElemPtr", "(⟨some 0, 24⟩ : Zig.Ptr)"),
                            ("maybeElemPtr", "(⟨some 0, 15⟩ : Zig.Ptr)"),
                            ("maybeBytePtr", "(⟨some 0, 15⟩ : Zig.Ptr)"),
                            ("maybeSlice", "(⟨(⟨some 0, 15⟩ : Zig.Ptr), (2 : BitVec 64)⟩ : Zig.Slice)"),
                            ("resCodePtr", "(⟨some 0, 20⟩ : Zig.Ptr)")]:
        assert f"def {function}  : Zig.MemM" in text and f"pure (.ret {value})" in text, function
    assert "Zig.load (BitVec 8) 1 (⟨some 0, 24⟩ : Zig.Ptr)" in text
    assert text.count("Zig.Mem.ofGlobals [") == 1 and "-- 1:" not in text, "a block was invented"
    checks += 1

    # Unbacked: `@ptrFromInt(0x1000)` as a direct pointer, nested in a constant slice, and as
    # the initial value of a global that a constant points into.
    def fixed(d):
        ret_value(d)["ptr"] = {"unsupported": "int", "off": 4096}
    checks += reject(binary, program(fixed, "const_bases.resElemPtr.json"), UNBACKED.format("int"))

    def fixed_slice(d):
        ret_value(d)["slice_ptr"]["ptr"] = {"unsupported": "int", "off": 4096}
    checks += reject(binary, program(fixed_slice, "const_bases.maybeSlice.json"), UNBACKED.format("int"))

    def fixed_global(d):
        holder = len(d["types"])
        d["types"].append(dict(d["types"][11], child=11))
        d["globals"].append({"name": "const_bases.fixed", "ty": 11, "const": True,
                             "threadlocal": False, "extern": False,
                             "init": {"ty": 11, "ptr": {"unsupported": "int", "off": 4096}}})
        d["ret"] = holder
        d["body"][-1]["args"] = [{"ty": holder, "ptr": {"global": 1, "off": 0}}]
    checks += reject(binary, program(fixed_global, "const_bases.resCodePtr.json"),
                     "global const_bases.fixed: " + UNBACKED.format("int"), "GLOBAL_FAILURE")

    # Comptime-only and exporter-unbacked bases stay explicit errors with their reason.
    for reason in ["comptime_alloc", "comptime_field", "arr_elem", "payload_unbacked"]:
        def comptime(d, reason=reason):
            ret_value(d)["ptr"] = {"unsupported": reason, "off": 0}
        checks += reject(binary, program(comptime, "const_bases.maybeElemPtr.json"),
                         UNBACKED.format(reason))

    # Invalid provenance: an unknown global, and an offset past the object's end.
    def unknown(d):
        ret_value(d)["ptr"]["global"] = 5
    checks += reject(binary, program(unknown, "const_bases.resElemPtr.json"), "pointer has unknown global id 5",
                     "STRUCTURE_FAILURE", cli=False)

    def past(d):
        ret_value(d)["ptr"]["off"] = 33
    checks += reject(binary, program(past, "const_bases.resCodePtr.json"),
                     "a pointer constant at offset 33 is outside global 0 (32 bytes)",
                     "STRUCTURE_FAILURE")

    def past_slice(d):
        ret_value(d)["slice_ptr"]["ptr"]["off"] = 40
    checks += reject(binary, program(past_slice, "const_bases.maybeSlice.json"),
                     "a pointer constant at offset 40 is outside global 0 (32 bytes)",
                     "STRUCTURE_FAILURE")

    # LLVM: every constant into the alignment-1 `Failure![3]u8` payload (offsets 22..25, one
    # past its end included) is rejected on stage2_llvm; the same program is accepted on
    # stage2_x86_64 (above). `resCodePtr` is retargeted to each offset.
    misplaced = ("const_bases.resElemPtr.json", "const_bases.readResElem.json")

    def retarget(off):
        def edit(d):
            llvm(d)
            if d["name"] == "const_bases.resCodePtr":
                ret_value(d)["ptr"]["off"] = off
        return {k: v for k, v in program(edit).items() if k not in misplaced}

    checks += reject(binary, program(llvm), "offset 24 of global 0 may address")
    checks += reject(binary, program(llvm), LLVM)
    # The wasm backend's `lowerPtr` has the same `eu_payload` measure (codegen/wasm/CodeGen.zig).
    def wasm(d):
        d["profile"]["backend"] = "stage2_wasm"
    checks += reject(binary, program(wasm), "such constants are outside the stage2_wasm profile")
    for off in (22, 25):
        checks += reject(binary, retarget(off), f"offset {off} of global 0 may address")

    # Controls on stage2_llvm: the error union itself (20) and its code (21), the optional
    # payload's nested element and slice (15), other fields, and runtime projections.
    llvm_text = accept(binary, {k: v for k, v in program(llvm).items() if k not in misplaced})
    assert "(⟨some 0, 20⟩ : Zig.Ptr)" in llvm_text and "(⟨some 0, 15⟩ : Zig.Ptr)" in llvm_text
    for off in (8, 20, 21, 26):
        accept(binary, retarget(off))
    checks += 1

    # An aligned (`Failure!u16`) payload starts at 0 on every backend: offsets 20 (payload)
    # and 22 (code) are accepted on stage2_llvm.
    for off in (20, 22):
        def aligned(d, off=off):
            llvm(d)
            d["types"][9]["payload"] = 1
            d["types"][9]["abi_size"] = 4
            if "globals" in d:
                d["globals"][0]["init"]["elems"][2] = {"ty": 9, "payload": {"ty": 1, "val": "7"}}
            if d["name"] == "const_bases.resCodePtr":
                ret_value(d)["ptr"]["off"] = off
        accept(binary, {k: v for k, v in program(aligned).items() if k in (
            "const_bases.resCodePtr.json", "const_bases.maybeElemPtr.json")})
    checks += 1

    # Legacy schema 1-11: no profile, so the backend that compiled the program is unknown and
    # the LLVM backend cannot be excluded. The same constants are rejected as on stage2_llvm,
    # with the same controls accepted, and the rejection says why.
    checks += reject(binary, program(legacy), "offset 24 of global 0 may address")
    checks += reject(binary, program(legacy), LEGACY)

    def legacy_retarget(off):
        def edit(d):
            legacy(d)
            if d["name"] == "const_bases.resCodePtr":
                ret_value(d)["ptr"]["off"] = off
        return {k: v for k, v in program(edit).items() if k not in misplaced}

    for off in (22, 25):
        checks += reject(binary, legacy_retarget(off), f"offset {off} of global 0 may address")
    legacy_text = accept(binary, {k: v for k, v in program(legacy).items() if k not in misplaced})
    assert "(⟨some 0, 15⟩ : Zig.Ptr)" in legacy_text and '"backend":"unverified"' in legacy_text
    for off in (8, 20, 21, 26):
        accept(binary, legacy_retarget(off))
    checks += 1
    # An aligned (`Failure!u16`) payload starts at 0 on every backend, legacy included.
    for off in (20, 22):
        def legacy_aligned(d, off=off):
            legacy(d)
            d["types"][9]["payload"] = 1
            d["types"][9]["abi_size"] = 4
            if "globals" in d:
                d["globals"][0]["init"]["elems"][2] = {"ty": 9, "payload": {"ty": 1, "val": "7"}}
            if d["name"] == "const_bases.resCodePtr":
                ret_value(d)["ptr"]["off"] = off
        accept(binary, {k: v for k, v in program(legacy_aligned).items() if k in (
            "const_bases.resCodePtr.json", "const_bases.maybeElemPtr.json")})
    checks += 1

    # Fresh exports (patched 0.16.0, 0.15.2 and 0.14.1 compilers, stage2_x86_64 x86_64-linux-musl
    # baseline ReleaseSafe; README §Fresh export). Each returned constant has the hand-written
    # global, offset and payload marker, and its generated definition is identical. Sema's
    # ReleaseSafe safety checks in the runtime projections and its folded read are the recorded
    # differences. The three versions translate to the same program but for the profile header.
    hand = fixtures()
    provenance = json.loads((HERE / "provenance.json").read_text())
    assert sorted(provenance["air_sha256"]) == sorted(
        f"{v}/{n}" for v in VERSIONS for n in fixtures(FRESH_ROOT / v)), "provenance lists other files"
    texts = {}
    for version in VERSIONS:
        fresh = fixtures(FRESH_ROOT / version)
        assert sorted(fresh) == sorted(hand), version
        for name, document in fresh.items():
            digest = hashlib.sha256((FRESH_ROOT / version / name).read_bytes()).hexdigest()
            assert provenance["air_sha256"][f"{version}/{name}"] == digest, (version, name)
            assert document["zig_version"] == version and document["profile"]["zig_version"] == version
            assert document["profile"]["backend"] == "stage2_x86_64", (version, name)
        for name in CONSTANTS:
            key = f"const_bases.{name}.json"
            mine = list(pointers(hand[key]["body"]))
            theirs = list(pointers(fresh[key]["body"]))
            assert theirs and theirs[-1] == mine[-1], (version, name, theirs, mine)
            assert fresh[key]["globals"][0]["name"] == "const_bases.table", (version, name)
            ignored = ("zig_version", "target_triple")
            assert {k: v for k, v in fresh[key]["profile"].items() if k not in ignored} == \
                {k: v for k, v in hand[key]["profile"].items() if k not in ignored}, (version, name)
        texts[version] = accept(binary, fresh)
        for name in CONSTANTS:
            assert definition(texts[version], name) == definition(text, name), (version, name)
        assert "pure (.ret (22 : BitVec 8))" in definition(texts[version], "readResElem"), version
        checks += reject(binary, {k: dict(v, profile=dict(v["profile"], backend="stage2_llvm"))
                                  for k, v in fresh.items()}, "offset 24 of global 0 may address")
        downgraded = copy.deepcopy(fresh)
        for document in downgraded.values():
            legacy(document)
        checks += reject(binary, downgraded, "offset 24 of global 0 may address")
    bodies = {v: t.split("\n", 1)[1] for v, t in texts.items()}
    assert len(set(bodies.values())) == 1, "the versions' fresh translations differ beyond the profile header"
    checks += 1

    print(f"{checks} constant-pointer-base CLI checks passed")


if __name__ == "__main__":
    main()
