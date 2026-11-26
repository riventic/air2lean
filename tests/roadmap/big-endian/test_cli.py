#!/usr/bin/env python3
"""T03: exercise a previously built translator on the retained s390x/x86_64 AIR.

Accepts the real s390x-linux export as the big-endian model profile `abi64-be-v1` (and only
with the `Zig.BigEndian` instances and `.big` bit-pointer accesses), keeps x86_64 on
`abi64-le-v1` without them, rejects contradictory endian metadata, and rejects every real
s390x export of `reject.zig` with its reason (`vecLanes` from Zig 0.17.1 on: its 0.16.0 export
has no lane pointer and translates). A rejection leaves the previous output intact.
Never builds or runs a compiler.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def exported_versions():
    """Every Zig version `exports.json` exports `big_endian.zig` and `reject.zig` for (one set)."""
    entries = json.loads((HERE / "exports.json").read_text())["exports"]
    sets = {tuple(e["versions"]) for e in entries if e["source"] in ("big_endian.zig", "reject.zig")}
    if len(sets) != 1:
        raise SystemExit(f"exports.json: big_endian.zig and reject.zig differ in their versions: {sets}")
    return sets.pop()


VERSIONS = exported_versions()


def load(version, target):
    air = HERE / "air" / version / target
    return {p.name: json.loads(p.read_text()) for p in sorted(air.glob("*.json"))}


def run(binary, documents, error=None, prefix="big_endian.", extra=()):
    with tempfile.TemporaryDirectory(prefix="air2lean-big-endian-") as directory:
        directory = Path(directory)
        air = directory / "air"
        air.mkdir()
        for name, doc in documents.items():
            (air / name).write_text(json.dumps(doc))
        out = directory / "out.lean"
        out.write_text("sentinel\n")
        result = subprocess.run([str(binary), str(air), "-o", str(out), "--namespace", "BE",
                                 "--prefix", prefix, *extra],
                                text=True, capture_output=True, check=False)
        if error is not None:
            assert result.returncode != 0, (error, result.stdout)
            assert error in result.stderr, (error, result.stderr)
            assert out.read_text() == "sentinel\n", "a rejection overwrote previous output"
            return None
        assert result.returncode == 0, result.stderr
        return out.read_text()


def one(docs, name):
    return {name: copy.deepcopy(docs[name])}


def main():
    binary = Path(sys.argv[1]).resolve(strict=True)
    for version in VERSIONS:
        checks = check_version(binary, version)
        print(f"big-endian CLI checks passed on {version} ({checks})")


def check_version(binary, version):
    checks = 0
    big, little = load(version, "s390x-linux"), load(version, "x86_64-linux")
    text = run(binary, big, extra=("--profile", "abi64-be-v1"))
    header = json.loads(text.splitlines()[0].removeprefix("-- air2lean-profile: "))
    assert header["profile"]["name"] == "abi64-be-v1" and header["profile"]["endian"] == "big"
    assert "open scoped Zig.BigEndian" in text
    assert "Zig.loadBitsOf .big" in text and "Zig.storeBitsOf .big" in text
    assert "Zig.loadBits (" not in text and "Zig.storeBits (" not in text
    checks += 1
    text = run(binary, little, extra=("--profile", "abi64-le-v1"))
    assert "Zig.BigEndian" not in text and "Of .big" not in text
    checks += 1
    # The big-endian profile is not the little-endian one.
    run(binary, big, error="differs from input profile", extra=("--profile", "abi64-le-v1"))
    run(binary, little, error="differs from input profile", extra=("--profile", "abi64-be-v1"))
    checks += 2
    # Mixed byte orders in one translation.
    mixed = one(big, "big_endian.u32ToBytes.json")
    mixed.update(one(little, "big_endian.bytesToU32.json"))
    run(binary, mixed, error="mixed AIR profiles")
    checks += 1
    # Endian metadata must be the triple's own byte order, and agree with `target_endian`.
    name = "big_endian.u32ToBytes.json"
    for target_docs, field, value, error in [
        (big, "endian", "little", "big-endian byte order"),
        (little, "endian", "big", "little-endian byte order"),
        (big, "target_triple", "x86_64-linux.5.10...6.19-musl", "little-endian byte order"),
        (big, "target_triple", "powerpc64-linux-musl", "model ABI scope"),
        (big, "endian", "middle", "little/big-endian memory model"),
        (big, "backend", "stage2_c", "outside the big-endian model (stage2_llvm only)"),
        # The exporter names the profile by its byte order; the translator never renames it.
        (big, "name", "abi64-le-v1", "unsupported profile 'abi64-le-v1' (want 'abi64-be-v1')"),
        (little, "name", "abi64-be-v1", "unsupported profile 'abi64-be-v1' (want 'abi64-le-v1')"),
    ]:
        bad = one(target_docs, name)
        bad[name]["profile"][field] = value
        run(binary, bad, error=error)
        checks += 1
    bad = one(big, name)
    bad[name]["target_endian"] = "little"
    run(binary, bad, error="target_endian differs from profile.endian")
    checks += 1
    # A legacy schema cannot carry big-endian metadata.
    bad = one(big, name)
    bad[name]["schema"] = 11
    del bad[name]["profile"]
    run(binary, bad, error="outside the little-endian memory model")
    checks += 1
    # `@tagName`/`@errorName` are admitted on the 64-bit big-endian and the 32-bit little-endian
    # models (T02); no 32-bit big-endian target is qualified, so a profile that declares one is
    # rejected before any name slice is emitted (`BuildProfile.collect`).
    names = load(version, "names/s390x-linux")
    name = "names.colorName.json"
    assert "Color.tagName" in run(binary, one(names, name), prefix="names.")
    for fields, error in [
        ({"pointer_bits": 32}, "differs from the s390x target's 64-bit pointer width"),
        ({"pointer_bits": 32, "target_triple": "mips-linux-musl"}, "model ABI scope"),
        ({"pointer_bits": 32, "target_triple": "powerpc-linux-musl"}, "model ABI scope"),
        ({"pointer_bits": 32, "target_triple": "wasm32-wasi-musl"}, "byte order"),
    ]:
        bad = one(names, name)
        bad[name]["profile"].update(fields)
        run(binary, bad, error=error, prefix="names.")
        checks += 1
    # Real s390x exports outside the qualified big-endian model (`reject.zig`).
    rejects = load(version, "s390x-reject")
    for name, error in [
        ("reject.atomicU12.json", "an atomic op on a 12-bit integer representation"),
        ("reject.packedUnion.json", "a `packed union` is outside the qualified big-endian model"),
        ("reject.f80Add.json", "`f80` is outside the qualified big-endian model"),
        ("reject.boolLanes.json", "a vector of `bool` or pointer lanes is outside"),
        ("reject.nibbleLanes.json", "a vector of non-byte-multiple lanes is outside"),
        ("reject.u128Bytes.json", "the memory model gives type"),
        ("reject.vecByte.json", "a pointer cast between a vector and another pointee type is illegal behaviour"),
        ("reject.vecFromBytes.json", "a pointer cast between a vector and another pointee type is illegal behaviour"),
        # Translated on 0.16.0 (`reject.zig`).
        ("reject.vecLanes.json", None if version == "0.16.0" else
         "a pointer to a vector lane (vector_index) is outside the subset"),
    ]:
        run(binary, one(rejects, name), error=error, prefix="reject.")
        checks += 1
    return checks


if __name__ == "__main__":
    main()
