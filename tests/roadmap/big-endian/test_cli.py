#!/usr/bin/env python3
"""T03: exercise a previously built translator on the retained s390x/x86_64 AIR.

Accepts the real s390x-linux export as the big-endian model profile `abi64-be-v1` (and only
with the `Zig.BigEndian` instances and `.big` bit-pointer accesses), keeps x86_64 on
`abi64-le-v1` without them, rejects contradictory endian metadata, and rejects every real
s390x export of `reject.zig` with its reason. A rejection leaves the previous output intact.
Never builds or runs a compiler.
"""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
AIR = HERE / "air" / "0.16.0"


def load(target):
    return {p.name: json.loads(p.read_text()) for p in sorted((AIR / target).glob("*.json"))}


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
    checks = 0
    big, little = load("s390x-linux"), load("x86_64-linux")
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
    # Real s390x exports outside the qualified big-endian model (`reject.zig`).
    rejects = load("s390x-reject")
    for name, error in [
        ("reject.atomicRead.json", "an atomic op is outside the qualified big-endian model"),
        ("reject.packedUnion.json", "a `packed union` is outside the qualified big-endian model"),
        ("reject.f80Add.json", "`f80` is outside the qualified big-endian model"),
        ("reject.boolLanes.json", "a vector of `bool` or pointer lanes is outside"),
        ("reject.nibbleLanes.json", "a vector of non-byte-multiple lanes is outside"),
        ("reject.tagName.json", "`@tagName` is outside the qualified big-endian model"),
        ("reject.create.json", "the std model 'mem.Allocator.create"),
        ("reject.u128Bytes.json", "the memory model gives type"),
    ]:
        run(binary, one(rejects, name), error=error, prefix="reject.")
        checks += 1
    print(f"big-endian CLI checks passed ({checks})")


if __name__ == "__main__":
    main()
