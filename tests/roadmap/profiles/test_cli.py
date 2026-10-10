#!/usr/bin/env python3
"""Exercise a previously built translator. This driver never builds a compiler."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
CURRENT = json.loads((HERE / "current.json").read_text())
LEGACY = json.loads((HERE / "legacy.json").read_text())


def run(binary, documents, extra=(), error=None, mode="ieee"):
    with tempfile.TemporaryDirectory(prefix="air2lean-profiles-") as directory:
        directory = Path(directory)
        air = directory / "air"
        air.mkdir()
        for i, doc in enumerate(documents):
            (air / f"{i}.json").write_text(json.dumps(doc))
        out = directory / "out.lean"
        out.write_text("sentinel\n")
        result = subprocess.run([str(binary), str(air), "-o", str(out), "--namespace", "ProfileTests", *extra],
                                text=True, capture_output=True, check=False)
        if error is not None:
            assert result.returncode != 0, (error, result.stdout, result.stderr)
            assert error in result.stderr, (error, result.stderr)
            assert out.read_text() == "sentinel\n", "rejection overwrote previous output"
        else:
            assert result.returncode == 0, result.stderr
            marker = out.read_text().splitlines()[0]
            assert marker.startswith("-- air2lean-profile: "), marker
            metadata = json.loads(marker.removeprefix("-- air2lean-profile: "))
            expected = "abi64-le-v1" if documents[0]["schema"] == 12 else "legacy-abi64-le"
            assert metadata["profile"]["name"] == expected
            assert metadata["float_semantics"] == mode
            assert metadata["correspondence"] == "model"
            assert "pure (.ret" in out.read_text()


def main():
    binary = Path(sys.argv[1]).resolve(strict=True)
    run(binary, [CURRENT])
    run(binary, [LEGACY])
    versioned = copy.deepcopy(CURRENT)
    versioned["profile"]["target_triple"] = "x86_64-linux.4.19...6.1-gnu.2.28"
    run(binary, [versioned])
    mac = copy.deepcopy(CURRENT)
    mac["profile"]["target_triple"] = "aarch64-macos.13.0...15.0-none"
    mac["profile"]["abi"] = "none"
    mac["profile"]["cpu"] = "apple_m1"
    mac["profile"]["features"] = ["neon"]
    run(binary, [mac])
    # aarch64-linux (T04): gnu only (every supported Zig version has a native probe record).
    arm = copy.deepcopy(CURRENT)
    arm["profile"].update(target_triple="aarch64-linux.6.8...6.8-gnu.2.39", cpu="generic", features=["neon"])
    run(binary, [arm])
    arm17 = copy.deepcopy(arm)
    arm17["zig_version"] = arm17["profile"]["zig_version"] = "0.17.0"
    arm17["profile"]["build_mode"] = "safe"
    run(binary, [arm17])
    musl = copy.deepcopy(arm)
    musl["profile"].update(target_triple="aarch64-linux-musl", abi="musl")
    run(binary, [musl], error="qualified for the gnu ABI only")
    # The float rules are generic's: a CPU with fullfp16 fuses an f16 @mulAdd.
    fp16 = copy.deepcopy(arm)
    fp16["profile"]["features"] = ["fullfp16", "neon"]
    run(binary, [fp16], error="fullfp16 is outside the aarch64-linux float rules")
    run(binary, [CURRENT], ["--profile", "abi64-le-v1", "--float-semantics", "compiler-rt"], mode="compiler-rt")
    for field in CURRENT["profile"]:
        malformed = copy.deepcopy(CURRENT)
        del malformed["profile"][field]
        run(binary, [malformed], error="profile")
    for field, value, error in [
        ("pointer_bits", 32, "64-bit"), ("endian", "big", "little-endian"),
        ("target_triple", "wasm32-freestanding-none", "ABI differs"),
        ("target_triple", "riscv64-linux-gnu", "model ABI scope"),
        ("zig_version", "0.15.2", "differs from top-level"),
        ("error_set_bits", 0, "1..32-bit"), ("error_set_bits", 33, "1..32-bit"),
        ("error_tracing", "false", "error_tracing"),
        ("export_stage", "shipping-binary", "binary correspondence is unqualified"),
        ("float_mode", "fast", "optimized AIR remains unsupported"),
        ("features", ["sse", "sse"], "duplicate feature"),
    ]:
        malformed = copy.deepcopy(CURRENT)
        malformed["profile"][field] = value
        run(binary, [malformed], error=error)
    malformed = copy.deepcopy(CURRENT)
    malformed["profile"] = None
    run(binary, [malformed], error="profile: object expected")
    for schema in (0, 13, 999):
        malformed = copy.deepcopy(CURRENT)
        malformed["schema"] = schema
        run(binary, [malformed], error="unsupported AIR schema")
    malformed = copy.deepcopy(CURRENT)
    malformed["profile"]["binary_correspondence"] = "verified"
    run(binary, [malformed], error="unsupported profile field")
    malformed = copy.deepcopy(CURRENT)
    del malformed["profile"]
    run(binary, [malformed], error="requires 'profile'")
    malformed = copy.deepcopy(CURRENT)
    malformed["schema"] = 11
    run(binary, [malformed], error="requires AIR schema 12")
    malformed = copy.deepcopy(LEGACY)
    malformed["target_endian"] = "big"
    run(binary, [malformed], error="little-endian")
    run(binary, [CURRENT], ["--profile", "legacy-abi64-le"], error="selected profile")
    run(binary, [CURRENT], ["--profile", "unqualified"], error="invalid --profile")
    run(binary, [CURRENT], ["--profile"], error="missing value")
    mixed_current = copy.deepcopy(CURRENT)
    mixed_current["name"] = "secondProfileFixture"
    run(binary, [LEGACY, mixed_current], error="mixed AIR profiles")
    for field, value in [("cpu", "haswell"), ("build_mode", "Debug"),
                         ("backend", "stage2_x86_64"), ("error_tracing", True),
                         ("features", ["sse2", "sse"])]:
        changed = copy.deepcopy(CURRENT)
        changed["name"] = "secondProfileFixture"
        changed["profile"][field] = value
        run(binary, [CURRENT, changed], error="mixed AIR profiles")
    changed = copy.deepcopy(LEGACY)
    changed["schema"] = 10
    changed["name"] = "secondProfileFixture"
    run(binary, [LEGACY, changed], error="mixed AIR profiles")
    print("profile CLI positive/negative checks passed")


if __name__ == "__main__":
    main()
