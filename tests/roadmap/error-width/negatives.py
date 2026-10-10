#!/usr/bin/env python3
"""Error-width configurations the translator must reject, each with its diagnostic.

usage: negatives.py TRANSLATOR
"""
import copy
import json
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load(directory, name="storeError"):
    return json.loads((HERE / "air" / directory / f"error_width.{name}.json").read_text())


def with_bits(doc, bits):
    doc = copy.deepcopy(doc)
    doc["profile"]["error_set_bits"] = bits
    return doc


def with_code_layout(doc, size, align):
    doc = copy.deepcopy(doc)
    for ty in doc["types"]:
        if ty["k"] in ("error_set", "optional"):
            ty["abi_size"], ty["abi_align"] = size, align
        if ty["k"] == "ptr" and ty["child"] == 0:
            ty["ptr_align"] = align
    return doc


def with_version(doc, version):
    doc = copy.deepcopy(doc)
    doc["zig_version"] = doc["profile"]["zig_version"] = version
    return doc


# `@errorName` (Zig 0.16.0 export of `tests/golden/slices`), relabelled as other versions.
ERROR_NAME = json.loads((HERE.parents[1] / "golden" / "0.16.0" / "slices" / "air" /
                         "slices.failName.json").read_text())

CASES = {
    # `--error-limit 0`: no error integer and no storage.
    "zero width": ([with_bits(load("bits16"), 0)], "profile.error_set_bits 0 is outside"),
    # ErrorInt is u32: no wider error integer exists.
    "33 bits": ([with_bits(load("bits16"), 33)], "profile.error_set_bits 33 is outside"),
    # The profile says 8 bits; the layouts are the default 2-byte code.
    "8-bit profile, 16-bit layout": ([with_bits(load("bits16"), 8)],
                                     "must be the profile's 8-bit error integer"),
    # The profile says 16 bits; the layouts are 1-byte codes.
    "16-bit profile, 8-bit layout": ([with_bits(load("bits8"), 16)],
                                     "must be the profile's 16-bit error integer"),
    # `--error-limit 1`: one nonzero code cannot hold the two-name domain.
    "domain beyond capacity": ([with_code_layout(with_bits(load("bits8"), 1), 1, 1)],
                               "exceeds the 1 nonzero codes of the profile's 1-bit error integer"),
    # One program, two widths: profiles must agree exactly.
    "mixed widths": ([load("bits16"), load("bits8", "loadOptional")],
                     "mixed AIR profiles: field 'error_set_bits' differs"),
    # Zig 0.14.1 names no error whose code has the top bit set; the error count is not exported.
    "@errorName on 0.14.1": ([with_version(ERROR_NAME, "0.14.1")],
                             "`@errorName` is rejected for Zig 0.14.1"),
}

# The same `@errorName` function is accepted by the other versions: the rejection is the
# 0.14.1 dialect, not the operation.
ACCEPTED = {f"@errorName on {v}": [with_version(ERROR_NAME, v)] for v in ("0.15.2", "0.16.0")}


def translate(docs):
    with tempfile.TemporaryDirectory(prefix="air2lean-error-width-") as temp:
        air = Path(temp) / "air"
        air.mkdir()
        for doc in docs:
            (air / f"{doc['name']}.json").write_text(json.dumps(doc))
        result = subprocess.run([sys.argv[1], str(air), "-o", str(Path(temp) / "Gen.lean"),
                                 "--namespace", "ErrorWidthNegative",
                                 "--prefix", docs[0]["name"].split(".")[0] + "."],
                                capture_output=True, text=True, timeout=300)
        return result, (Path(temp) / "Gen.lean").exists()


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    for name, (docs, expected) in CASES.items():
        result, wrote = translate(docs)
        output = result.stdout + result.stderr
        if result.returncode == 0 or expected not in output:
            raise SystemExit(f"{name}: expected rejection containing {expected!r}, "
                             f"got exit {result.returncode}: {output[-2000:]}")
        if wrote:
            raise SystemExit(f"{name}: a rejected configuration wrote Gen.lean")
    for name, docs in ACCEPTED.items():
        result, wrote = translate(docs)
        if result.returncode != 0 or not wrote:
            raise SystemExit(f"{name}: expected translation, got exit {result.returncode}: "
                             f"{(result.stdout + result.stderr)[-2000:]}")
    print(f"error-width negatives rejected: {len(CASES)}; controls accepted: {len(ACCEPTED)}")


if __name__ == "__main__":
    main()
