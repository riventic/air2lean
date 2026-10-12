#!/usr/bin/env python3
"""CLI regressions for union-member constant pointer bases (L06), for a root-built translator.

`air/<version>` and `air-reject/<version>` are compiler exports (provenance.json) of
`union_bases.zig` and `union_reject.zig` from patched 0.16.0, 0.15.2 and 0.14.1 compilers built
from this tree's exporter. Every version translates to the retained `UnionBases/Gen.lean`; each
union-member base is its global's block plus the exact total offset. The shapes outside the model
stay explicit errors. Never builds or invokes compilers.

`test_cli.py --refresh-provenance <dir>` rewrites provenance.json after `export.sh`, with the
compilers `<dir>/zig-air-<version>/bin/zig-unlocked`.
"""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
VERSIONS = ("0.16.0", "0.15.2", "0.14.1")
GEN = HERE / "UnionBases" / "Gen.lean"
PROVENANCE = HERE / "provenance.json"
ARGS = ["--namespace", "UnionBases", "--prefix", "union_bases.", "--allow-unqualified-build-mode"]
REJECT_ARGS = ["--namespace", "UnionReject", "--prefix", "union_reject.", "--allow-unqualified-build-mode"]
COMMAND = ("ZIG_AIR_JSON_DIR=<dir>/<version> ZIG_AIR_JSON_FILTER=<source>. <patched zig> build-obj "
           "-fno-emit-bin -OReleaseSafe -fno-error-tracing -fno-llvm -fno-lld -target x86_64-linux-musl "
           "-mcpu=baseline <source>.zig (export.sh)")
# Each returned constant: (block, offset) of the global it is based on.
CONSTANTS = {
    "extWordPtr": (0, 36), "extHiPtr": (0, 38), "extBytePtr": (0, 38), "wideCellPtr": (0, 48),
    "lowPairPtr": (0, 1), "barePairPtr": (0, 78), "outerPairPtr": (0, 27), "maybeCellPtr": (0, 58),
    "resBytePtr": (0, 71), "mixedLowPtr": (1, 5), "mixedHighPtr": (1, 7),
}
UNBACKED = "a pointer constant without a global (union_field) is outside the subset"
# A typed alias of error storage must name a matching subobject, which is not reconstructed
# through a union member (`matchingGlobalSubobject`).
ALIAS = "outside the finite error-storage fragment"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def provenance():
    """The current hashes of everything provenance.json pins, except the compilers."""
    return {
        "sources": {name: sha(HERE / name) for name in ("union_bases.zig", "union_reject.zig")},
        "exporter_sha256": {name: sha(ROOT / "zig-patch/air-json" / name)
                            for name in ("json.zig", "pointer-offset.zig", "identity.zig")},
        "command": COMMAND,
        "air_sha256": {f"{d}/{v}/{p.name}": sha(p) for d in ("air", "air-reject") for v in VERSIONS
                       for p in sorted((HERE / d / v).glob("*.json"))},
    }


def fixtures(directory):
    return {p.name: json.loads(p.read_text()) for p in sorted(directory.glob("*.json"))}


def translate(binary, documents, directory, args=ARGS):
    air = directory / "air"
    air.mkdir()
    for name, document in documents.items():
        (air / name).write_text(json.dumps(document))
    out = directory / "Gen.lean"
    out.write_text("sentinel\n")
    result = subprocess.run([str(binary), str(air), "-o", str(out), *args], text=True,
                            capture_output=True, check=False, timeout=60)
    return result, out


def accept(binary, documents):
    with tempfile.TemporaryDirectory(prefix="air2lean-union-bases-") as d:
        result, out = translate(binary, documents, Path(d))
        assert result.returncode == 0, result.stderr
        return out.read_text()


def reject(binary, documents, marker, code, args=ARGS):
    """CLI rejection with `marker`; `--diagnostics-json` reports it under `code`."""
    with tempfile.TemporaryDirectory(prefix="air2lean-union-bases-") as d:
        result, out = translate(binary, documents, Path(d), args)
        assert result.returncode == 1, (marker, result.returncode, result.stderr)
        assert marker in result.stderr, (marker, result.stderr)
        assert out.read_text() == "sentinel\n", "a rejected input replaced the output"
        diagnostics = subprocess.run([str(binary), "--diagnostics-json", str(Path(d) / "air"),
                                      "--allow-unqualified-build-mode"],
                                     text=True, capture_output=True, check=False, timeout=60)
        assert diagnostics.returncode == 1, diagnostics.stderr
        hits = [e for e in json.loads(diagnostics.stdout)["diagnostics"] if marker in e["message"]]
        assert hits and all(e["code"] == code for e in hits), (marker, code, hits)
    return 1


def body(text):
    """A translation without its first (profile) line."""
    return text.split("\n", 1)[1]


def ret_value(document):
    return document["body"][-1]["args"][0]


def llvm(documents):
    documents = copy.deepcopy(documents)
    for document in documents.values():
        document["profile"]["backend"] = "stage2_llvm"
    return documents


def main():
    binary = Path(sys.argv[1] if len(sys.argv) > 1 else ROOT / ".lake/build/bin/air2lean")
    checks = 0

    recorded = json.loads(PROVENANCE.read_text())
    now = provenance()
    for key, value in now.items():
        assert recorded[key] == value, f"provenance.json {key} is stale (export.sh, --refresh-provenance)"
    compilers = recorded["patched_compiler_sha256"]
    assert sorted(compilers) == sorted(VERSIONS) and len(set(compilers.values())) == len(VERSIONS)
    checks += 1

    # Every version: the retained translation (up to the profile line), each union-member base
    # the global's block plus its total offset, and no invented block.
    retained = GEN.read_text()
    exports = {v: fixtures(HERE / "air" / v) for v in VERSIONS}
    for version, documents in exports.items():
        assert all(d["zig_version"] == version and d["profile"]["backend"] == "stage2_x86_64"
                   for d in documents.values()), version
        text = accept(binary, documents)
        assert body(text) == body(retained), f"{version}: translation differs from UnionBases/Gen.lean"
        assert f'"zig_version":"{version}"' in text.split("\n", 1)[0], version
        for function, (block, off) in CONSTANTS.items():
            assert f"pure (.ret (⟨some {block}, {off}⟩ : Zig.Ptr))" in text, (version, function)
        assert "pure (.ret (⟨(⟨some 0, 46⟩ : Zig.Ptr), (2 : BitVec 64)⟩ : Zig.Slice))" in text
        assert "-- 2:" not in text, "a block was invented"
        checks += 1

    # The exporter fails closed for a member whose compiler payload offset is not the model's
    # (`odd`: an explicitly aligned member), and the translator for a member with error storage.
    for version in VERSIONS:
        documents = fixtures(HERE / "air-reject" / version)
        odd = ret_value(documents["union_reject.oddPtr.json"])["ptr"]
        assert odd.get("unsupported") == "union_field" and "global" not in odd, (version, odd)
        checks += reject(binary, documents, UNBACKED, "CONSTANT_FAILURE", REJECT_ARGS)
        checks += reject(binary, {k: v for k, v in documents.items() if "resPtr" in k}, ALIAS,
                         "STRUCTURE_FAILURE", REJECT_ARGS)

    # The same reason injected into an accepted program is rejected.
    latest = exports["0.16.0"]
    edited = copy.deepcopy(latest)
    ret_value(edited["union_bases.wideCellPtr.json"])["ptr"] = {"unsupported": "union_field", "off": 0}
    checks += reject(binary, edited, UNBACKED, "CONSTANT_FAILURE")

    # stage2_llvm: union members are scanned member by member. A constant at or one past
    # `mixed`'s alignment-1 `Failure![2]u8` payload (6..8, through the `raw` member) is rejected;
    # every other union-member constant is accepted.
    checks += reject(binary, llvm(latest), "mixedHighPtr: a pointer constant at offset 7 of global 0 "
                     "may address", "CONSTANT_FAILURE")
    accepted = accept(binary, llvm({k: v for k, v in latest.items() if "mixedHighPtr" not in k}))
    assert "pure (.ret (⟨some 1, 5⟩ : Zig.Ptr))" in accepted
    checks += 1

    print(f"{checks} union-member constant base CLI checks passed")


def refresh(zig_root):
    record = provenance()
    record["patched_compiler_sha256"] = {v: sha(Path(zig_root) / f"zig-air-{v}/bin/zig-unlocked")
                                         for v in VERSIONS}
    record["note"] = ("Each compiler is zig-patch/build.sh <version> from this tree's exporter "
                      "(exporter_sha256); patched_compiler_sha256 hashes bin/zig-unlocked behind the "
                      "AIR-only lock wrapper.")
    PROVENANCE.write_text(json.dumps(record, indent=2, sort_keys=True, ensure_ascii=False) + "\n")


if __name__ == "__main__":
    if sys.argv[1:2] == ["--refresh-provenance"]:
        refresh(sys.argv[2])
    else:
        main()
