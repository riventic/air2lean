#!/usr/bin/env python3
"""L05 null-pointer provenance: the committed exports match provenance.json byte for byte.

Runs no compiler. `--refresh` rewrites provenance.json after `export.sh` (it records the patched
compilers' hashes from AIR2LEAN_ZIG_AIR).
"""
import hashlib
import json
import os
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
VERSIONS = ("0.17.0", "0.16.0", "0.15.2", "0.14.1")
PROVENANCE = HERE / "provenance.json"
COMMAND = ("ZIG_AIR_JSON_DIR=<dir>/<version> ZIG_AIR_JSON_FILTER=<roots> <patched zig> build-obj -fno-emit-bin "
           "-OReleaseSafe -fno-error-tracing -target x86_64-linux -mcpu=baseline <source>.zig (export.sh)")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def current():
    return {
        "sources": {name: sha(HERE / name) for name in ("nullpointers.zig", "reject.zig")},
        "exporter": "zig-patch/air-json/json.zig",
        "exporter_sha256": sha(ROOT / "zig-patch/air-json/json.zig"),
        "air": {"schema": 12, "target": "x86_64-linux", "cpu": "baseline",
                "optimization": "ReleaseSafe", "error_tracing": False, "command": COMMAND},
        "air_sha256": {f"{d}/{v}/{p.name}": sha(p) for d in ("air", "air-reject") for v in VERSIONS
                       for p in sorted((HERE / d / v).glob("*.json"))},
    }


def refresh():
    record = current()
    zig_root = Path(os.environ["AIR2LEAN_ZIG_AIR"])
    record["patched_compiler_sha256"] = {v: sha(zig_root / f"zig-air-{v}/bin/zig-unlocked") for v in VERSIONS}
    record["qualification"] = ("Compiler exports of nullpointers.zig and reject.zig by patched 0.17.0, 0.16.0, "
                               "0.15.2 and 0.14.1 compilers built from the recorded exporter; check.sh translates "
                               "each and compares the model with expected/<version>.txt, which check.sh --native "
                               "compares with native runs.")
    PROVENANCE.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")


class Provenance(unittest.TestCase):
    def test_record_matches_files(self):
        recorded = json.loads(PROVENANCE.read_text())
        now = current()
        for key in ("sources", "exporter", "exporter_sha256", "air", "air_sha256"):
            self.assertEqual(recorded[key], now[key], key)
        compilers = recorded["patched_compiler_sha256"]
        self.assertEqual(sorted(compilers), sorted(VERSIONS))
        self.assertEqual(len(set(compilers.values())), len(VERSIONS), "one digest for several compilers")

    def test_every_file_is_this_versions_export(self):
        for d in ("air", "air-reject"):
            for version in VERSIONS:
                files = sorted((HERE / d / version).glob("*.json"))
                self.assertTrue(files, (d, version))
                for path in files:
                    document = json.loads(path.read_text())
                    self.assertEqual((document["zig_version"], document["schema"]), (version, 12), path.name)
                    profile = document["profile"]
                    self.assertEqual((profile["build_mode"], profile["error_tracing"], profile["cpu"]),
                                     ("ReleaseSafe", False, "x86_64"), path.name)

if __name__ == "__main__":
    if sys.argv[1:] == ["--refresh"]:
        refresh()
        sys.argv[1:] = []
    unittest.main()
