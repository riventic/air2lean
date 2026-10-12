#!/usr/bin/env python3
"""L14 error-tracing provenance: the committed exports match provenance.json byte for byte.

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
COMMAND = ("ZIG_AIR_JSON_DIR=air/<version> ZIG_AIR_JSON_FILTER=<roots>,builtin.returnError,lang.returnError "
           "<patched zig> build-obj -fno-emit-bin -OReleaseSafe -ferror-tracing -target x86_64-linux "
           "-mcpu=baseline error_tracing.zig (export.sh)")
TRACE_TAGS = {"err_return_trace", "set_err_return_trace", "save_err_return_trace_index", "ret_addr",
              "is_non_err_ptr"}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def current():
    return {
        "source": "tests/roadmap/error-tracing/error_tracing.zig",
        "source_sha256": sha(HERE / "error_tracing.zig"),
        "exporter": "zig-patch/air-json/json.zig",
        "exporter_sha256": sha(ROOT / "zig-patch/air-json/json.zig"),
        "air": {"schema": 12, "target": "x86_64-linux", "cpu": "baseline",
                "optimization": "ReleaseSafe", "error_tracing": True, "command": COMMAND},
        "air_sha256": {f"{v}/{p.name}": sha(p) for v in VERSIONS
                       for p in sorted((HERE / "air" / v).glob("*.json"))},
    }


def refresh():
    record = current()
    zig_root = Path(os.environ["AIR2LEAN_ZIG_AIR"])
    record["patched_compiler_sha256"] = {v: sha(zig_root / f"zig-air-{v}/bin/zig-unlocked") for v in VERSIONS}
    record["qualification"] = ("Compiler exports of error_tracing.zig with error return tracing by patched "
                               "0.17.0, 0.16.0, 0.15.2 and 0.14.1 compilers built from the recorded exporter; "
                               "check.sh translates each and compares the model's results with native runs.")
    PROVENANCE.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")


def tags(body):
    for i in body:
        yield i["tag"]
        for key in ("body", "then", "else"):
            yield from tags(i.get(key, []))
        for case in i.get("cases", []):
            yield from tags(case["body"])


class Provenance(unittest.TestCase):
    def test_record_matches_files(self):
        recorded = json.loads(PROVENANCE.read_text())
        now = current()
        for key in ("source", "source_sha256", "exporter", "exporter_sha256", "air", "air_sha256"):
            self.assertEqual(recorded[key], now[key], key)
        compilers = recorded["patched_compiler_sha256"]
        self.assertEqual(sorted(compilers), sorted(VERSIONS))
        self.assertEqual(len(set(compilers.values())), len(VERSIONS), "one digest for several compilers")

    def test_every_version_exports_the_trace(self):
        for version in VERSIONS:
            files = sorted((HERE / "air" / version).glob("*.json"))
            seen = set()
            for path in files:
                document = json.loads(path.read_text())
                self.assertEqual((document["zig_version"], document["schema"]), (version, 12), path.name)
                self.assertTrue(document["profile"]["error_tracing"], path.name)
                seen |= set(tags(document["body"]))
            # Every trace operation, and the ret_load check of a large error union.
            self.assertTrue(TRACE_TAGS <= seen, (version, TRACE_TAGS - seen))


if __name__ == "__main__":
    if sys.argv[1:] == ["--refresh"]:
        refresh()
        sys.argv[1:] = []
    unittest.main()
