#!/usr/bin/env python3
"""L-series long tail provenance: the committed exports match provenance.json byte for byte.

Runs no compiler. `--refresh` rewrites provenance.json after `export.sh` (it records the
patched compilers' hashes from AIR2LEAN_ZIG_AIR, default /opt/dev/air2lean-build).
"""
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
VERSIONS = ("0.17.0", "0.16.0", "0.15.2", "0.14.1")
PROVENANCE = HERE / "provenance.json"
# Each fixture source and the register row whose evidence it is.
SOURCES = {
    "error_params": "L10",
}
COMMAND = ("ZIG_AIR_JSON_DIR=air/<stem>/<version> ZIG_AIR_JSON_FILTER=<stem>. <patched zig> build-obj "
           "-fno-emit-bin -OReleaseSafe -fno-error-tracing -target x86_64-linux -mcpu=baseline <stem>.zig "
           "(export.sh)")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def air_files(stem, version):
    return sorted((HERE / "air" / stem / version).glob("*.json"))


def current():
    return {
        "sources": {stem: {"row": row, "source": f"tests/roadmap/lang-long-tail/{stem}.zig",
                           "source_sha256": sha(HERE / f"{stem}.zig")}
                    for stem, row in SOURCES.items()},
        "exporter": "zig-patch/air-json/json.zig",
        "exporter_sha256": sha(ROOT / "zig-patch/air-json/json.zig"),
        "air": {"schema": 12, "target": "x86_64-linux", "cpu": "baseline",
                "optimization": "ReleaseSafe", "error_tracing": False, "command": COMMAND},
        "air_sha256": {f"{stem}/{v}/{p.name}": sha(p) for stem in SOURCES for v in VERSIONS
                       for p in air_files(stem, v)},
    }


def refresh():
    record = current()
    zig_root = Path(os.environ.get("AIR2LEAN_ZIG_AIR", "/opt/dev/air2lean-build"))
    # bin/zig is the AIR-only lock wrapper (zig-patch/lock.sh), the same file for every version.
    record["patched_compiler_sha256"] = {v: sha(zig_root / f"zig-air-{v}/bin/zig-unlocked") for v in VERSIONS}
    record["qualification"] = ("Compiler exports of every function of each fixture source with patched "
                               "0.17.0, 0.16.0, 0.15.2 and 0.14.1 compilers built from the recorded exporter, "
                               "x86_64-linux ReleaseSafe. They are the translator's evidence for the rows named "
                               "in `sources`; other shapes are not covered.")
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
        for stem in SOURCES:
            for version in VERSIONS:
                files = air_files(stem, version)
                self.assertTrue(files, f"{stem} {version}")
                for path in files:
                    document = json.loads(path.read_text())
                    self.assertEqual(document["zig_version"], version, path.name)
                    self.assertEqual(document["schema"], 12, path.name)
                    profile = document["profile"]
                    self.assertEqual((profile["build_mode"], profile["error_tracing"], profile["cpu"]),
                                     ("ReleaseSafe", False, "x86_64"), path.name)

    def test_every_exported_function_is_in_the_source(self):
        for stem in SOURCES:
            text = (HERE / f"{stem}.zig").read_text()
            for version in VERSIONS:
                for path in air_files(stem, version):
                    name = json.loads(path.read_text())["name"]
                    base = re.sub(r"__(anon|func)_\w+$", "", name.split(".", 1)[1])
                    self.assertRegex(text, rf"fn {re.escape(base)}\b", path.name)


if __name__ == "__main__":
    if sys.argv[1:] == ["--refresh"]:
        refresh()
    else:
        unittest.main()
