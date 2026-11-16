#!/usr/bin/env python3
"""L10 error-width native provenance: the committed native observations match provenance.json
byte for byte and cover every version. The AIR exports (`air-fresh/`) are pinned by
`exports.lock.json` (scripts/fixture-exports.py check error-width), not here.

Runs no compiler. `--refresh` rewrites provenance.json after `native.py`: it records the hashes
of the stock compilers that produced `native/` (AIR2LEAN_NATIVE_ZIG, a `version=path,...` list;
a compiler on another host as `version=sha256:<hex>`, `shasum -a 256` there).
"""
import hashlib
import json
import os
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROVENANCE = HERE / "provenance.json"
VERSIONS = ("0.17.0", "0.16.0", "0.15.2", "0.14.1")
NATIVE_COMMAND = ("<stock zig> build-exe -lc -OReleaseSafe -fno-error-tracing [--error-limit <limit>] "
                  "probe.zig, one build per configuration (native.py)")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def current():
    return {
        "command": NATIVE_COMMAND,
        "probe_sha256": sha(HERE / "probe.zig"),
        "driver_sha256": sha(HERE / "native.py"),
        "observations_sha256": {p.name: sha(p) for p in sorted((HERE / "native").glob("*.txt"))},
    }


def refresh():
    old = json.loads(PROVENANCE.read_text())["native"] if PROVENANCE.exists() else {}
    record = current()
    given = os.environ.get("AIR2LEAN_NATIVE_ZIG")
    if not given:
        sys.exit("set AIR2LEAN_NATIVE_ZIG to the stock compilers that produced native/")
    paths = dict(item.split("=", 1) for item in given.split(","))
    record["stock_compiler_sha256"] = {
        v: paths[v][len("sha256:"):] if paths[v].startswith("sha256:") else sha(paths[v]) for v in VERSIONS}
    record["target"] = old.get("target", "aarch64-macos")
    PROVENANCE.write_text(json.dumps({"native": record}, indent=2, sort_keys=True) + "\n")


class Provenance(unittest.TestCase):
    def test_record_matches_files(self):
        recorded = json.loads(PROVENANCE.read_text())
        self.assertEqual(sorted(recorded), ["native"])
        for key, value in current().items():
            self.assertEqual(recorded["native"][key], value, key)
        self.assertEqual(sorted(recorded["native"]["stock_compiler_sha256"]), sorted(VERSIONS))

    def test_every_exported_function_is_kept_alive(self):
        source = (HERE / "error_width.zig").read_text()
        names = {p.stem.split(".", 1)[1] for p in (HERE / "air-fresh").glob("*/bits*/*.json")}
        self.assertEqual(len(names), 7)
        for name in names:
            self.assertIn(f"_ = &{name};", source)

    def test_native_files_cover_every_version(self):
        for version in VERSIONS:
            text = (HERE / "native" / f"aarch64-macos-{version}.txt").read_text()
            self.assertIn(f"meta zig {version}\n", text)


if __name__ == "__main__":
    if sys.argv[1:] == ["--refresh"]:
        refresh()
    else:
        unittest.main()
