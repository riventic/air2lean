#!/usr/bin/env python3
"""L10 error-width provenance: the committed exports and native observations match
provenance.json byte for byte, and each export is the profile it claims.

Runs no compiler. `--refresh` rewrites provenance.json after `export.sh` and `native.py`: it
records the hashes of the patched compilers (AIR2LEAN_ZIG_AIR, default /opt/dev/air2lean-build)
and of the stock compilers that produced `native/` (AIR2LEAN_NATIVE_ZIG, a `version=path,...`
list; default: the three versions of this host's `~/.cache/air2lean`).
"""
import hashlib
import json
import os
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PROVENANCE = HERE / "provenance.json"
VERSIONS = ("0.16.0", "0.15.2", "0.14.1")
# Directory -> error_set_bits of the `--error-limit` it was exported with (export.sh).
WIDTHS = {2: 2, 8: 8, 10: 10, 16: 16, 17: 17, 32: 32}
LIMITS = {2: 3, 8: 255, 10: 1000, 16: None, 17: 100000, 32: 4294967295}
COMMAND = ("ZIG_AIR_JSON_DIR=air-fresh/<version>/bits<N> ZIG_AIR_JSON_FILTER=error_width. <patched zig> "
           "build-obj -fno-emit-bin -OReleaseSafe -fno-error-tracing -target x86_64-linux "
           "-mcpu=baseline [--error-limit <limit>] error_width.zig (export.sh)")
NATIVE_COMMAND = ("<stock zig> build-exe -lc -OReleaseSafe -fno-error-tracing [--error-limit <limit>] "
                  "probe.zig, one build per configuration (native.py)")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def exports():
    return sorted((HERE / "air-fresh").glob("*/bits*/*.json"))


def current():
    return {
        "source": "tests/roadmap/error-width/error_width.zig",
        "source_sha256": sha(HERE / "error_width.zig"),
        "exporter": "zig-patch/air-json/json.zig",
        "exporter_sha256": sha(ROOT / "zig-patch/air-json/json.zig"),
        "air": {"schema": 12, "target": "x86_64-linux", "cpu": "baseline",
                "optimization": "ReleaseSafe", "error_tracing": False, "command": COMMAND,
                "error_limits": {f"bits{b}": LIMITS[b] or "default" for b in WIDTHS}},
        "air_sha256": {str(p.relative_to(HERE / "air-fresh")): sha(p) for p in exports()},
        "native": {
            "command": NATIVE_COMMAND,
            "probe_sha256": sha(HERE / "probe.zig"),
            "driver_sha256": sha(HERE / "native.py"),
            "observations_sha256": {p.name: sha(p) for p in sorted((HERE / "native").glob("*.txt"))},
        },
    }


def tool_hashes():
    root = Path(os.environ.get("AIR2LEAN_ZIG_AIR", "/opt/dev/air2lean-build"))
    patched = {v: sha(root / f"zig-air-{v}/bin/zig-unlocked") for v in VERSIONS}
    home = Path.home() / ".cache/air2lean"
    default = {"0.16.0": home / "host-0.16.0/zig", "0.15.2": home / "host-0.15.2/zig",
               "0.14.1": Path("/opt/dev/air2lean-build/0.14.1/zig-aarch64-macos-0.14.1/zig")}
    given = os.environ.get("AIR2LEAN_NATIVE_ZIG")
    paths = dict(item.split("=", 1) for item in given.split(",")) if given else default
    stock = {v: sha(paths[v]) for v in VERSIONS}
    return patched, stock


def refresh():
    record = current()
    old = json.loads(PROVENANCE.read_text()) if PROVENANCE.exists() else {}
    record["patched_compiler_sha256"], record["native"]["stock_compiler_sha256"] = tool_hashes()
    record["native"]["target"] = old.get("native", {}).get("target", "aarch64-macos")
    PROVENANCE.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")


class Provenance(unittest.TestCase):
    def test_record_matches_files(self):
        recorded = json.loads(PROVENANCE.read_text())
        now = current()
        for key in ("source_sha256", "exporter_sha256", "air", "air_sha256"):
            self.assertEqual(recorded[key], now[key], key)
        for key in ("probe_sha256", "driver_sha256", "observations_sha256"):
            self.assertEqual(recorded["native"][key], now["native"][key], key)
        self.assertEqual(sorted(recorded["patched_compiler_sha256"]), sorted(VERSIONS))
        self.assertEqual(sorted(recorded["native"]["stock_compiler_sha256"]), sorted(VERSIONS))

    def test_every_export_is_this_versions_and_widths(self):
        seen = set()
        for path in exports():
            version, directory = path.parent.parent.name, path.parent.name
            document = json.loads(path.read_text())
            self.assertEqual(document["zig_version"], version, path)
            self.assertEqual(document["schema"], 12, path)
            profile = document["profile"]
            self.assertEqual((profile["build_mode"], profile["error_tracing"], profile["cpu"]),
                             ("ReleaseSafe", False, "x86_64"), path)
            self.assertEqual(profile["error_set_bits"], int(directory[4:]), path)
            seen.add((version, directory))
        self.assertEqual(seen, {(v, f"bits{b}") for v in VERSIONS for b in WIDTHS})

    def test_every_exported_function_is_in_the_source(self):
        source = (HERE / "error_width.zig").read_text()
        names = {p.stem.split(".", 1)[1] for p in exports()}
        self.assertEqual(len(names), 7)
        for name in names:
            self.assertIn(f"pub fn {name}(", source)
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
