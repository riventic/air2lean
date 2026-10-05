#!/usr/bin/env python3
"""Reproduction guard regressions; these tests never invoke Zig, Lake, or Lean."""
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[3]
CASE = ROOT / "case-studies/flow-time"
COMPARE = ROOT / "tests/roadmap/flow-time/compare-air.py"


class ProvenanceGuards(unittest.TestCase):
    def test_source_hash_success_change_and_missing(self):
        with tempfile.TemporaryDirectory() as name:
            directory = pathlib.Path(name)
            checker = directory / "check-source.py"
            shutil.copyfile(CASE / "check-source.py", checker)
            source = directory / "external.zig"
            source.write_bytes(b"external production source\n")
            (directory / "provenance.json").write_text(json.dumps({"production_sha256": hashlib.sha256(source.read_bytes()).hexdigest()}))
            good = subprocess.run(["python3", str(checker), str(source)], capture_output=True, text=True)
            self.assertEqual(good.returncode, 0, good.stderr)
            source.write_bytes(b"changed external production source\n")
            stale = subprocess.run(["python3", str(checker), str(source)], capture_output=True, text=True)
            self.assertNotEqual(stale.returncode, 0)
            self.assertIn("Flow source changed", stale.stderr)
            source.unlink()
            missing = subprocess.run(["python3", str(checker), str(source)], capture_output=True, text=True)
            self.assertNotEqual(missing.returncode, 0)
            self.assertIn("Flow source unavailable", missing.stderr)

    def test_manifest_hash_is_required_and_validated(self):
        with tempfile.TemporaryDirectory() as name:
            directory = pathlib.Path(name)
            checker = directory / "check-source.py"
            shutil.copyfile(CASE / "check-source.py", checker)
            source = directory / "external.zig"
            source.write_bytes(b"external production source\n")
            for manifest in ({}, {"production_sha256": None}, {"production_sha256": 7},
                             {"production_sha256": "a" * 63}, {"production_sha256": "g" * 64},
                             {"production_sha256": "A" * 64}):
                (directory / "provenance.json").write_text(json.dumps(manifest))
                result = subprocess.run(["python3", str(checker), str(source)], capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("Flow provenance invalid", result.stderr)
            (directory / "provenance.json").write_text(json.dumps({"production_sha256": "0" * 64}))
            stale = subprocess.run(["python3", str(checker), str(source)], capture_output=True, text=True)
            self.assertNotEqual(stale.returncode, 0)
            self.assertIn("Flow source changed", stale.stderr)

    def test_real_pipeline_rejects_changed_source_before_tool_execution(self):
        with tempfile.TemporaryDirectory() as name:
            source = pathlib.Path(name) / "changed.zig"
            source.write_text("// deliberately different source\n")
            result = subprocess.run(["bash", str(ROOT / "scripts/flow-time.sh")],
                                    env={**os.environ, "FLOW_TIME_SOURCE": str(source),
                                         "AIR2LEAN_ZIG_AIR": "/must-not-be-executed"},
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("Flow source changed", result.stderr)
            self.assertNotIn("compiler unavailable", result.stderr)

    def test_artifact_proof_scan_fails_closed_without_external_source(self):
        with tempfile.TemporaryDirectory() as name:
            directory = pathlib.Path(name)
            scan = directory / "rg"
            for status in (0, 2, 127):
                scan.write_text(f"#!/bin/sh\nexit {status}\n")
                scan.chmod(0o755)
                result = subprocess.run(["bash", str(ROOT / "scripts/flow-time.sh"), "--check-artifacts"],
                                        env={**os.environ, "PATH": str(directory) + os.pathsep + os.environ["PATH"],
                                             "FLOW_TIME_SOURCE": "/missing/external/production/source.zig"},
                                        capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertNotIn("Flow source unavailable", result.stderr)
                self.assertIn("untrusted proof" if status == 0 else "proof scan failed", result.stderr)

    def test_air_accepts_equal_json_rejects_changed_and_incomplete_exports(self):
        with tempfile.TemporaryDirectory() as name:
            directory = pathlib.Path(name)
            for source in (CASE / "air").glob("*.json"):
                shutil.copyfile(source, directory / source.name)
            def compare():
                return subprocess.run(["python3", str(COMPARE), str(CASE / "air"), str(directory)],
                                      capture_output=True, text=True)
            self.assertEqual(compare().returncode, 0)
            source = directory / "flow_time.timestamp32.json"
            source.write_text(source.read_text().replace('"target_endian": "little"',
                                                        '"target_endian": "big"'))
            changed = compare()
            self.assertNotEqual(changed.returncode, 0)
            self.assertIn("Flow AIR changed", changed.stderr)
            source.unlink()
            missing = compare()
            self.assertNotEqual(missing.returncode, 0)
            self.assertIn("exactly both timestamp entry points", missing.stderr)


if __name__ == "__main__":
    unittest.main()
