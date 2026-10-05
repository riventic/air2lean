#!/usr/bin/env python3
"""Exercise cache invalidation without running compiler processes outside the build guard."""
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from test_policy import audit


class ToolCacheTests(unittest.TestCase):
    def test_verified_cache_reuse_and_invalidation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tools").mkdir()
            source = root / "tools/Assurance.lean"
            source.write_text("import Lean\n")
            pin = root / "lean-toolchain"
            pin.write_text("leanprover/lean4:v4.34.0\n")
            (root / "lakefile.toml").write_text('name = "test"\n')
            dependency = root / "imported-dependency"
            dependency.write_text("original dependency")
            artifact = root / ".lake/build/lib/lean/tools/Assurance.olean"
            artifact.parent.mkdir(parents=True)
            builds, validations, previous_inputs = [], [], []

            def validate_and_build(command):
                # Mock Lake's responsibility for dependency freshness, never skip asking it.
                self.assertEqual(command, ["lake", "--rehash", "build", "AssuranceTools"])
                validations.append(command)
                inputs = source.read_bytes() + pin.read_bytes() + dependency.read_bytes()
                if not artifact.is_file() or previous_inputs != [inputs]:
                    builds.append(inputs)
                    artifact.write_bytes(b"checked artifact: " + inputs)
                    artifact.with_suffix(".trace").write_bytes(hashlib.sha256(inputs).digest())
                    previous_inputs[:] = [inputs]

            def prepare():
                trace = audit.prepare_tool(root, validate_and_build)
                self.assertEqual(trace["olean_sha256"], audit.file_sha256(artifact))
                self.assertEqual(trace["lake_trace_sha256"], audit.file_sha256(artifact.with_suffix(".trace")))
                return trace

            self.assertFalse(prepare()["cache_reused"])
            self.assertTrue(prepare()["cache_reused"])
            self.assertEqual(len(builds), 1)
            source.write_text(source.read_text() + "-- extractor changed\n")
            self.assertFalse(prepare()["cache_reused"])
            pin.write_text("leanprover/lean4:changed-release-pin\n")
            self.assertFalse(prepare()["cache_reused"])
            artifact.write_bytes(b"invalid cached tool")
            self.assertFalse(prepare()["cache_reused"])
            artifact.unlink()
            self.assertFalse(prepare()["cache_reused"])
            dependency.write_text("changed imported dependency")
            self.assertFalse(prepare()["cache_reused"])
            self.assertEqual(len(builds), 6)
            self.assertEqual(len(validations), 7)

    def test_failed_preparation_never_publishes_valid_cache(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "tools").mkdir()
            (root / "tools/Assurance.lean").write_text("import Lean\n")
            (root / "lean-toolchain").write_text("pin\n")
            (root / "lakefile.toml").write_text('name = "test"\n')

            def failed_builder(_):
                raise RuntimeError("compiler failed")

            with self.assertRaises(RuntimeError):
                audit.prepare_tool(root, failed_builder)
            self.assertFalse((root / ".lake/assurance/tool-trace.json").exists())


if __name__ == "__main__":
    unittest.main()
