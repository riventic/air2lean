#!/usr/bin/env python3
"""scripts/diff.sh runs a prebuilt native side (AIR2LEAN_DIFF_PREBUILT) only under the stock Zig
version, optimize mode, backend and target that built it (`air2lean-native.txt`). A fake `zig`
answers `version`; the run stops before any build or harness run. No Zig or Lean."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]


class PrebuiltNative(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)
        self.zig = self.dir / "zig"
        self.zig.write_text('#!/bin/sh\n[ "$1" = version ] && echo 0.16.0 && exit 0\nexit 3\n')
        self.zig.chmod(0o755)
        self.native = self.dir / "native"
        self.native.mkdir()

    def tearDown(self):
        self.tmp.cleanup()

    def run_diff(self):
        env = {k: v for k, v in os.environ.items() if not k.startswith("AIR2LEAN_")}
        env.update(AIR2LEAN_ZIG=str(self.zig), AIR2LEAN_DIFF_PREBUILT=str(self.native),
                   AIR2LEAN_EXAMPLES="basic", AIR2LEAN_DIFF_REPORT=str(self.dir / "report.json"),
                   PYTHONDONTWRITEBYTECODE="1")
        return subprocess.run(["bash", str(ROOT / "scripts/diff.sh")], cwd=ROOT, env=env,
                              capture_output=True, text=True, timeout=120)

    def stamp(self, text):
        (self.native / "air2lean-native.txt").write_text(text + "\n")

    def test_other_zig_version_is_refused(self):
        self.stamp("zig=0.15.2 optimize=ReleaseSafe backend=default target=host")
        r = self.run_diff()
        self.assertEqual(r.returncode, 1, r.stderr)
        self.assertIn("was built with 'zig=0.15.2", r.stderr)

    def test_other_mode_is_refused(self):
        self.stamp("zig=0.16.0 optimize=Debug backend=default target=host")
        r = self.run_diff()
        self.assertEqual(r.returncode, 1, r.stderr)
        self.assertIn("was built with 'zig=0.16.0 optimize=Debug", r.stderr)

    def test_unrecorded_is_refused(self):
        r = self.run_diff()
        self.assertEqual(r.returncode, 1, r.stderr)
        self.assertIn("was built with 'unrecorded'", r.stderr)

    def test_same_build_passes_the_guard(self):
        self.stamp("zig=0.16.0 optimize=ReleaseSafe backend=default target=host")
        r = self.run_diff()
        # It goes on to run the (missing) harnesses and fails there, past the guard.
        self.assertNotIn("was built with", r.stderr)
        self.assertIn("== running zig harnesses ==", r.stderr)


if __name__ == "__main__":
    unittest.main()
