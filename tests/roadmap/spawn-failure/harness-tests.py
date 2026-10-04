#!/usr/bin/env python3
"""Offline only: self-expiring tiny mocks with observed RSS <=32 MiB.
No compiler, translator, native, or network calls. Virtual-memory limits are not
used: the interpreter can reserve more address space than its resident footprint.
"""
import importlib.util
import json
from pathlib import Path
import resource
import signal
import subprocess
import sys
import tempfile
import unittest
sys.dont_write_bytecode = True
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("spawn_qualify", Path(__file__).with_name("qualify.py"))
qualify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(qualify)

class HarnessTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.directory = Path(self.temporary.name)
        self.gate = qualify.Gate(self.directory)

    def tearDown(self):
        self.temporary.cleanup()
        usage = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        peak_bytes = usage if sys.platform == "darwin" else usage * 1024
        self.assertLessEqual(peak_bytes, 32*1024*1024)

    def tiny(self, text, code=0):
        program = "import resource,signal,sys; signal.alarm(3); rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss; assert (rss if sys.platform == 'darwin' else rss*1024) <= 32*1024*1024; print(" + repr(text) + "); raise SystemExit(" + str(code) + ")"
        return [sys.executable, "-c", program]

    def test_passing_marker(self):
        self.gate.run("pass", self.tiny("PASS"), marker="PASS", timeout=2)
        self.assertEqual(self.gate.steps[-1]["status"], "passed")

    def test_missing_marker_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "missing evidence"):
            self.gate.run("missing", self.tiny("nothing"), marker="PASS", timeout=2)

    def test_wrong_exit_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "wrong exit"):
            self.gate.run("wrong", self.tiny("PASS", 1), marker="PASS", timeout=2)

    def test_compile_error_cannot_detect_mutant(self):
        with self.assertRaisesRegex(RuntimeError, "compilation failure"):
            self.gate.run("compile", self.tiny("file.lean:3: error: bad term\nSOURCE_REJECTED:", 1),
                          expected=1, marker="SOURCE_REJECTED:", timeout=2)

    def test_timeout_group_killed_before_reaping(self):
        events = []
        class Process:
            pid = 12345
            def wait(self, timeout):
                events.append(("wait", timeout))
                if len(events) == 1:
                    raise subprocess.TimeoutExpired("mock", timeout)
                return -signal.SIGKILL
        with patch.object(qualify.subprocess, "Popen", return_value=Process()), \
             patch.object(qualify.os, "killpg", side_effect=lambda pid, sig: events.append(("kill", sig))), \
             patch.object(qualify.time, "sleep", side_effect=lambda delay: events.append(("grace", delay))):
            with self.assertRaisesRegex(RuntimeError, "timed out"):
                self.gate.run("timeout", ["mock"], timeout=0.01)
        self.assertEqual(events, [("wait", 0.01), ("kill", signal.SIGTERM), ("grace", 0.2),
                                  ("kill", signal.SIGKILL), ("wait", 2)])
        self.assertEqual(self.gate.steps[-1]["status"], "timeout")

    def test_artifacts_prune_cache_directories_keep_named_files(self):
        (self.directory / "zig-cache").mkdir()
        (self.directory / "zig-cache" / "private-output").write_text("cached")
        (self.directory / "cache-report.txt").write_text("retained")
        (self.directory / "Gen.lean").write_text("/- Thread assignment policy: fallible -/")
        found = qualify.artifacts(self.directory)
        self.assertEqual(sorted(found), ["Gen.lean", "cache-report.txt"])
        self.assertEqual(found["Gen.lean"]["sha256"], qualify.digest(self.directory / "Gen.lean"))

if __name__ == "__main__":
    signal.alarm(10)
    unittest.main()
