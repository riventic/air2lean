#!/usr/bin/env python3
"""Offline only: self-expiring tiny mocks with observed RSS <=32 MiB.
No compiler, translator, native, or network calls. Virtual-memory limits are not
used: the interpreter can reserve more address space than its resident footprint.
"""
import importlib.util
import ctypes
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
sys.dont_write_bytecode = True
from contextlib import contextmanager

@contextmanager
def replaced(target, name, value):
    original = getattr(target, name)
    setattr(target, name, value)
    try:
        yield
    finally:
        setattr(target, name, original)

spec = importlib.util.spec_from_file_location("spawn_qualify", Path(__file__).with_name("qualify.py"))
qualify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(qualify)

class HarnessTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.directory = Path(self.temporary.name)
        self.gate = qualify.Gate(self.directory)
        # The execution sandbox may forbid killpg even for our own children.
        # Group signals are mocked; every real tiny child expires independently.
        self.original_killpg = qualify.os.killpg
        qualify.os.killpg = lambda pid, sig: None

    def tearDown(self):
        qualify.os.killpg = self.original_killpg
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

    def process_events(self, program, label, **kwargs):
        events = []
        real_popen = subprocess.Popen
        def start(*args, **options):
            proc = real_popen(*args, **options)
            real_wait = proc.wait
            def reap(*args, **options):
                self.assertEqual(events[-1], signal.SIGKILL)
                events.append("reap")
                return real_wait(*args, **options)
            proc.wait = reap
            return proc
        def kill(pid, sig):
            events.append(sig)
            return None
        with replaced(qualify.subprocess, "Popen", start), \
             replaced(qualify.os, "killpg", kill):
            try:
                self.gate.run(label, [sys.executable, "-c", "import resource,signal,sys; signal.alarm(2); rss=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss; assert (rss if sys.platform == 'darwin' else rss*1024) <= 32*1024*1024; " + program], **kwargs)
            finally:
                self.assertEqual(events, [signal.SIGTERM, signal.SIGKILL, "reap"])

    def test_timeout_group_killed_before_reaping(self):
        with self.assertRaisesRegex(RuntimeError, "timeout"):
            self.process_events("import time; time.sleep(1)", "timeout", timeout=0.03)
        self.assertEqual(self.gate.steps[-1]["status"], "timeout")

    def closed_output(self, label, duration, timeout):
        scans = []
        real_peek = qualify.peek_status
        def peek(proc):
            scans.append(1)
            return real_peek(proc)
        with replaced(qualify, "peek_status", peek):
            try:
                self.process_events("import os,time; os.close(1); os.close(2); time.sleep(" +
                                    str(duration) + ")", label, timeout=timeout)
            finally:
                self.assertLessEqual(len(scans), 32)
                self.assertGreater(len(scans), 0)

    def test_closed_output_live_child_completes_without_spinning(self):
        self.closed_output("closed-pass", 0.08, 0.7)
        self.assertEqual(self.gate.steps[-1]["status"], "passed")

    def test_closed_output_live_child_retains_deadline(self):
        with self.assertRaisesRegex(RuntimeError, "timeout"):
            self.closed_output("closed-timeout", 0.15, 0.06)
        self.assertEqual(self.gate.steps[-1]["status"], "timeout")

    def test_cleanup_failure_is_not_retried_after_reap(self):
        calls = []
        real_stop = qualify.stop_group
        def fail_after_cleanup(proc):
            calls.append(1)
            real_stop(proc)
            raise RuntimeError("mock cleanup failure")
        with replaced(qualify, "stop_group", fail_after_cleanup):
            with self.assertRaisesRegex(RuntimeError, "process cleanup failed"):
                self.gate.run("cleanup-failed", self.tiny("PASS"), timeout=1)
        self.assertEqual(calls, [1])
        self.assertEqual(self.gate.steps[-1]["status"], "cleanup_failed")

    def test_signal_interruption_preserves_anchor(self):
        with self.assertRaisesRegex(RuntimeError, "interrupted"):
            self.process_events("import os,time; os.kill(os.getppid(),signal.SIGTERM); time.sleep(1)",
                                "signal", timeout=1)
        self.assertEqual(self.gate.steps[-1]["status"], "interrupted")

    def test_exited_leader_descendant_is_stopped(self):
        events = []
        descendants = {"alive": True}
        reader, writer = os.pipe()
        os.write(writer, b"PASS\n")
        os.close(writer)
        class Process:
            pid = 12345
            stdout = os.fdopen(reader, "rb")
            def wait(self, timeout):
                self_test.assertFalse(descendants["alive"])
                events.append("reap")
                return 0
        self_test = self
        def peek(proc):
            events.append("observe_exited_unreaped")
            return 0
        def kill(pid, sig):
            events.append(sig)
            if sig == signal.SIGKILL:
                descendants["alive"] = False
        with replaced(qualify.subprocess, "Popen", lambda *args, **kwargs: Process()), \
             replaced(qualify, "peek_status", peek), \
             replaced(qualify.os, "killpg", kill):
            self.gate.run("descendant", ["mock"], marker="PASS", timeout=1)
        self.assertEqual(events, ["observe_exited_unreaped", signal.SIGTERM, signal.SIGKILL, "reap"])
        self.assertEqual(self.gate.steps[-1]["status"], "passed")

    def test_output_cap_rejects_while_process_runs(self):
        with self.assertRaisesRegex(RuntimeError, "oversized_log"):
            self.process_events("import os,time; os.write(1,b'x'*4096); time.sleep(1)",
                                "output", timeout=1, log_limit=1024)
        self.assertEqual((self.directory / "output.log").stat().st_size, 1024)
        self.assertEqual(self.gate.steps[-1]["status"], "oversized_log")

    def test_cleanup_failure_still_attempts_kill_and_bounded_reap(self):
        events = []
        class Process:
            pid = 12345
            def wait(self, timeout):
                events.append("reap")
                self_test.assertGreaterEqual(timeout, 0)
                self_test.assertLessEqual(timeout, 2)
                return 0
        self_test = self
        def denied(pid, sig):
            events.append(sig)
            raise PermissionError("mock restriction")
        with replaced(qualify.os, "killpg", denied):
            with self.assertRaisesRegex(RuntimeError, "cleanup"):
                qualify.stop_group(Process())
        self.assertEqual(events, [signal.SIGTERM, signal.SIGKILL, "reap"])

    def test_darwin_native_nonreaping_status(self):
        class NativeWaitid:
            def __call__(self, kind, pid, buffer, flags):
                self.arguments = kind, pid, flags
                fields = (ctypes.c_int32 * 6).from_buffer(buffer)
                fields[2], fields[3], fields[5] = 1, pid, 7
                return 0
        native = NativeWaitid()
        with replaced(qualify, "os", SimpleNamespace()), \
             replaced(qualify.sys, "platform", "darwin"), \
             replaced(qualify.ctypes, "CDLL", lambda *args, **kwargs: SimpleNamespace(waitid=native)):
            self.assertEqual(qualify.peek_status(SimpleNamespace(pid=12345)), 7)
        self.assertEqual(native.arguments, (1, 12345, 0x25))

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
