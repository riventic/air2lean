#!/usr/bin/env python3
"""Offline only: self-expiring tiny mocks with observed RSS <=32 MiB.
No compiler, translator, native, or network calls. Virtual-memory limits are not
used: the interpreter can reserve more address space than its resident footprint.
"""
import importlib.util
import ctypes
import copy
import errno
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

    def current_record(self, version="0.16.0", abi="gnu"):
        profile = dict(name="abi64-le-v1", target_triple="x86_64-linux.5.10-" + abi,
                       pointer_bits=64, endian="little", abi=abi, zig_version=version,
                       backend="stage2_llvm", cpu="x86_64",
                       features=["64bit", "cmov", "cx8", "fxsr", "idivq_to_divl", "macrofusion",
                                 "mmx", "nopl", "slow_3ops_lea", "slow_incdec", "sse", "sse2",
                                 "vzeroupper", "x87"],
                       build_mode="ReleaseSafe", float_mode="per-instruction", error_set_bits=16,
                       error_layout="type-table", error_tracing=False, export_stage="analyzed-air")
        return dict(schema=12, zig_version=version, target_endian="little", name="worker", profile=profile)

    def test_fresh_versioned_linux_gnu_musl_profiles(self):
        for version in ("0.15.2", "0.16.0"):
            for abi in ("gnu", "musl"):
                record = self.current_record(version, abi)
                self.assertEqual(qualify.fresh_profile([record], version, ["worker"]),
                                 dict(record["profile"], schema=12))

    def test_fresh_schema_endian_inventory_and_profile_fail_closed(self):
        record = self.current_record()
        changes = [("schema", 11), ("zig_version", "0.15.2"), ("target_endian", "big")]
        for key, value in changes:
            bad = copy.deepcopy(record); bad[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                qualify.fresh_profile([bad], "0.16.0", ["worker"])
        for key, value in [("cpu", "haswell"), ("features", []), ("build_mode", "Debug"),
                           ("error_tracing", True), ("backend", "stage2_c"), ("pointer_bits", 32)]:
            bad = copy.deepcopy(record); bad["profile"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                qualify.fresh_profile([bad], "0.16.0", ["worker"])
        for records in ([], [record, record]):
            with self.assertRaises(ValueError):
                qualify.fresh_profile(records, "0.16.0", ["worker"])
        other = self.current_record(abi="musl"); other["name"] = "other"
        with self.assertRaisesRegex(ValueError, "mixed profiles"):
            qualify.fresh_profile([record, other], "0.16.0", ["worker", "other"])

    def test_complete_body_comparison_retains_raw_legacy_receipt(self):
        air = self.directory / "air"; air.mkdir()
        record = dict(schema=11, zig_version="0.16.0", target_endian="little", name="worker")
        (air / "worker.json").write_text(json.dumps(record))
        baseline = self.directory / "baseline.lean"
        body = b"import ZigLean\ndef worker := 7\n-- complete tail\n"
        baseline.write_bytes(body)
        raw = self.directory / "Gen.lean"
        metadata = dict(profile=qualify.HELPERS["profile_for_air"](record),
                        float_semantics="ieee", correspondence="model")
        header = qualify.HELPERS["PREFIX"] + json.dumps(metadata).encode() + b"\n"
        raw.write_bytes(header + body)
        receipt = self.directory / "generated-receipt.json"
        captured = qualify.generated_receipt(raw, air, receipt)
        qualify.HELPERS["compare"](baseline, raw, receipt)
        self.assertEqual(raw.read_bytes(), header + body)
        self.assertEqual(baseline.read_bytes(), body)
        self.assertEqual(captured["generated_sha256"], qualify.digest(raw))
        self.assertEqual(captured["air"], [dict(file="worker.json", sha256=qualify.digest(air / "worker.json"))])
        baseline.write_bytes(body.replace(b"complete tail", b"lost tail"))
        with self.assertRaisesRegex(ValueError, "semantics changed"):
            qualify.HELPERS["compare"](baseline, raw, receipt)
        raw.write_bytes(header + body + b"-- new tail\n")
        with self.assertRaisesRegex(ValueError, "validated check report"):
            qualify.HELPERS["checked_generated"](raw, receipt)
        raw.write_bytes(body)
        with self.assertRaisesRegex(ValueError, "first-line profile"):
            qualify.generated_receipt(raw, air, receipt)
        metadata["profile"]["zig_version"] = "0.15.2"
        raw.write_bytes(qualify.HELPERS["PREFIX"] + json.dumps(metadata).encode() + b"\n" + body)
        with self.assertRaisesRegex(ValueError, "AIR profile differs"):
            qualify.generated_receipt(raw, air, receipt)

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

    def test_darwin_pid_query_requires_exact_terminal_anchor(self):
        class Query:
            def __call__(self, kind, group, buffer, capacity):
                self.arguments = kind, group, capacity
                for index, pid in enumerate(self.pids):
                    buffer[index] = pid
                ctypes.set_errno(self.error)
                return self.size
        query = Query()
        cases = [(4, [12345], 0, True), (0, [], 0, False), (-1, [], errno.EPERM, False),
                 (512, [12345], 0, False), (3, [12345], 0, False),
                 (8, [12345, 999], 0, False), (4, [999], 0, False),
                 (4, [12345], errno.EPERM, False)]
        with replaced(qualify.sys, "platform", "darwin"), \
             replaced(qualify, "peek_status", lambda proc: 0), \
             replaced(qualify.ctypes, "CDLL", lambda *a, **k: SimpleNamespace(proc_listpids=query)):
            for size, pids, error, expected in cases:
                with self.subTest(size=size, pids=pids, error=error):
                    query.size, query.pids, query.error = size, pids, error
                    self.assertEqual(qualify.darwin_exited_anchor_only(SimpleNamespace(pid=12345)), expected)
                    self.assertEqual(query.arguments, (2, 12345, 512))
            query.size, query.pids, query.error, query.arguments = 4, [12345], 0, None
            with replaced(qualify, "peek_status", lambda proc: None):
                self.assertFalse(qualify.darwin_exited_anchor_only(SimpleNamespace(pid=12345)))
                self.assertIsNone(query.arguments)

    def test_darwin_eperm_resolution_precedes_reap(self):
        events = []
        class Process:
            pid = 12345
            def wait(self, timeout):
                events.append("reap")
                return 0
        def denied(pid, sig):
            events.append(sig)
            raise PermissionError(errno.EPERM, "mock zombie group")
        def proof(proc):
            events.append("terminal_anchor_only")
            return True
        with replaced(qualify.sys, "platform", "darwin"), \
             replaced(qualify.os, "killpg", denied), \
             replaced(qualify, "darwin_exited_anchor_only", proof):
            self.assertEqual(qualify.stop_group(Process()), 0)
        self.assertEqual(events, [signal.SIGTERM, signal.SIGKILL, "terminal_anchor_only", "reap"])

    def test_eperm_resolution_fails_closed_without_proof(self):
        class Process:
            pid = 12345
            def wait(self, timeout):
                return 0
        def denied(pid, sig):
            raise PermissionError(errno.EPERM, "mock restriction")
        for platform, proof in [("linux", lambda proc: True), ("darwin", lambda proc: False),
                                ("darwin", lambda proc: (_ for _ in ()).throw(OSError("query failed")))]:
            with self.subTest(platform=platform), replaced(qualify.sys, "platform", platform), \
                 replaced(qualify.os, "killpg", denied), \
                 replaced(qualify, "darwin_exited_anchor_only", proof):
                with self.assertRaisesRegex(RuntimeError, "cleanup"):
                    qualify.stop_group(Process())
        with replaced(qualify.sys, "platform", "darwin"), \
             replaced(qualify.os, "killpg", lambda p, s: (_ for _ in ()).throw(OSError(errno.EINVAL, "bad signal"))), \
             replaced(qualify, "darwin_exited_anchor_only", lambda proc: True):
            with self.assertRaisesRegex(RuntimeError, "cleanup"):
                qualify.stop_group(Process())

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
