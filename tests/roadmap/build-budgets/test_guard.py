#!/usr/bin/env python3
"""Offline guard tests: stdlib Python children only, no compiler probes/builds."""

import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
GUARD = ROOT / "scripts/build-guard.py"
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("build_guard", GUARD)
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)


class GuardTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="air2lean-guard-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.counter = 0

    def command(self, source, *options, cwd=None):
        self.counter += 1
        report = self.root / f"report{self.counter}.json"
        log = self.root / f"log{self.counter}"
        args = [sys.executable, str(GUARD), "--cwd", str(cwd or self.root),
                "--lock", str(self.root / "shared.lock"), "--report", str(report),
                "--log", str(log), "--rss-mib", "32", "--timeout", "5",
                "--interval", "0.02", "--grace", "0.1", *options,
                "--", sys.executable, "-c", source]
        return args, report, log

    def run_guard(self, source, *options):
        args, report, log = self.command(source, *options)
        result = subprocess.run(args, capture_output=True, text=True, timeout=12)
        self.assertTrue(report.is_file(), result.stderr)
        return result, json.loads(report.read_text()), log

    def wait_file(self, path):
        deadline = time.monotonic() + 5
        while not path.exists() and time.monotonic() < deadline:
            time.sleep(0.01)
        self.assertTrue(path.exists(), str(path))

    def live(self, pid):
        return pid in guard.processes()  # zombie descendants have already stopped

    def test_success_evidence_and_bounded_output(self):
        source = 'import os; print(os.environ["LEAN_NUM_THREADS"]); print("x" * 100000)'
        result, report, log = self.run_guard(source, "--log-bytes", "256", "--profile", "mock")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(report["outcome"], "success")
        self.assertTrue(report["log_truncated"])
        self.assertEqual(log.stat().st_size, 256)
        self.assertEqual(report["log_sha256"], guard.digest(log))
        self.assertTrue(log.read_bytes().startswith(b"1\n"))
        self.assertEqual(report["command"], [sys.executable, "-c", source])
        self.assertEqual(report["guard"]["sha256"], guard.digest(GUARD))
        self.assertIn("sha256", report["tools"][0])
        self.assertEqual(report["profile"], "mock")
        self.assertLess(len(json.dumps(report)), 128 * 1024)

    def test_child_failure_and_spawn_failure(self):
        result, report, _ = self.run_guard("raise SystemExit(9)")
        self.assertEqual((result.returncode, report["outcome"], report["child_status"]),
                         (9, "child_failed", 9))
        args, path, _ = self.command("pass")
        args[-3:] = ["/does/not/exist"]
        result = subprocess.run(args, capture_output=True, timeout=12)
        self.assertEqual(result.returncode, 127)
        self.assertEqual(json.loads(path.read_text())["outcome"], "spawn_error")

    def test_timeout_kills_ignoring_child_and_grandchild(self):
        pids = self.root / "pids"
        source = f'''
import os, signal, time
signal.signal(signal.SIGTERM, signal.SIG_IGN)
pid = os.fork()
if pid == 0:
    while True: time.sleep(1)
open({str(pids)!r}, 'w').write(str(os.getpid()) + ' ' + str(pid))
while True: time.sleep(1)
'''
        result, report, _ = self.run_guard(source, "--timeout", "0.3")
        self.assertEqual((result.returncode, report["outcome"]), (124, "timeout"), result.stderr)
        self.assertTrue(all(not self.live(int(pid)) for pid in pids.read_text().split()))
        result, _, _ = self.run_guard("pass")
        self.assertEqual(result.returncode, 0)

    def test_sampled_memory_limit_without_large_allocations(self):
        result, report, _ = self.run_guard("import time; time.sleep(2)", "--rss-mib", "1")
        self.assertEqual((result.returncode, report["outcome"]), (125, "rss_limit"))
        self.assertGreater(report["peak_sampled_rss_kib"], 1024)

    def test_global_lock_across_working_directories_and_cancellation(self):
        ready = self.root / "ready"
        source = f'import pathlib,time; pathlib.Path({str(ready)!r}).touch(); time.sleep(20)'
        args, report, _ = self.command(source)
        first = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.addCleanup(lambda: first.poll() is None and first.kill())
        self.wait_file(ready)
        other = self.root / "other-worktree"
        other.mkdir()
        blocked, blocked_report, _ = self.command("pass", cwd=other)
        result = subprocess.run(blocked, capture_output=True, timeout=12)
        self.assertEqual(result.returncode, 75)
        self.assertEqual(json.loads(blocked_report.read_text())["outcome"], "lock_busy")
        first.send_signal(signal.SIGTERM)
        first.communicate(timeout=12)
        self.assertEqual(first.returncode, 143)
        self.assertEqual(json.loads(report.read_text())["outcome"], "cancelled")
        result, _, _ = self.run_guard("pass")
        self.assertEqual(result.returncode, 0)

    def test_waiting_for_lock_can_be_cancelled_without_spawning(self):
        import fcntl
        with (self.root / "shared.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            marker = self.root / "must-not-run"
            args, path, _ = self.command(f'open({str(marker)!r}, "w").close()', "--lock-wait", "20")
            a = guard.parse_args(args[2:])
            with mock.patch.object(guard.time, "sleep", side_effect=lambda _: os.kill(os.getpid(), signal.SIGINT)):
                report = guard.run(a)
            self.assertEqual(report["exit_code"], 130)
            self.assertFalse(marker.exists())
            self.assertEqual(json.loads(path.read_text())["outcome"], "cancelled")

    def test_orphaned_group_is_stopped(self):
        pidfile = self.root / "orphan"
        source = f'''
import os, time
pid = os.fork()
if pid == 0:
    time.sleep(20)
else:
    open({str(pidfile)!r}, 'w').write(str(pid))
'''
        result, report, _ = self.run_guard(source)
        self.assertEqual((result.returncode, report["outcome"]), (71, "orphaned_children"))
        self.assertFalse(self.live(int(pidfile.read_text())))

    def test_observed_detached_descendant_is_stopped(self):
        pidfile = self.root / "detached"
        source = f'''
import os, time
pid = os.fork()
if pid == 0:
    os.setsid()
    time.sleep(20)
else:
    open({str(pidfile)!r}, 'w').write(str(pid))
    time.sleep(20)
'''
        result, report, _ = self.run_guard(source, "--timeout", "0.4")
        self.assertEqual((result.returncode, report["outcome"]), (124, "timeout"))
        self.assertFalse(self.live(int(pidfile.read_text())))

    def test_observer_failure_cleans_group(self):
        a = guard.parse_args(["--cwd", str(self.root), "--lock", str(self.root / "lock"),
                              "--report", str(self.root / "report.json"), "--log", str(self.root / "log"),
                              "--grace", "0.02", "--", sys.executable, "-c", "import time; time.sleep(20)"])
        with mock.patch.object(guard, "processes", side_effect=RuntimeError("ps failed")):
            report = guard.run(a)
        self.assertEqual(report["exit_code"], 70)
        self.assertEqual(report["outcome"], "cleanup_failed")

    def test_sequential_zig_flags_and_leaf_count(self):
        names = {"zig"}
        self.assertEqual(guard.sequential_command(["zig", "build", "test"], names),
                         ["zig", "build", "-j1", "test"])
        for command in (["zig", "build", "-j2"], ["zig", "build", "-j", "2"],
                        ["zig", "build", "-j"], ["zig", "build", "@options"]):
            with self.assertRaises(ValueError):
                guard.sequential_command(command, names)
        rows = {1: {"parent": 0, "name": "zig"}, 2: {"parent": 1, "name": "zig"}}
        self.assertFalse(guard.parallel_zig(rows, {1, 2}, names))
        rows[3] = {"parent": 1, "name": "zig"}
        self.assertTrue(guard.parallel_zig(rows, {1, 2, 3}, names))

    def test_observed_pid_reuse_is_not_owned(self):
        tree = guard.Tree(10)
        first = {10: {"parent": 1, "group": 10, "start": "old"},
                 11: {"parent": 10, "group": 11, "start": "old"}}
        self.assertEqual(tree.owned(first), {10, 11})
        reused = {11: {"parent": 1, "group": 11, "start": "new"}}
        self.assertEqual(tree.owned(reused), set())

    def test_relative_tool_provenance_uses_workload_directory(self):
        tool = self.root / "bin" / "tool"
        tool.parent.mkdir()
        tool.write_text("unused mock file")
        tool.chmod(0o755)
        self.assertEqual(guard.executable("bin/tool", self.root), str(tool))

    def test_input_and_output_hashes(self):
        source = self.root / "input"
        source.write_text("small fixture")
        result, report, _ = self.run_guard('open("output", "w").write("generated fixture")',
                                            "--input", "input", "--output", "output", "--cache", "warm",
                                            "--phase", "emit")
        self.assertEqual(result.returncode, 0)
        self.assertEqual(report["inputs"][0]["sha256"], guard.digest(source))
        self.assertEqual(report["outputs"][0]["bytes"], len("generated fixture"))
        self.assertEqual(report["cache_label"], "warm")
        self.assertEqual(report["phase"], "emit")

    def test_invalid_evidence_alias_and_nonfinite_limits(self):
        lock = self.root / "lock"
        lock.touch()
        alias = self.root / "alias"
        os.link(lock, alias)
        base = ["--lock", str(lock), "--log", str(alias), "--report", str(self.root / "report"), "--", "mock"]
        with mock.patch("sys.stderr"):
            with self.assertRaises(SystemExit) as error:
                guard.parse_args(base)
            self.assertEqual(error.exception.code, 2)
            for limit in ("nan", "inf", "0", "-1"):
                with self.assertRaises(SystemExit):
                    guard.parse_args(["--timeout", limit, *base])

    def test_special_files_cannot_block_evidence_or_lock_setup(self):
        fifo = self.root / "fifo"
        os.mkfifo(fifo)
        self.assertEqual(guard.file_evidence(fifo)["unavailable"], "not a regular file")
        with mock.patch("sys.stderr"):
            with self.assertRaises(SystemExit):
                guard.parse_args(["--lock", str(fifo), "--log", str(self.root / "log"),
                                  "--report", str(self.root / "report"), "--", "mock"])


if __name__ == "__main__":
    unittest.main()
