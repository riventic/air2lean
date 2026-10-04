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
        self.root = Path(self.temporary.name).resolve()
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
        evidence = json.loads(blocked_report.read_text())
        self.assertEqual(evidence["outcome"], "lock_busy")
        for key in ("command", "guard", "revision", "inputs", "tools", "pins", "environment_overrides"):
            self.assertNotIn(key, evidence)
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
        self.assertTrue(report["drain_incomplete"])
        self.assertTrue(report["log_truncated"])

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
        alias = "zig-very-long-configured-alias"
        rows[2]["name"] = rows[3]["name"] = alias[:15]
        self.assertTrue(guard.parallel_zig(rows, {1, 2, 3}, {alias}))
        self.assertEqual(guard.sequential_command(["zig", "build", "--prefix", "-j1"], names),
                         ["zig", "build", "-j1", "--prefix", "-j1"])
        self.assertEqual(guard.sequential_command(["zig", "build", "run", "--", "-j1", "-j2"], names),
                         ["zig", "build", "-j1", "run", "--", "-j1", "-j2"])
        with self.assertRaises(ValueError):
            guard.sequential_command(["zig", "build", "--prefix", "-j1", "-j2"], names)

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

    def test_fingerprints_are_collected_after_the_waiting_lock_is_acquired(self):
        import fcntl
        fixture = self.root / "input"
        fixture.write_text("before")
        args, _, _ = self.command("pass", "--input", "input", "--lock-wait", "2")
        a = guard.parse_args(args[2:])
        original_flock = fcntl.flock
        original_evidence = guard.file_evidence
        with a.lock.open("a") as owner:
            original_flock(owner, fcntl.LOCK_EX)
            acquired = [False]
            def finish_previous(_duration):
                fixture.write_text("after")
                original_flock(owner, fcntl.LOCK_UN)
                acquired[0] = True
            def evidence(*args, **kwargs):
                self.assertTrue(acquired[0])
                return original_evidence(*args, **kwargs)
            with mock.patch.object(guard.time, "sleep", side_effect=finish_previous), \
                    mock.patch.object(guard, "file_evidence", side_effect=evidence), \
                    mock.patch.object(guard, "revision", side_effect=lambda _: {"head": "after"} if acquired[0] else self.fail("early revision")):
                report = guard.run(a)
        self.assertEqual(report["exit_code"], 0)
        self.assertEqual(report["inputs"][0]["sha256"], guard.digest(fixture))
        self.assertEqual(report["revision"]["head"], "after")

    def test_fingerprint_cache_keeps_duplicate_entries_and_fresh_outputs(self):
        fixture = self.root / "input"
        fixture.write_text("before")
        alias = self.root / "alias"
        os.link(fixture, alias)
        args, _, _ = self.command('open("input", "w").write("after")', "--input", "input",
                                  "--input", "alias", "--output", "input", "--tool", sys.executable)
        with mock.patch.object(guard, "digest", wraps=guard.digest) as digests:
            report = guard.run(guard.parse_args(args[2:]))
        self.assertEqual(report["exit_code"], 0)
        fixture_calls = [call for call in digests.call_args_list if Path(call.args[0]).resolve() in (fixture, alias)]
        python_calls = [call for call in digests.call_args_list if Path(call.args[0]).resolve() == Path(sys.executable).resolve()]
        self.assertEqual(len(fixture_calls), 2)  # initial inode once, post-execution output once
        self.assertEqual(len(python_calls), 1)
        self.assertEqual([item["path"] for item in report["inputs"]], [str(fixture), str(alias)])
        self.assertEqual(report["inputs"][0]["sha256"], report["inputs"][1]["sha256"])
        self.assertNotEqual(report["inputs"][0]["sha256"], report["outputs"][0]["sha256"])

    def test_cleanup_fallback_signals_after_leader_exit_without_reaping(self):
        pidfile = self.root / "survivor"
        source = f'''
import os, signal, time
signal.signal(signal.SIGTERM, signal.SIG_IGN)
pid = os.fork()
if pid == 0:
    while True: time.sleep(1)
open({str(pidfile)!r}, 'w').write(str(pid))
os._exit(0)
'''
        child = subprocess.Popen([sys.executable, "-c", source], start_new_session=True)
        tree = guard.Tree(child.pid)
        def cleanup():
            guard.stop_tree(child, tree, 0.01)
            child.wait(timeout=5)
        self.addCleanup(cleanup)
        self.wait_file(pidfile)
        deadline = time.monotonic() + 5
        while guard.peek_status(child) is None and time.monotonic() < deadline:
            time.sleep(0.01)
        self.assertEqual(guard.peek_status(child), 0)
        with mock.patch.object(guard, "processes", side_effect=RuntimeError("ps failed")), \
                mock.patch.object(guard.os, "killpg", wraps=os.killpg) as signals:
            self.assertFalse(guard.stop_tree(child, tree, 0.03))
        self.assertEqual([call.args for call in signals.call_args_list],
                         [(child.pid, signal.SIGTERM), (child.pid, signal.SIGKILL)])
        self.assertIsNone(child.returncode)  # retain the PID anchor until final cleanup
        child.wait(timeout=5)
        deadline = time.monotonic() + 5
        while self.live(int(pidfile.read_text())) and time.monotonic() < deadline:
            time.sleep(0.01)
        self.assertFalse(self.live(int(pidfile.read_text())))

    def test_final_cleanup_only_skips_a_confirmed_empty_tree(self):
        args, _, _ = self.command("pass")
        with mock.patch.object(guard, "stop_tree", wraps=guard.stop_tree) as stops:
            self.assertEqual(guard.run(guard.parse_args(args[2:]))["exit_code"], 0)
            self.assertEqual(stops.call_count, 0)
        args, _, _ = self.command("import time; time.sleep(20)", "--timeout", "0.1")
        with mock.patch.object(guard, "stop_tree", wraps=guard.stop_tree) as stops:
            self.assertEqual(guard.run(guard.parse_args(args[2:]))["exit_code"], 124)
            self.assertEqual(stops.call_count, 1)
        args, _, _ = self.command("import time; time.sleep(20)", "--timeout", "0.1")
        original_stop = guard.stop_tree
        results = []
        def uncertain_once(*args):
            result = original_stop(*args)
            results.append(result)
            return False if len(results) == 1 else result
        with mock.patch.object(guard, "stop_tree", side_effect=uncertain_once) as stops:
            report = guard.run(guard.parse_args(args[2:]))
            self.assertEqual(report["exit_code"], 124)
            self.assertEqual(stops.call_count, 2)
            self.assertEqual(results, [True, True])

    def test_truncated_alias_leaves_trigger_workload_termination(self):
        alias = "zig-long-configured-compiler"
        args, _, _ = self.command("import time; time.sleep(20)", "--zig-name", alias)
        original_processes = guard.processes
        def sampled_leaves():
            rows = original_processes()
            leaders = [pid for pid, row in rows.items()
                       if row["parent"] == os.getpid() and row["group"] == pid]
            if leaders:
                leader = leaders[0]
                rows[leader]["name"] = "driver"
                for pid in (-1, -2):
                    rows[pid] = {"parent": leader, "group": leader, "start": "mock",
                                 "name": alias[:15], "rss_kib": 0}
            return rows
        with mock.patch.object(guard, "processes", side_effect=sampled_leaves):
            report = guard.run(guard.parse_args(args[2:]))
        self.assertEqual((report["exit_code"], report["outcome"]), (126, "parallel_zig"))
        self.assertLess(report["child_status"], 0)

    def test_chunk_limits_cover_zero_exact_and_discarded_output(self):
        import io
        for limit in (0, 3, 4):
            output = io.BytesIO()
            report = {"output_bytes": 0}
            guard.write_chunk(output, report, limit, b"abc")
            guard.write_chunk(output, report, limit, b"d")
            self.assertEqual(output.getvalue(), b"abcd"[:limit])
            self.assertEqual(report["output_bytes"], 4)

    def test_final_drain_is_bounded_with_an_infinite_read_provider(self):
        import io
        report = {"output_bytes": 0}
        output = io.BytesIO()
        with mock.patch.object(guard.os, "read", return_value=b"abc") as reads, \
                mock.patch.object(guard.time, "monotonic", return_value=0):
            self.assertTrue(guard.drain_pipe(99, output, report, 3, lambda: False, 1))
        self.assertEqual(reads.call_count, 16)
        self.assertEqual(report["output_bytes"], 48)
        self.assertEqual(output.getvalue(), b"abc")
        for cancelled, deadline in ((True, 1), (False, 0)):
            with mock.patch.object(guard.os, "read", return_value=b"abc") as reads, \
                    mock.patch.object(guard.time, "monotonic", return_value=0):
                self.assertTrue(guard.drain_pipe(99, output, report, 3, lambda: cancelled, deadline))
                self.assertEqual(reads.call_count, 0)
        with mock.patch.object(guard.os, "read", return_value=b""):
            self.assertFalse(guard.drain_pipe(99, output, report, 3, lambda: False, time.monotonic() + 1))

    def test_incomplete_final_drain_still_reports_and_releases_the_lock(self):
        args, path, log = self.command("pass", "--log-bytes", "64")
        original_drain = guard.drain_pipe
        def replenished_pipe(*args):
            with mock.patch.object(guard.os, "read", return_value=b"x" * 65536), \
                    mock.patch.object(guard.time, "monotonic", return_value=0):
                return original_drain(*args)
        with mock.patch.object(guard, "drain_pipe", side_effect=replenished_pipe):
            report = guard.run(guard.parse_args(args[2:]))
        self.assertEqual(report["exit_code"], 0)
        self.assertTrue(report["drain_incomplete"])
        self.assertTrue(report["log_truncated"])
        self.assertEqual(report["output_bytes"], 16 * 65536)
        self.assertEqual(log.stat().st_size, 64)
        self.assertEqual(json.loads(path.read_text())["output_bytes"], report["output_bytes"])
        result, _, _ = self.run_guard("pass")
        self.assertEqual(result.returncode, 0)

    def test_pinned_frontend_stage_contracts(self):
        # Operand-consuming branches in each official pinned cmdBuild. This
        # models the external frontend, not build_runner's later argument pass.
        common = {"--build-file", "--zig-lib-dir", "--build-runner", "--cache-dir",
                  "--global-cache-dir", "--system", "--debug-log", "--debug-target",
                  "--color", "--seed"}
        versions = {"0.14.1": common, "0.15.2": common | {"--debug-libc"},
                    "0.16.0": common | {"--debug-libc"}}
        self.assertEqual(guard.FRONTEND_VALUES, set.intersection(*versions.values()))
        self.assertEqual(set(guard.FRONTEND_STAGES), {frozenset(values) for values in versions.values()})
        def frontend_jobs(arguments, operands):
            jobs = None
            i = 0
            while i < len(arguments):
                arg = arguments[i]
                if arg in operands:
                    i += 2
                    continue
                if arg == "--":
                    break
                if arg.startswith("-j"):
                    jobs = int(arg[2:])
                i += 1
            return jobs
        dangerous = (["--prefix", "-j2"], ["--sysroot", "-j2"],
                     ["--prefix", "--", "-j2"], ["--prefix", "@flags"],
                     ["--build-file", "@flags"], ["--debug-libc", "-j2"],
                     ["--debug-libc", "--", "-j2"])
        for suffix in dangerous:
            with self.subTest(suffix=suffix):
                with self.assertRaises(ValueError):
                    guard.sequential_command(["zig", "build", *suffix], {"zig"})
        accepted = (["--prefix", "-j1"], ["--sysroot", "root"],
                    ["--build-file", "-j2"], ["run", "--", "-j2", "@application"],
                    ["--build-file", "--", "run", "--", "-j2"])
        for version, operands in versions.items():
            for suffix in accepted:
                with self.subTest(version=version, suffix=suffix):
                    command = guard.sequential_command(["zig", "build", *suffix], {"zig"})
                    self.assertEqual(command[2], "-j1")
                    self.assertEqual(command[3:], list(suffix))
                    self.assertEqual(frontend_jobs(command[2:], operands), 1)


if __name__ == "__main__":
    unittest.main()
