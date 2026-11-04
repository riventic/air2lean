#!/usr/bin/env python3
"""Offline guard tests: stdlib Python children only, no compiler probes/builds."""

import contextlib
import fcntl
import importlib.util
import io
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

# Longer than the coordinator's 12-second timeout and bounded PID waits. Tests
# assert removal before this deadline; expiry only protects a broken harness.
FIXTURE_LIFETIME = 30


class GuardTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="air2lean-guard-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.counter = 0
        self.fixture_counter = 0
        # A coordinator running these under its merge lane must not move the guards under test.
        environment = mock.patch.dict(os.environ)
        environment.start()
        self.addCleanup(environment.stop)
        os.environ.pop("AIR2LEAN_GUARD_PRIORITY", None)
        os.environ.pop("AIR2LEAN_GUARD_IDLE_MINUTES", None)

    def fixture_source(self, source, lifetime=FIXTURE_LIFETIME):
        self.fixture_counter += 1
        token = str(self.root / f"owned-fixture-{self.fixture_counter}")
        self.addCleanup(self.cleanup_fixture, token)
        support = f'''import time
fixture_token = {token!r}
fixture_deadline = time.monotonic() + {lifetime!r}
def fixture_pause():
    while True:
        remaining = fixture_deadline - time.monotonic()
        if remaining <= 0:
            return
        time.sleep(remaining)
'''
        # Keep ps's command field on one line, including after fork/setsid.
        return f"exec({(support + source)!r})"

    def cleanup_fixture(self, token):
        # Independent of every guard observer/cleanup function under test. A
        # fresh, unique command token identifies even reparented/detached forks;
        # never signal the test runner's own process group.
        for _ in range(3):
            rows = subprocess.run(["ps", "-axo", "pid=,pgid=,stat=,command="],
                                  capture_output=True, text=True, check=True,
                                  timeout=2, env={**os.environ, "LC_ALL": "C"})
            groups = set()
            for line in rows.stdout.splitlines():
                fields = line.split(None, 3)
                if len(fields) == 4 and token in fields[3] and not fields[2].startswith("Z"):
                    group = int(fields[1])
                    if group > 0 and group != os.getpgrp():
                        groups.add(group)
            if not groups:
                return
            for group in groups:
                try:
                    os.killpg(group, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            time.sleep(0.01)
        self.fail("test-owned fixture survived independent cleanup")

    def cleanup_process(self, child):
        if child.poll() is None:
            child.kill()
        child.communicate(timeout=2)

    def command(self, source, *options, cwd=None):
        self.counter += 1
        report = self.root / f"report{self.counter}.json"
        log = self.root / f"log{self.counter}"
        if "fixture_pause()" in source:
            source = self.fixture_source(source)
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
        self.assertEqual(report["environment_overrides"]["AIR2LEAN_JOBS"], "1")

    def test_jobs_and_lean_threads_are_explicit_and_recorded(self):
        source = ('import os; print(os.environ["LEAN_NUM_THREADS"], os.environ["AIR2LEAN_JOBS"], '
                  'os.environ["AIR2LEAN_MEM_MIB"])')
        result, report, log = self.run_guard(source, "--jobs", "3", "--lean-threads", "2")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(log.read_text(), "2 3 32\n")
        self.assertEqual((report["budget"]["jobs"], report["budget"]["lean_threads"]), (3, 2))
        self.assertEqual(report["environment_overrides"]["LEAN_NUM_THREADS"], "2")
        for bad in (("--jobs", "0"), ("--lean-threads", "0"), ("--jobs", "257")):
            with self.assertRaises(SystemExit):
                guard.parse_args([*bad, "--report", "r.json", "--log", "l.log", "--", "true"])

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
    fixture_pause()
    os._exit(0)
open({str(pids)!r}, 'w').write(str(os.getpid()) + ' ' + str(pid))
fixture_pause()
'''
        started = time.monotonic()
        result, report, _ = self.run_guard(source, "--timeout", "0.3")
        self.assertEqual((result.returncode, report["outcome"]), (124, "timeout"), result.stderr)
        self.assertTrue(all(not self.live(int(pid)) for pid in pids.read_text().split()))
        self.assertLess(time.monotonic() - started, FIXTURE_LIFETIME)
        result, _, _ = self.run_guard("pass")
        self.assertEqual(result.returncode, 0)

    def test_fixture_self_expiry_is_inherited_by_forks(self):
        pids = self.root / "expiry-pids"
        source = self.fixture_source(f'''
import os, signal
signal.signal(signal.SIGTERM, signal.SIG_IGN)
pid = os.fork()
if pid == 0:
    fixture_pause()
    os._exit(0)
open({str(pids)!r}, 'w').write(str(os.getpid()) + ' ' + str(pid))
fixture_pause()
''', lifetime=0.15)
        child = subprocess.Popen([sys.executable, "-c", source], start_new_session=True)
        self.addCleanup(self.cleanup_process, child)
        self.wait_file(pids)
        child.wait(timeout=2)
        deadline = time.monotonic() + 2
        while any(self.live(int(pid)) for pid in pids.read_text().split()) and time.monotonic() < deadline:
            time.sleep(0.01)
        self.assertTrue(all(not self.live(int(pid)) for pid in pids.read_text().split()))

    def test_independent_fixture_cleanup_survives_coordinator_crash(self):
        pids = self.root / "crash-pids"
        args, _, _ = self.command(f'''
import os, signal
signal.signal(signal.SIGTERM, signal.SIG_IGN)
pid = os.fork()
if pid == 0:
    os.setsid()
    fixture_pause()
    os._exit(0)
open({str(pids)!r}, 'w').write(str(os.getpid()) + ' ' + str(pid))
fixture_pause()
''')
        token = str(self.root / f"owned-fixture-{self.fixture_counter}")
        started = time.monotonic()
        coordinator = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.addCleanup(self.cleanup_process, coordinator)
        self.wait_file(pids)
        coordinator.kill()
        coordinator.communicate(timeout=2)
        self.assertTrue(all(self.live(int(pid)) for pid in pids.read_text().split()))
        with mock.patch.object(guard, "stop_tree", side_effect=AssertionError("cleanup under test")), \
                mock.patch.object(guard, "processes", side_effect=AssertionError("observer under test")):
            self.cleanup_fixture(token)
        self.assertTrue(all(not self.live(int(pid)) for pid in pids.read_text().split()))
        self.assertLess(time.monotonic() - started, FIXTURE_LIFETIME)

    def test_idle_limit_stops_a_workload_without_cpu_progress(self):
        started = time.monotonic()
        result, report, _ = self.run_guard("fixture_pause()", "--idle-minutes", "0.02")
        self.assertEqual((result.returncode, report["outcome"]), (123, "hung"), result.stderr)
        self.assertEqual(report["budget"]["idle_minutes"], 0.02)
        self.assertLess(time.monotonic() - started, FIXTURE_LIFETIME)

    def test_idle_limit_spares_a_workload_that_computes(self):
        # 6 s of silent computing against a 3 s limit and a 1 s step: each window needs a third
        # of a core, and Linux ps counts whole seconds.
        source = "import time\nend = time.monotonic() + 6\nwhile time.monotonic() < end: pass"
        result, report, _ = self.run_guard(source, "--idle-minutes", "0.05", "--timeout", "10")
        self.assertEqual((result.returncode, report["outcome"]), (0, "success"), result.stderr)

    def test_idle_limit_comes_from_the_environment_or_is_off(self):
        os.environ["AIR2LEAN_GUARD_IDLE_MINUTES"] = "0.02"
        result, report, _ = self.run_guard("fixture_pause()")
        self.assertEqual((result.returncode, report["outcome"]), (123, "hung"), result.stderr)
        os.environ["AIR2LEAN_GUARD_IDLE_MINUTES"] = "soon"
        result = subprocess.run(self.command("pass")[0], capture_output=True, text=True, timeout=12)
        self.assertEqual(result.returncode, 2)
        del os.environ["AIR2LEAN_GUARD_IDLE_MINUTES"]
        result, report, _ = self.run_guard("import time; time.sleep(1.5)")
        self.assertEqual((result.returncode, report["budget"]["idle_minutes"]), (0, 0))

    def test_progress_is_a_started_process_output_or_cpu_time(self):
        rows = {1: {"start": "a", "cpu_s": 5.0}, 2: {"start": "a", "cpu_s": 0.0}}
        progress = guard.Progress(60, 0)
        self.assertFalse(progress.hung(rows, {1, 2}, 0, 1))  # both started: progress
        self.assertEqual(progress.since, 1)
        rows[1]["cpu_s"] = 5.5
        self.assertFalse(progress.hung(rows, {1, 2}, 0, 30))  # 0.5 s of CPU: under the 1 s step
        self.assertEqual(progress.since, 1)
        del rows[1]  # an ended process takes nothing back
        rows[2]["cpu_s"] = 0.6
        self.assertFalse(progress.hung(rows, {2}, 0, 40))  # 0.5 + 0.6 s reach the step
        self.assertEqual(progress.since, 40)
        self.assertFalse(progress.hung(rows, {2}, 7, 90))  # output
        self.assertEqual(progress.since, 90)
        rows[2] = {"start": "b", "cpu_s": 0.0}  # PID reuse: a started process
        self.assertFalse(progress.hung(rows, {2}, 7, 149))
        self.assertEqual(progress.since, 149)
        self.assertTrue(progress.hung(rows, {2}, 7, 209))
        self.assertEqual([guard.cpu_seconds(text) for text in ("0:01.50", "01:02:03", "2-00:00:01")],
                         [1.5, 3723.0, 172801.0])

    def test_sampled_memory_limit_without_large_allocations(self):
        result, report, _ = self.run_guard("import time; time.sleep(2)", "--rss-mib", "1")
        self.assertEqual((result.returncode, report["outcome"]), (125, "rss_limit"))
        self.assertGreater(report["peak_sampled_rss_kib"], 1024)

    def start_holder(self, *options, cwd=None):
        """A guarded workload that holds its admission until cancelled."""
        ready = self.root / f"ready{self.counter + 1}"
        source = f'import pathlib; pathlib.Path({str(ready)!r}).touch(); fixture_pause()'
        args, report, _ = self.command(source, *options, cwd=cwd)
        holder = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.addCleanup(self.cleanup_process, holder)
        self.wait_file(ready)
        return holder, report

    def attempt(self, *options, cwd=None):
        """Exit code and report of a guarded `pass` that may not wait for admission."""
        args, report, _ = self.command("pass", *options, cwd=cwd)
        result = subprocess.run(args, capture_output=True, timeout=12)
        return result.returncode, json.loads(report.read_text())

    def worktree(self, name):
        path = self.root / name
        path.mkdir(exist_ok=True)
        return path

    def test_global_lock_across_working_directories_and_cancellation(self):
        # One slot (budget 1 GiB, weight 1): the second worktree waits for the first.
        first, report = self.start_holder("--mem-budget-mib", "1024")
        code, evidence = self.attempt("--mem-budget-mib", "1024", cwd=self.worktree("other-worktree"))
        self.assertEqual(code, 75)
        self.assertEqual(evidence["outcome"], "lock_busy")
        for key in ("command", "guard", "revision", "inputs", "tools", "pins", "environment_overrides"):
            self.assertNotIn(key, evidence)
        first.send_signal(signal.SIGTERM)
        first.communicate(timeout=12)
        self.assertEqual(first.returncode, 143)
        self.assertEqual(json.loads(report.read_text())["outcome"], "cancelled")
        result, _, _ = self.run_guard("pass")
        self.assertEqual(result.returncode, 0)

    def test_memory_slots_admit_worktrees_while_the_budget_allows(self):
        # Budget 3 GiB; weights 1 (rss 32 MiB) and 2 (rss 1025 MiB).
        budget = ("--mem-budget-mib", "3072")
        self.start_holder(*budget)
        code, evidence = self.attempt(*budget, "--rss-mib", "1025", cwd=self.worktree("b"))
        self.assertEqual((code, evidence["outcome"]), (0, "success"))
        self.assertEqual((evidence["admission"]["capacity"], evidence["admission"]["weight"]), (3, 2))
        self.start_holder(*budget, "--rss-mib", "1025", cwd=self.worktree("c"))
        code, evidence = self.attempt(*budget, cwd=self.worktree("d"))
        self.assertEqual((code, evidence["outcome"]), (75, "lock_busy"))  # all 3 slots held

    def test_one_build_per_workspace_unless_shared(self):
        budget = ("--mem-budget-mib", "8192")
        self.start_holder(*budget)
        code, evidence = self.attempt(*budget)
        self.assertEqual((code, evidence["outcome"]), (75, "lock_busy"))
        self.assertEqual(evidence["admission"]["workspace"], str(self.root))
        code, _ = self.attempt(*budget, "--shared-workspace")
        self.assertEqual(code, 75)  # an exclusive workload of the workspace is running
        other = self.worktree("other")
        self.start_holder(*budget, "--shared-workspace", cwd=other)
        code, _ = self.attempt(*budget, "--shared-workspace", cwd=other)
        self.assertEqual(code, 0)
        code, _ = self.attempt(*budget, cwd=other)
        self.assertEqual(code, 75)

    def test_workspace_is_the_git_top_level(self):
        repo = self.worktree("repo")
        subprocess.run(["git", "init", "-q", str(repo)], check=True)
        (repo / "tests" / "diff").mkdir(parents=True)
        self.assertEqual(guard.workspace(repo / "tests" / "diff"), repo.resolve())
        self.assertEqual(guard.workspace(self.root), self.root)

    def test_exclusive_runs_alone(self):
        budget = ("--mem-budget-mib", "8192")
        holder, _ = self.start_holder(*budget)
        code, _ = self.attempt(*budget, "--exclusive", cwd=self.worktree("x"))
        self.assertEqual(code, 75)
        holder.send_signal(signal.SIGTERM)
        holder.communicate(timeout=12)
        self.start_holder(*budget, "--exclusive", cwd=self.worktree("y"))
        code, _ = self.attempt(*budget, cwd=self.worktree("z"))
        self.assertEqual(code, 75)

    def test_every_lake_of_a_workload_runs_in_one_cache_mode(self):
        # The regression of 2026-10-20 (main, alloc-fba): a plain `lake` beside `cas.py run` rebuilt
        # root modules inside a compiler-owned audit binding.
        source = 'import os; print(os.environ.get("LAKE_ARTIFACT_CACHE"), os.environ.get("LAKE_CACHE_DIR"))'
        os.environ.pop("AIR2LEAN_CAS_DIR", None)
        for key in ("LAKE_ARTIFACT_CACHE", "LAKE_CACHE_DIR", "LAKE_RESTORE_ARTIFACTS"):
            os.environ.pop(key, None)
        result, report, log = self.run_guard(source)
        self.assertEqual(log.read_text(), "None None\n", result.stderr)
        self.assertNotIn("LAKE_ARTIFACT_CACHE", report["environment_overrides"])
        os.environ["AIR2LEAN_CAS_DIR"] = str(self.root / "cas")
        result, report, log = self.run_guard(source)
        self.assertEqual(log.read_text(), "true %s\n" % (self.root / "cas" / "lake"), result.stderr)
        self.assertEqual(report["environment_overrides"]["LAKE_ARTIFACT_CACHE"], "true")

    def test_guard_mode_is_exported_and_recorded(self):
        for options, mode in (((), "shared"), (("--exclusive",), "exclusive")):
            result, report, log = self.run_guard('import os; print(os.environ["AIR2LEAN_GUARD_MODE"])', *options)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(log.read_text(), mode + "\n")
            self.assertEqual(report["environment_overrides"]["AIR2LEAN_GUARD_MODE"], mode)
            self.assertEqual(report["admission"]["exclusive"], bool(options))

    def nested(self, outer, inner):
        """A guard (options `outer`) whose workload runs a guard (options `inner`) of the same
        lock and workspace; returns (outer exit, outer report, inner report)."""
        inner_args, inner_report, _ = self.command("pass", *inner)
        source = "import subprocess, sys; sys.exit(subprocess.run(%r).returncode)" % inner_args
        result, report, _ = self.run_guard(source, *outer)
        return result.returncode, report, json.loads(inner_report.read_text())

    def test_a_nested_guard_inherits_the_enclosing_admission(self):
        # One slot: without inheritance the inner guard waits for the slot and the workspace
        # its ancestor holds (lock_busy at --lock-wait 0).
        code, report, inner = self.nested(("--mem-budget-mib", "1024", "--rss-mib", "512"), ("--mem-budget-mib", "1024"))
        self.assertEqual(code, 0)
        self.assertEqual(inner["outcome"], "success")
        self.assertEqual(inner["admission"]["inherited_from"]["pid"], json.loads(
            report["environment_overrides"][guard.INHERIT])["pid"])
        self.assertNotIn("inherited_from", report["admission"])

    def test_a_nested_guard_that_cannot_inherit_fails_instead_of_waiting(self):
        for inner, reason in ((("--rss-mib", "1024"), "exceeds"), (("--exclusive",), "--exclusive")):
            code, _, report = self.nested(("--rss-mib", "512"), inner)
            self.assertEqual(code, 75)
            self.assertEqual(report["outcome"], "inheritance_refused")
            self.assertIn(reason, report["error"])
        # Another workspace (another checkout) is admitted on its own, as before.
        inner_args, inner_report, _ = self.command("pass", cwd=self.worktree("other"))
        source = "import subprocess, sys; sys.exit(subprocess.run(%r).returncode)" % inner_args
        result, _, _ = self.run_guard(source, "--rss-mib", "512")
        self.assertEqual(result.returncode, 0)
        self.assertNotIn("inherited_from", json.loads(inner_report.read_text())["admission"])

    def test_free_mib_counts_the_slots_nobody_holds(self):
        lock = self.root / "shared.lock"
        self.assertEqual(guard.free_mib(lock, 4096), 4096)  # a lock no guard has used yet
        holder, _ = self.start_holder("--mem-budget-mib", "4096", "--rss-mib", "2048")
        self.assertEqual(guard.free_mib(lock, 4096), 2048)
        holder.send_signal(signal.SIGTERM)
        holder.communicate(timeout=12)
        self.assertEqual(guard.free_mib(lock, 4096), 4096)

    def test_a_stale_grant_is_not_an_admission(self):
        os.environ[guard.INHERIT] = json.dumps({"pid": 999999, "lock": str(self.root / "shared.lock"),
                                                "workspace": str(self.root), "rss_mib": 1e9,
                                                "exclusive": True, "shared_workspace": False})
        code, report = self.attempt()
        self.assertEqual(code, 0)
        self.assertNotIn("inherited_from", report["admission"])

    def test_an_older_guard_holding_the_lock_still_runs_alone(self):
        with (self.root / "shared.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)  # what a guard of an older checkout takes
            code, _ = self.attempt(cwd=self.worktree("new"))
            self.assertEqual(code, 75)
        code, _ = self.attempt(cwd=self.worktree("new"))
        self.assertEqual(code, 0)

    def test_a_waiting_queue_holder_is_admitted_before_later_acquirers(self):
        directory = Path(str(self.root / "shared.lock") + ".d")
        directory.mkdir()
        with (directory / "queue").open("a") as queue:
            fcntl.flock(queue, fcntl.LOCK_EX)  # an acquirer still collecting its slots
            code, _ = self.attempt(cwd=self.worktree("late"))
            self.assertEqual(code, 75)
        code, _ = self.attempt(cwd=self.worktree("late"))
        self.assertEqual(code, 0)

    def wait_text(self, path, text):
        deadline = time.monotonic() + 5
        while text not in path.read_text() and time.monotonic() < deadline:
            time.sleep(0.01)
        self.assertIn(text, path.read_text())

    def start_waiter(self, name, order, *options, cwd=None):
        """A guard (in its own worktree unless cwd is given) that records `name` in `order` once
        admitted. Returns when it waits for admission, with its stderr file (the waiting line
        shows its priority)."""
        source = f'open({str(order)!r}, "a").write({name!r} + "\\n")'
        args, _, _ = self.command(source, "--lock-wait", "20", *options, cwd=cwd or self.worktree(name))
        err = self.root / f"{name}.err"
        with err.open("wb") as stderr:
            waiter = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=stderr)
        self.addCleanup(self.cleanup_process, waiter)
        self.wait_text(err, "waiting for admission")
        return waiter, err

    def finish(self, *guards):
        for process in guards:
            process.communicate(timeout=12)
            self.assertEqual(process.returncode, 0)

    @property
    def tickets(self):
        return Path(str(self.root / "shared.lock") + ".d") / "merge"

    def test_a_merge_guard_is_admitted_ahead_of_queued_normal_guards(self):
        order, budget = self.root / "order", ("--mem-budget-mib", "1024")
        holder, _ = self.start_holder(*budget)
        first, _ = self.start_waiter("normal-1", order, *budget)  # collects first, as the queue head
        second, _ = self.start_waiter("normal-2", order, *budget)
        merge, err = self.start_waiter("merge", order, *budget, "--priority", "merge")
        self.assertIn("merge priority", err.read_text())
        self.assertIn("normal priority", (self.root / "normal-1.err").read_text())
        self.assertIsNone(holder.poll())  # the running workload is not preempted
        holder.send_signal(signal.SIGTERM)
        holder.communicate(timeout=12)
        self.finish(merge, first, second)
        self.assertEqual(order.read_text().split()[0], "merge")
        self.assertEqual(sorted(order.read_text().split()), ["merge", "normal-1", "normal-2"])
        self.assertIn("admitted after", err.read_text())
        self.assertEqual(os.listdir(self.tickets), [])

    def test_merge_guards_are_served_in_arrival_order(self):
        order, budget = self.root / "order", ("--mem-budget-mib", "1024")
        holder, _ = self.start_holder(*budget)
        normal, _ = self.start_waiter("normal", order, *budget)
        merges = [self.start_waiter(f"merge-{i}", order, *budget, "--priority", "merge")[0] for i in (1, 2, 3)]
        holder.send_signal(signal.SIGTERM)
        holder.communicate(timeout=12)
        self.finish(*merges, normal)
        self.assertEqual(order.read_text().split(), ["merge-1", "merge-2", "merge-3", "normal"])

    def test_a_normal_guard_collecting_slots_gives_them_to_a_merge_guard(self):
        # Budget 2 GiB: the holder takes one slot and the big normal guard (weight 2) collects the
        # other and waits for the holder. The merge guard (weight 1) needs only that slot.
        order, budget = self.root / "order", ("--mem-budget-mib", "2048")
        holder, _ = self.start_holder(*budget)
        big, _ = self.start_waiter("big", order, *budget, "--rss-mib", "1025")
        code, evidence = self.attempt(*budget, "--priority", "merge", "--lock-wait", "5", cwd=self.worktree("merge"))
        self.assertEqual((code, evidence["outcome"]), (0, "success"))
        self.assertEqual(evidence["admission"]["priority"], "merge")
        self.assertIsNone(holder.poll())
        self.assertIsNone(big.poll())
        holder.send_signal(signal.SIGTERM)
        holder.communicate(timeout=12)
        self.finish(big)  # nothing was lost: it is admitted once the holder ends
        self.assertEqual(order.read_text().split(), ["big"])

    def test_without_a_merge_guard_nothing_changes(self):
        order, budget = self.root / "order", ("--mem-budget-mib", "1024")
        holder, _ = self.start_holder(*budget)
        waiters = [self.start_waiter(f"normal-{i}", order, *budget)[0] for i in (1, 2, 3)]
        holder.send_signal(signal.SIGTERM)
        holder.communicate(timeout=12)
        self.finish(*waiters)
        self.assertEqual(sorted(order.read_text().split()), ["normal-1", "normal-2", "normal-3"])
        self.assertFalse(self.tickets.exists())  # no merge guard, no queue state
        code, evidence = self.attempt(cwd=self.worktree("later"))
        self.assertEqual((code, evidence["admission"]["priority"]), (0, "normal"))

    def test_a_small_guard_backfills_beside_a_waiting_head(self):
        # Budget 3 GiB: the holder takes one slot; the big head (weight 3) waits and, early in its
        # ramp, keeps one slot. The small guard runs in the third; the head follows the holder.
        order, budget = self.root / "order", ("--mem-budget-mib", "3072")
        holder, _ = self.start_holder(*budget)
        big, _ = self.start_waiter("big", order, *budget, "--rss-mib", "3000", "--backfill-ramp", "600")
        code, evidence = self.attempt(*budget, "--lock-wait", "5", cwd=self.worktree("small"))
        self.assertEqual((code, evidence["outcome"]), (0, "success"))
        self.assertTrue(evidence["admission"]["backfilled"])
        self.assertIsNone(big.poll())
        holder.send_signal(signal.SIGTERM)
        holder.communicate(timeout=12)
        self.finish(big)
        self.assertEqual(order.read_text().split(), ["big"])
        self.assertEqual(os.listdir(Path(str(self.root / "shared.lock") + ".d") / "heads"), [])

    def test_a_head_past_its_ramp_keeps_every_free_slot(self):
        budget = ("--mem-budget-mib", "3072")
        holder, _ = self.start_holder(*budget)
        big, _ = self.start_waiter("big", self.root / "order", *budget, "--rss-mib", "3000",
                                   "--backfill-ramp", "0")
        code, evidence = self.attempt(*budget, "--lock-wait", "2", cwd=self.worktree("small"))
        self.assertEqual((code, evidence["outcome"]), (75, "lock_busy"))
        self.assertFalse(evidence["admission"]["backfilled"])
        holder.send_signal(signal.SIGTERM)
        holder.communicate(timeout=12)
        self.finish(big)

    def stand_in_head(self, content, enter=None):
        """A queue head (stand-in): it holds the queue and publishes `content` in `heads/`, until
        the test ends (or what `enter` belongs to closes)."""
        enter = enter or self.enterContext
        directory = Path(str(self.root / "shared.lock") + ".d")
        directory.mkdir(parents=True, exist_ok=True)
        queue = enter((directory / "queue").open("a"))
        fcntl.flock(queue, fcntl.LOCK_EX)
        enter(guard.publish_entry(directory / "heads", "1-1", content, lambda path: path.open("a")))

    def test_backfill_leaves_the_heads_unmet_reservation_free(self):
        self.stand_in_head({"pid": os.getpid(), "unmet": 1, "need": 3})
        code, _ = self.attempt("--mem-budget-mib", "1024", "--lock-wait", "2", cwd=self.worktree("a"))
        self.assertEqual(code, 75)  # one free slot: the head's
        code, evidence = self.attempt("--mem-budget-mib", "2048", "--lock-wait", "2", cwd=self.worktree("b"))
        self.assertEqual(code, 0)  # two: one for the head, one for the backfill
        self.assertTrue(evidence["admission"]["backfilled"])
        self.assertEqual(guard.free_mib(self.root / "shared.lock", 2048), 1024)  # the head's reserved slot

    def test_free_slots_that_admit_the_head_go_to_it(self):
        self.stand_in_head({"pid": os.getpid(), "unmet": 0, "need": 2})
        code, evidence = self.attempt("--mem-budget-mib", "2048", "--lock-wait", "2", cwd=self.worktree("a"))
        self.assertEqual(code, 75)
        self.assertFalse(evidence["admission"]["backfilled"])
        code, _ = self.attempt("--mem-budget-mib", "3072", "--lock-wait", "2", cwd=self.worktree("b"))
        self.assertEqual(code, 75)  # three free still admit the head (2) first

    def test_a_head_entry_of_another_shape_gets_no_backfill(self):
        for content in ({"unmet": "x", "need": 3}, {"unmet": 1}, {"unmet": 2, "need": 1}, {"unmet": None, "need": 3}):
            with self.subTest(content=content), contextlib.ExitStack() as stack:
                self.stand_in_head(content, stack.enter_context)
                code, evidence = self.attempt("--mem-budget-mib", "4096", "--lock-wait", "1.5",
                                              cwd=self.worktree("a"))
                self.assertEqual((code, evidence["outcome"]), (75, "lock_busy"))

    def test_the_backfill_ramp(self):
        for value in ("-1", "inf", "nan"):
            with self.subTest(value=value), self.assertRaises(SystemExit), \
                    contextlib.redirect_stderr(io.StringIO()):
                guard.parse_args(["--report", "r", "--log", "l", "--backfill-ramp", value, "--", "true"])
        a = guard.parse_args(["--report", "r", "--log", "l", "--rss-mib", "4096", "--backfill-ramp", "100",
                              "--mem-budget-mib", "8192", "--lock", str(self.root / "shared.lock"), "--", "true"])
        self.assertEqual(a.backfill_ramp, 100)
        admission = guard.Admission(a)
        self.assertEqual([admission.reservation(w) for w in (0, 1, 25, 50, 99, 100, 1000)], [0, 1, 1, 2, 4, 4, 4])
        a.backfill_ramp = 0
        self.assertEqual(admission.reservation(0), 4)

    def test_no_backfill_behind_a_merge_ticket(self):
        order, budget = self.root / "order", ("--mem-budget-mib", "3072")
        holder, _ = self.start_holder(*budget)
        merge, _ = self.start_waiter("merge", order, *budget, "--rss-mib", "3000", "--priority", "merge")
        code, evidence = self.attempt(*budget, "--lock-wait", "2", cwd=self.worktree("small"))
        self.assertEqual((code, evidence["outcome"]), (75, "lock_busy"))
        holder.send_signal(signal.SIGTERM)
        holder.communicate(timeout=12)
        self.finish(merge)

    def test_normal_guards_wait_for_a_live_merge_ticket_and_ignore_a_dead_one(self):
        self.tickets.mkdir(parents=True)
        ticket = self.tickets / "00000000000000000001-1"
        with ticket.open("a") as owner:
            fcntl.flock(owner, fcntl.LOCK_EX)  # a merge guard waiting for admission
            code, _ = self.attempt(cwd=self.worktree("normal"))
            self.assertEqual(code, 75)
        self.assertTrue(ticket.exists())  # its guard has died: nothing holds the ticket
        code, _ = self.attempt(cwd=self.worktree("normal"))
        self.assertEqual(code, 0)
        self.assertFalse(ticket.exists())

    def test_merge_priority_keeps_one_build_per_workspace(self):
        budget = ("--mem-budget-mib", "8192")
        self.start_holder(*budget)
        code, evidence = self.attempt(*budget, "--priority", "merge")  # the holder's workspace
        self.assertEqual((code, evidence["outcome"]), (75, "lock_busy"))
        waiter, err = self.start_waiter("same-workspace", self.root / "order", *budget, "--priority", "merge",
                                        cwd=self.root)
        self.assertIn("merge priority", err.read_text())
        # Waiting for its workspace it holds no place in the queue: others are admitted meanwhile.
        code, _ = self.attempt(*budget, "--lock-wait", "2", cwd=self.worktree("other"))
        self.assertEqual(code, 0)
        self.assertIsNone(waiter.poll())
        self.assertFalse(self.tickets.exists() and os.listdir(self.tickets))

    def test_a_queued_exclusive_guard_drains_running_workloads_then_runs_alone(self):
        # The budget admits every guard here at once: only the drain makes them wait.
        order, budget = self.root / "order", ("--mem-budget-mib", "8192")
        holder, _ = self.start_holder(*budget)
        exclusive, err = self.start_waiter("exclusive", order, *budget, "--exclusive", "--priority", "merge")
        self.assertIn("exclusive priority", err.read_text())
        code, evidence = self.attempt(*budget, "--lock-wait", "1", cwd=self.worktree("late"))
        self.assertEqual((code, evidence["outcome"]), (75, "lock_busy"))  # no new admission meanwhile
        normal, err = self.start_waiter("normal", order, *budget)
        self.assertIn("0 merge and 1 exclusive guard(s) queued", err.read_text())
        self.assertIsNone(holder.poll())  # the running workload is not preempted
        self.assertIsNone(exclusive.poll())
        holder.send_signal(signal.SIGTERM)
        holder.communicate(timeout=12)
        self.finish(exclusive, normal)
        self.assertEqual(order.read_text().split(), ["exclusive", "normal"])
        self.assertEqual(os.listdir(self.tickets), [])

    def test_merge_and_exclusive_guards_are_served_in_arrival_order(self):
        # One slot: every guard waits for the holder, then the tickets go first come, first served.
        order, budget = self.root / "order", ("--mem-budget-mib", "1024")
        holder, _ = self.start_holder(*budget)
        guards = [self.start_waiter("merge-1", order, *budget, "--priority", "merge")[0],
                  self.start_waiter("exclusive-1", order, *budget, "--exclusive")[0],
                  self.start_waiter("merge-2", order, *budget, "--priority", "merge")[0],
                  self.start_waiter("normal", order, *budget)[0],
                  self.start_waiter("exclusive-2", order, *budget, "--exclusive")[0]]
        holder.send_signal(signal.SIGTERM)
        holder.communicate(timeout=12)
        self.finish(*guards)
        self.assertEqual(order.read_text().split(), ["merge-1", "exclusive-1", "merge-2", "exclusive-2", "normal"])

    def test_the_ticket_of_a_dead_exclusive_guard_expires(self):
        budget = ("--mem-budget-mib", "8192")
        holder, _ = self.start_holder(*budget)
        exclusive, _ = self.start_waiter("exclusive", self.root / "order", *budget, "--exclusive")
        code, _ = self.attempt(*budget, cwd=self.worktree("normal"))
        self.assertEqual(code, 75)
        exclusive.kill()  # no cleanup runs: the ticket file stays, but nothing holds it
        exclusive.communicate(timeout=12)
        self.assertEqual(len(os.listdir(self.tickets)), 1)
        code, _ = self.attempt(*budget, cwd=self.worktree("normal"))
        self.assertEqual(code, 0)
        self.assertEqual(os.listdir(self.tickets), [])
        self.assertIsNone(holder.poll())

    def test_priority_comes_from_the_environment_or_the_option(self):
        def priority(*options):
            return guard.parse_args(["--report", "r.json", "--log", "l.log", *options, "--", "true"]).priority
        with mock.patch.dict(os.environ, {"AIR2LEAN_GUARD_PRIORITY": "merge"}):
            self.assertEqual(priority(), "merge")
            self.assertEqual(priority("--priority", "normal"), "normal")
            result, report, _ = self.run_guard("pass")  # the guard process inherits the variable
            self.assertEqual((result.returncode, report["admission"]["priority"]), (0, "merge"))
        with mock.patch.dict(os.environ, {"AIR2LEAN_GUARD_PRIORITY": ""}):
            self.assertEqual(priority(), "normal")
        with mock.patch.dict(os.environ, {"AIR2LEAN_GUARD_PRIORITY": "urgent"}), \
                mock.patch("sys.stderr"), self.assertRaises(SystemExit):
            priority()

    def test_budget_comes_from_the_environment(self):
        with mock.patch.dict(os.environ, {"AIR2LEAN_BUILD_MEM_MIB": "2048"}):
            a = guard.parse_args(["--report", "r.json", "--log", "l.log", "--", "true"])
        self.assertEqual(a.mem_budget_mib, 2048)
        with mock.patch.dict(os.environ, {"AIR2LEAN_BUILD_MEM_MIB": "-1"}), self.assertRaises(SystemExit):
            guard.parse_args(["--report", "r.json", "--log", "l.log", "--", "true"])

    # Usage-aware charge (build-guard.py's docstring). /proc/meminfo and the cgroup limit are
    # mocked: the policy is the same on every host, only its MemAvailable source is Linux's.
    def admission(self, *options, budget="8192", rss="6000"):
        cgroup = mock.patch.object(guard, "cgroup_limited", return_value=False)
        cgroup.start()
        self.addCleanup(cgroup.stop)
        a = guard.parse_args(["--cwd", str(self.root), "--lock", str(self.root / "shared.lock"),
                              "--report", "r.json", "--log", "l.log", "--mem-budget-mib", budget,
                              "--rss-mib", rss, "--lock-wait", "1", *options, "--", "lake", "build"])
        admission = guard.Admission(a)
        admission.directory.mkdir(parents=True, exist_ok=True)
        self.addCleanup(admission.release)
        return admission

    def history(self, admission, *runs):
        admission.history.parent.mkdir(exist_ok=True)
        admission.history.write_text(json.dumps([{"outcome": outcome, "peak_mib": peak} for outcome, peak in runs]))

    def test_overcommit_charges_the_measured_need_after_two_successes(self):
        self.assertEqual(guard.history_charge([{"outcome": "success", "peak_mib": 2000}], 6000),
                         (6000, "fewer than 2 recent successes"))
        runs = [{"outcome": "success", "peak_mib": 1000}, {"outcome": "child_failed", "peak_mib": 5000},
                {"outcome": "success", "peak_mib": 2000}]
        self.assertEqual(guard.history_charge(runs, 6000), (2600, None))  # 1.3 x the largest success
        self.assertEqual(guard.history_charge(runs, 2048), (2048, None))  # never above --rss-mib
        tiny = [{"outcome": "success", "peak_mib": 10}] * 2
        self.assertEqual(guard.history_charge(tiny, 6000), (guard.SLOT_MIB, None))  # at least one slot
        admission = self.admission()
        self.history(admission, ("success", 1000), ("success", 2000))
        with mock.patch.object(guard, "mem_available_mib", return_value=6000):
            admission.plan()
        self.assertEqual((admission.declared, admission.weight), (6, 3))
        self.assertEqual(admission.evidence()["charge_mib"], 2600)

    def test_overcommit_falls_back_to_the_declared_limit_after_a_limit_hit(self):
        oom = {"outcome": "child_failed", "exit_code": guard.KILLED, "peak_mib": 900}
        for unsafe in [{"outcome": outcome, "peak_mib": 6100} for outcome in guard.UNSAFE_OUTCOMES] + [oom]:
            admission = self.admission()
            ok = {"outcome": "success", "peak_mib": 1000}
            admission.history.parent.mkdir(exist_ok=True)
            admission.history.write_text(json.dumps([ok, unsafe, ok, ok]))
            with mock.patch.object(guard, "mem_available_mib", return_value=6000):
                admission.plan()
            self.assertEqual(admission.weight, admission.declared)
            self.assertIn("hit its limit", admission.evidence()["why_declared"])
        # It ages out: after HISTORY_RUNS later runs the command is charged its need again.
        self.history(admission, ("rss_limit", 6100), *[("success", 1000)] * guard.HISTORY_RUNS)
        with mock.patch.object(guard, "mem_available_mib", return_value=6000):
            admission.plan()
        self.assertEqual(admission.weight, 2)
        # Entries that are not runs (a damaged file) are skipped, not fatal.
        admission.history.write_text(json.dumps([1, None, "x", {"outcome": "success", "peak_mib": 1000}]))
        self.assertEqual(guard.history_charge(admission.runs(), 6000), (6000, "fewer than 2 recent successes"))

    def test_recorded_runs_feed_the_next_charge(self):
        admission = self.admission()
        for peak in (900, 1500):
            admission.record({"started_utc": "t", "outcome": "success", "exit_code": 0, "samples": 3,
                              "peak_sampled_rss_kib": peak * 1024})
        admission.record({"started_utc": "t", "outcome": "cancelled", "exit_code": 143, "samples": 0,
                          "peak_sampled_rss_kib": 0})
        self.assertEqual([(run["outcome"], run["peak_mib"]) for run in admission.runs()],
                         [("success", 900), ("success", 1500), ("cancelled", None)])
        # One key for every checkout of the command, another for another directory in the checkout.
        one, two, sub = (self.admission("--cwd", str(self.root / path)).a for path in ("w1", "w2", "w1/tests"))
        self.assertEqual(guard.command_key(one, one.cwd), guard.command_key(two, two.cwd))
        self.assertNotEqual(guard.command_key(one, one.cwd), guard.command_key(sub, one.cwd))
        other = self.admission()  # the same command in the same workspace shares the history
        with mock.patch.object(guard, "mem_available_mib", return_value=6000):
            other.plan()
        self.assertEqual(other.weight, 2)  # ceil(1.3 x 1500) = 1950 MiB

    def test_macos_and_opted_out_guards_are_never_overcommitted(self):
        cases = (((), None, False, "not Linux"), (("--no-overcommit",), 6000, False, "--no-overcommit"),
                 (("--exclusive",), 6000, False, "--exclusive"), (("--lock-wait", "0"), 6000, False, "--lock-wait 0"),
                 ((), 6000, True, "cgroup"))
        for options, available, limited, why in cases:
            admission = self.admission(*options)
            self.history(admission, ("success", 1000), ("success", 1000))
            with mock.patch.object(guard, "mem_available_mib", return_value=available), \
                    mock.patch.object(guard, "cgroup_limited", return_value=limited):
                admission.plan()
            self.assertEqual(admission.weight, admission.declared)
            self.assertIn(why, admission.evidence()["why_declared"])
            self.assertFalse(admission.evidence()["overcommit"])

    def test_declared_limits_stay_within_the_bound(self):
        # 8 slots: the registered excess may reach 4 (declared limits <= 1.5 x budget, as held
        # slots never exceed the budget), whatever runs at its declared charge besides.
        admission = self.admission(rss="4096")
        admission.weight = 1
        self.assertTrue(admission.within_bound())  # excess 3 <= 4
        other = self.admission()
        guard.publish_entry(other.running, "00000000000000000001-1", {"excess_slots": 3}, other.open)
        self.assertFalse(admission.within_bound())  # 3 + 3 > 4
        other.release()  # its guard ended: the entry no longer counts
        self.assertTrue(admission.within_bound())

    @unittest.skipIf(guard.mem_available_mib() is None or guard.cgroup_limited(), "never overcommitted here")
    def test_a_repeated_command_is_admitted_at_its_measured_need(self):
        options = ("--mem-budget-mib", "8192", "--rss-mib", "4096", "--lock-wait", "5")
        reports = [self.run_guard("import time; time.sleep(0.1)", *options)[1] for _ in range(3)]
        self.assertEqual([report["admission"]["weight"] for report in reports], [4, 4, 1])
        self.assertEqual([report["admission"]["overcommit"] for report in reports], [False, False, True])
        self.assertEqual(reports[2]["budget"]["rss_mib"], 4096)  # the limit stays the declared one
        self.assertEqual(os.listdir(self.root / "shared.lock.d/running"), [])  # gone with its guard

    def test_the_backstop_preempts_only_the_youngest_overcommitted_workload(self):
        older, younger, declared = self.admission(), self.admission(), self.admission()
        for admission in (older, younger):
            admission.weight = 2
            admission.register()
        low, high = guard.backstop_mib() - 1, guard.backstop_mib()

        def preempt(admission):
            admission.next_backstop_check = 0.0  # MemAvailable is read at most once a second
            return admission.preempt()
        with mock.patch.object(guard, "mem_available_mib", return_value=high):
            self.assertFalse(preempt(younger))
        with mock.patch.object(guard, "mem_available_mib", return_value=low):
            self.assertFalse(preempt(declared))  # it holds its declared slots
            self.assertFalse(preempt(older))
            self.assertTrue(preempt(younger))
            self.assertEqual(len(os.listdir(younger.running)), 1)  # it left the registry at once
            self.assertFalse(preempt(older))  # now the youngest, but within the hold-off
            (older.directory / "preempted").write_text("0")
            self.assertTrue(preempt(older))

    def test_waiting_for_lock_can_be_cancelled_without_spawning(self):
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
    fixture_pause()
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
    fixture_pause()
else:
    open({str(pidfile)!r}, 'w').write(str(pid))
    fixture_pause()
'''
        result, report, _ = self.run_guard(source, "--timeout", "0.4")
        self.assertEqual((result.returncode, report["outcome"]), (124, "timeout"))
        self.assertFalse(self.live(int(pidfile.read_text())))

    def test_observer_failure_cleans_group(self):
        args, _, _ = self.command("fixture_pause()", "--grace", "0.02")
        a = guard.parse_args(args[2:])
        with mock.patch.object(guard, "processes", side_effect=RuntimeError("ps failed")):
            report = guard.run(a)
        self.assertEqual(report["exit_code"], 70)
        self.assertEqual(report["outcome"], "cleanup_failed")
        self.assertTrue(report["drain_incomplete"])
        self.assertTrue(report["log_truncated"])

    def fake_ps(self, hang_calls):
        """A bin directory whose `ps` hangs on its first `hang_calls` calls (None: always), then runs the real one."""
        bin_dir = self.root / "fakebin"
        bin_dir.mkdir(exist_ok=True)
        counter = self.root / "ps-calls"
        counter.write_text("")
        real = subprocess.run(["/usr/bin/which", "ps"], capture_output=True, text=True).stdout.strip()
        limit = "10**9" if hang_calls is None else str(hang_calls)
        script = bin_dir / "ps"
        script.write_text(f'''#!{sys.executable}
import os, sys, time
c = {str(counter)!r}
open(c, "a").write("x")
if len(open(c).read()) <= {limit}:
    time.sleep(30)
os.execv({real!r}, ["ps"] + sys.argv[1:])
''')
        script.chmod(0o755)
        return bin_dir, counter

    def run_with_ps(self, bin_dir, source, *options):
        args, report, log = self.command(source, *options)
        env = {**os.environ, "PATH": f"{bin_dir}{os.pathsep}{os.environ['PATH']}"}
        subprocess.run(args, capture_output=True, text=True, timeout=25, env=env)
        return json.loads(report.read_text())

    def test_one_slow_ps_sample_does_not_abort_the_build(self):
        bin_dir, counter = self.fake_ps(1)
        report = self.run_with_ps(bin_dir, "import time; time.sleep(0.5)",
                                  "--ps-timeout", "0.3", "--sample-stale", "10")
        self.assertEqual((report["exit_code"], report["outcome"]), (0, "success"))
        self.assertEqual(report["failed_samples"], 1)
        self.assertGreater(report["samples"], 0)

    def test_ps_that_keeps_timing_out_aborts_after_the_stale_window(self):
        bin_dir, counter = self.fake_ps(None)
        started = time.monotonic()
        report = self.run_with_ps(bin_dir, "fixture_pause()",
                                  "--ps-timeout", "0.2", "--sample-stale", "1", "--timeout", "20")
        self.assertEqual(report["samples"], 0)
        self.assertGreater(report["failed_samples"], 1)
        self.assertEqual(report["exit_code"], 70)
        self.assertIn("no process sample", report["error"])
        self.assertLess(time.monotonic() - started, 20)

    def test_sampler_keeps_failing_inside_window_then_raises(self):
        sampler = guard.Sampler(0.1, 0.3)
        timeout = subprocess.TimeoutExpired("ps", 0.1)
        with mock.patch.object(guard, "processes", side_effect=timeout):
            self.assertIsNone(sampler.sample())
            time.sleep(0.35)
            with self.assertRaises(RuntimeError):
                sampler.sample()

    def test_sequential_zig_flags_and_invocation_count(self):
        names = {"zig"}
        self.assertEqual(guard.sequential_command(["zig", "build", "test"], names),
                         ["zig", "build", "-j1", "test"])
        for command in (["zig", "build", "-j2"], ["zig", "build", "-j", "2"],
                        ["zig", "build", "-j"], ["zig", "build", "@options"]):
            with self.assertRaises(ValueError):
                guard.sequential_command(command, names)
        # `zig build` (1) runs its compilers (2, 3, 4) below its build runner (10).
        rows = {1: {"parent": 0, "name": "zig"}, 10: {"parent": 1, "name": "build"},
                2: {"parent": 10, "name": "zig"}}
        self.assertFalse(guard.parallel_zig(rows, {1, 10, 2}, names))
        rows[3] = {"parent": 10, "name": "zig"}
        self.assertTrue(guard.parallel_zig(rows, {1, 10, 2, 3}, names))
        self.assertFalse(guard.parallel_zig(rows, {1, 10, 2, 3}, names, jobs=2))
        rows[4] = {"parent": 10, "name": "zig"}
        self.assertTrue(guard.parallel_zig(rows, {1, 10, 2, 3, 4}, names, jobs=2))
        self.assertFalse(guard.parallel_zig(rows, {1, 10, 2, 3, 4}, names, jobs=3))
        # A cold libc build under it: compiler 2's `zig clang` children are part of compiler 2.
        for pid in (20, 21, 22, 23):
            rows[pid] = {"parent": 2, "name": "zig"}
        tree = {1, 10, 2, 3, 4, 20, 21, 22, 23}
        self.assertFalse(guard.parallel_zig(rows, tree, names, jobs=3))
        self.assertTrue(guard.parallel_zig(rows, tree, names, jobs=2))
        # A non-Zig process below a clang child that runs a compiler (40): compiler 2 supervises
        # it, so 40 counts instead of 2.
        rows[41] = {"parent": 20, "name": "sh"}
        rows[40] = {"parent": 41, "name": "zig"}
        self.assertFalse(guard.parallel_zig(rows, tree | {40, 41}, names, jobs=3))  # 3, 4 and 40
        rows[5] = {"parent": 10, "name": "zig"}
        self.assertTrue(guard.parallel_zig(rows, tree | {40, 41, 5}, names, jobs=3))

        def tree_of(edges, name="zig"):  # {pid: parent pid} of Zig processes, others as given
            return {pid: {"parent": parent, "name": name} for pid, parent in edges.items()}

        # One `zig build-exe ... -lc` (30) with its clang children: one invocation. So is a Zig
        # process with direct Zig children (Zig starts several compilers only through a runner).
        single = tree_of({30: 0, 31: 30, 32: 30, 33: 30})
        self.assertFalse(guard.parallel_zig(single, set(single), names))
        # 0.17: `zig build` execs into its runner `maker`; its compilers (with clang children) each count.
        maker = {50: {"parent": 0, "name": "maker"}, **tree_of({51: 50, 52: 50, 53: 51, 54: 51})}
        self.assertTrue(guard.parallel_zig(maker, set(maker), names))
        self.assertFalse(guard.parallel_zig(maker, set(maker), names, jobs=2))
        # Truncated comm: aliases sharing the 15-byte prefix count as the configured name.
        alias = "zig-very-long-configured-alias"
        aliased = {60: {"parent": 0, "name": "driver"}, **tree_of({61: 60, 62: 60}, alias[:15])}
        self.assertTrue(guard.parallel_zig(aliased, set(aliased), {alias}))
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
    fixture_pause()
    os._exit(0)
open({str(pidfile)!r}, 'w').write(str(pid))
os._exit(0)
'''
        source = self.fixture_source(source)
        started = time.monotonic()
        child = subprocess.Popen([sys.executable, "-c", source], start_new_session=True)
        tree = guard.Tree(child.pid)
        self.addCleanup(self.cleanup_process, child)
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
        self.assertLess(time.monotonic() - started, FIXTURE_LIFETIME)

    def test_final_cleanup_only_skips_a_confirmed_empty_tree(self):
        args, _, _ = self.command("pass")
        with mock.patch.object(guard, "stop_tree", wraps=guard.stop_tree) as stops:
            self.assertEqual(guard.run(guard.parse_args(args[2:]))["exit_code"], 0)
            self.assertEqual(stops.call_count, 0)
        args, _, _ = self.command("fixture_pause()", "--timeout", "0.1")
        with mock.patch.object(guard, "stop_tree", wraps=guard.stop_tree) as stops:
            self.assertEqual(guard.run(guard.parse_args(args[2:]))["exit_code"], 124)
            self.assertEqual(stops.call_count, 1)
        args, _, _ = self.command("fixture_pause()", "--timeout", "0.1")
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

    def test_truncated_alias_compilers_trigger_workload_termination(self):
        alias = "zig-long-configured-compiler"
        args, _, _ = self.command("fixture_pause()", "--zig-name", alias)
        original_processes = guard.processes
        def sampled_compilers(*args):
            rows = original_processes(*args)
            leaders = [pid for pid, row in rows.items()
                       if row["parent"] == os.getpid() and row["group"] == pid]
            if leaders:
                leader = leaders[0]
                rows[leader]["name"] = "driver"
                for pid in (-1, -2):
                    rows[pid] = {"parent": leader, "group": leader, "start": "mock",
                                 "name": alias[:15], "rss_kib": 0}
            return rows
        with mock.patch.object(guard, "processes", side_effect=sampled_compilers):
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
