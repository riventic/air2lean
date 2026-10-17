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

    def test_a_waiting_exclusive_workload_holds_up_no_admission(self):
        budget = ("--mem-budget-mib", "8192")
        self.start_holder(*budget)
        args, _, _ = self.command("pass", *budget, "--exclusive", "--lock-wait", "8", cwd=self.worktree("x"))
        waiter = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.addCleanup(self.cleanup_process, waiter)
        time.sleep(0.5)  # the exclusive workload is waiting now
        code, _ = self.attempt(*budget, "--lock-wait", "2", cwd=self.worktree("y"))
        self.assertEqual(code, 0)
        self.assertIsNone(waiter.poll())

    def test_guard_mode_is_exported_and_recorded(self):
        for options, mode in (((), "shared"), (("--exclusive",), "exclusive")):
            result, report, log = self.run_guard('import os; print(os.environ["AIR2LEAN_GUARD_MODE"])', *options)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(log.read_text(), mode + "\n")
            self.assertEqual(report["environment_overrides"]["AIR2LEAN_GUARD_MODE"], mode)
            self.assertEqual(report["admission"]["exclusive"], bool(options))

    def test_an_older_guard_holding_the_lock_still_runs_alone(self):
        import fcntl
        with (self.root / "shared.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)  # what a guard of an older checkout takes
            code, _ = self.attempt(cwd=self.worktree("new"))
            self.assertEqual(code, 75)
        code, _ = self.attempt(cwd=self.worktree("new"))
        self.assertEqual(code, 0)

    def test_a_waiting_queue_holder_is_admitted_before_later_acquirers(self):
        import fcntl
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

    def test_normal_guards_wait_for_a_live_merge_ticket_and_ignore_a_dead_one(self):
        import fcntl
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

    def test_an_exclusive_workload_has_no_priority_and_holds_up_nobody(self):
        budget = ("--mem-budget-mib", "8192")
        self.start_holder(*budget)
        waiter, err = self.start_waiter("x", self.root / "order", *budget, "--exclusive", "--priority", "merge")
        self.assertIn("normal priority", err.read_text())
        code, _ =self.attempt(*budget, "--lock-wait", "2", cwd=self.worktree("y"))
        self.assertEqual(code, 0)
        self.assertIsNone(waiter.poll())
        self.assertFalse(self.tickets.exists())

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
        self.assertFalse(guard.parallel_zig(rows, {1, 2, 3}, names, jobs=2))
        rows[4] = {"parent": 1, "name": "zig"}
        self.assertTrue(guard.parallel_zig(rows, {1, 2, 3, 4}, names, jobs=2))
        del rows[4]
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

    def test_truncated_alias_leaves_trigger_workload_termination(self):
        alias = "zig-long-configured-compiler"
        args, _, _ = self.command("fixture_pause()", "--zig-name", alias)
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
