#!/usr/bin/env python3
"""Admit POSIX build workloads within a machine-wide memory budget and record reactive
resource-budget evidence.

Admission (the lock `--lock`, default AIR2LEAN_BUILD_LOCK or ~/.cache/air2lean/build.lock):
- Memory slots. The budget (`--mem-budget-mib`, default AIR2LEAN_BUILD_MEM_MIB, else 75% of
  physical memory) is split into slots of 1 GiB, files `<lock>.d/slot-NNN`. A workload holds
  ceil(--rss-mib / 1 GiB) of them (at most all), and --rss-mib is a hard limit (the guard stops
  a workload above it), so the guarded workloads together stay within the budget: several
  worktrees build at once while memory allows, and the rest wait.
- One build per Lake workspace. Lake has no build lock of its own, so two builds in one checkout
  must not overlap: a workload holds `<lock>.d/ws-<digest of the git top level of --cwd>`
  exclusively, or shared with `--shared-workspace` (a workload that writes nothing Lake owns,
  e.g. `lake env lean` of files into a private directory).
- `<lock>` itself: held shared by every workload, exclusively with `--exclusive` (timing
  measurements: nothing else guarded runs meanwhile). A guard of an older checkout takes it
  exclusively, so it still runs alone.
- Fairness: acquirers queue on `<lock>.d/queue`; the one holding it collects its slots while
  later ones wait behind it, so a large workload is not starved by small ones. An exclusive
  workload only tries at the head of the queue and never waits there (that would hold every
  admission until the longest running workload ends), so it may wait until --lock-wait.
Never take a private lock lane (another AIR2LEAN_BUILD_LOCK) to get around a wait: the budget
is only a bound when every heavy workload of the machine goes through the same lock.
--lock-wait bounds the whole admission; exit 75 (lock_busy) when it is exceeded."""

import argparse
import datetime
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import selectors
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time


def digest(path):
    h = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def file_evidence(path, cache=None):
    path = Path(path).resolve()
    try:
        info = path.stat()
        if not stat.S_ISREG(info.st_mode):
            return {"path": str(path), "unavailable": "not a regular file"}
        identity = (info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns)
        if cache is None:
            fingerprint = {"sha256": digest(path), "bytes": info.st_size}
        else:
            if identity not in cache:
                cache[identity] = {"sha256": digest(path), "bytes": info.st_size}
            fingerprint = cache[identity]
        return {"path": str(path), **fingerprint}
    except OSError as error:
        return {"path": str(path), "unavailable": str(error)[:256]}


def revision(cwd):
    def git(*args):
        # Read repository state only; never invoke a compiler/version probe.
        result = subprocess.run(["git", "-C", str(cwd), *args],
                                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                timeout=5, check=True, text=True)
        return result.stdout.strip()
    try:
        return {"head": git("rev-parse", "HEAD"),
                "tracked_dirty": bool(git("status", "--porcelain", "--untracked-files=no"))}
    except (OSError, subprocess.SubprocessError):
        return {"unavailable": True}


def executable(tool, cwd):
    if os.path.dirname(tool):
        path = cwd / tool
        return str(path) if path.is_file() and os.access(path, os.X_OK) else None
    search = os.pathsep.join(str(cwd / directory) for directory in os.get_exec_path())
    return shutil.which(tool, path=search)


def processes():
    # Both macOS and Linux ps provide these columns. lstart distinguishes reused
    # PIDs when following observed descendants; it has one-second resolution.
    env = os.environ | {"LC_ALL": "C"}
    result = subprocess.run(["ps", "-axo", "pid=,ppid=,pgid=,rss=,lstart=,stat=,comm="],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=5, check=True, text=True, env=env)
    rows = {}
    for line in result.stdout.splitlines():
        fields = line.split(None, 10)
        if len(fields) != 11:
            raise RuntimeError("unrecognized ps process row")
        pid, parent, group, rss = map(int, fields[:4])
        if fields[9].startswith("Z"):
            continue  # an orphaned zombie is already stopped and cannot be killed
        rows[pid] = {"parent": parent, "group": group, "rss_kib": rss,
                     "start": " ".join(fields[4:9]), "name": Path(fields[10]).name}
    return rows


class Tree:
    def __init__(self, root):
        self.root = root
        self.seen = {}
        self.original_group_gone = False

    def owned(self, rows):
        # The initial process group also catches children orphaned before our
        # first sample. Known descendants remain owned after reparenting/setsid.
        owned = {pid for pid, row in rows.items() if row["group"] == self.root}
        if not owned:
            self.original_group_gone = True
        owned.update(pid for pid, started in self.seen.items()
                     if pid in rows and rows[pid]["start"] == started)
        pending = list(owned)
        children = {}
        for pid, row in rows.items():
            children.setdefault(row["parent"], []).append(pid)
        while pending:
            for pid in children.get(pending.pop(), []):
                if pid not in owned:
                    owned.add(pid)
                    pending.append(pid)
        self.seen = {pid: rows[pid]["start"] for pid in owned}
        return owned


def parallel_zig(rows, owned, names, jobs=1):
    # More than `jobs` leaf Zig compilers. Linux comm truncates to 15 bytes. Prefix
    # collisions are intentionally conservative: refusing ambiguous parallel work is
    # safer than missing it.
    observed_names = names | {name.encode()[:15].decode(errors="replace") for name in names}
    zig = {pid for pid in owned if rows[pid]["name"] in observed_names}
    # A zig build driver supervising one compiler is sequential. Count leaf Zig
    # processes, not their build-driver ancestors.
    ancestors = set()
    for pid in zig:
        parent = rows[pid]["parent"]
        visited = set()
        while parent in owned and parent not in visited:
            visited.add(parent)
            ancestors.add(parent)
            parent = rows[parent]["parent"]
    return len(zig - ancestors) > jobs


def signal_groups(groups, sig):
    for group in groups:
        if group <= 0 or group == os.getpgrp():
            raise RuntimeError("child unexpectedly joined coordinator process group")
        try:
            os.killpg(group, sig)
        except ProcessLookupError:
            pass


def signal_workload(child, tree, sig):
    try:
        rows = processes()
        groups = {rows[pid]["group"] for pid in tree.owned(rows)}
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError):
        # The unreaped leader reserves its PID/PGID even after exit. Do not
        # condition this fallback on poll(): surviving children still need it.
        groups = set() if tree.original_group_gone else {child.pid}
    signal_groups(groups, sig)


def peek_status(child):
    # WNOWAIT retains the leader as a PID anchor until all cleanup attempts end.
    info = os.waitid(os.P_PID, child.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
    if info is None:
        return None
    return info.si_status if info.si_code == os.CLD_EXITED else -info.si_status


def stop_tree(child, tree, grace):
    # Keep the global lock until both the leader and observed descendants stop.
    # If ps fails, the original group can still be stopped without guessing PIDs.
    signal_workload(child, tree, signal.SIGTERM)
    end = time.monotonic() + grace
    while time.monotonic() < end:
        try:
            rows = processes()
            owned = tree.owned(rows)
            if not owned:
                return True
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError):
            pass
        time.sleep(min(0.05, max(0, end - time.monotonic())))
    signal_workload(child, tree, signal.SIGKILL)
    end = time.monotonic() + 5
    while time.monotonic() < end:
        try:
            if not tree.owned(processes()):
                return True
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError):
            return False
        time.sleep(0.01)
    return False


def atomic_report(path, report):
    path.parent.mkdir(parents=True, exist_ok=True)
    data = json.dumps(report, sort_keys=True, indent=2) + "\n"
    if len(data.encode()) > 128 * 1024:
        raise RuntimeError("report exceeds 128 KiB limit")
    fd, temporary = tempfile.mkstemp(prefix=".build-guard-", dir=path.parent)
    try:
        with os.fdopen(fd, "w") as out:
            out.write(data)
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def positive(value):
    value = float(value)
    if not 0 < value < float("inf"):
        raise argparse.ArgumentTypeError("must be a finite positive number")
    return value


def parse_args(argv):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cwd", type=Path, default=Path.cwd())
    p.add_argument("--lock", type=Path, default=Path(os.environ.get(
        "AIR2LEAN_BUILD_LOCK", str(Path.home() / ".cache/air2lean/build.lock"))))
    p.add_argument("--report", type=Path, required=True)
    p.add_argument("--log", type=Path, required=True)
    p.add_argument("--timeout", type=positive, default=900)
    p.add_argument("--rss-mib", type=positive, default=8192)
    p.add_argument("--interval", type=positive, default=0.25)
    p.add_argument("--grace", type=positive, default=2)
    p.add_argument("--jobs", type=int, default=1,
                   help="parallel jobs the workload may run (AIR2LEAN_JOBS, leaf Zig compilers)")
    p.add_argument("--lean-threads", type=int, default=1, help="LEAN_NUM_THREADS of the workload")
    p.add_argument("--lock-wait", type=float, default=0)
    p.add_argument("--mem-budget-mib", type=positive, default=None,
                   help="memory budget of all guarded workloads (AIR2LEAN_BUILD_MEM_MIB, else 75%% of RAM)")
    p.add_argument("--exclusive", action="store_true",
                   help="run alone: no other guarded workload of this lock meanwhile (timing runs)")
    p.add_argument("--shared-workspace", action="store_true",
                   help="share the Lake workspace with other shared workloads (writes nothing Lake owns)")
    p.add_argument("--log-bytes", type=int, default=1024 * 1024)
    p.add_argument("--profile", default="manual")
    p.add_argument("--phase", choices=("build", "parse", "normalize", "check", "emit", "proof"), default="build")
    p.add_argument("--cache", choices=("cold", "warm", "unspecified"), default="unspecified")
    p.add_argument("--input", type=Path, action="append", default=[])
    p.add_argument("--output", type=Path, action="append", default=[])
    p.add_argument("--tool", action="append", default=[])
    p.add_argument("--zig-name", action="append", default=[])
    p.add_argument("command", nargs=argparse.REMAINDER)
    a = p.parse_args(argv)
    if a.command[:1] == ["--"]:
        a.command = a.command[1:]
    if not a.command:
        p.error("a command is required after --")
    if not 1 <= a.jobs <= 256 or not 1 <= a.lean_threads <= 256:
        p.error("--jobs and --lean-threads must be between 1 and 256")
    if not 0 <= a.lock_wait < float("inf") or not 0 <= a.log_bytes <= 16 * 1024 * 1024:
        p.error("invalid lock wait or log size (maximum 16 MiB)")
    if len(json.dumps(a.command).encode()) > 32 * 1024 or len(a.profile) > 128:
        p.error("command/profile exceeds evidence limits")
    if len(a.input) > 32 or len(a.output) > 32 or len(a.tool) > 32 or len(a.zig_name) > 32:
        p.error("at most 32 inputs, outputs, tools or extra Zig names")
    if len(json.dumps([str(path) for path in [a.cwd, a.lock, a.report, a.log, *a.input, *a.output]]
                      + a.tool + a.zig_name).encode()) > 16 * 1024:
        p.error("metadata paths exceed evidence limits")
    if a.mem_budget_mib is None:
        try:
            a.mem_budget_mib = default_budget_mib()
        except argparse.ArgumentTypeError as error:
            p.error(f"AIR2LEAN_BUILD_MEM_MIB {error}")
    a.cwd = a.cwd.resolve()
    a.lock = a.lock.expanduser().resolve()
    a.report = a.report.resolve()
    a.log = a.log.resolve()
    if a.report == a.log or a.lock in (a.report, a.log):
        p.error("lock, report and log must be distinct files")
    paths = (a.lock, a.report, a.log)
    for i, path in enumerate(paths):
        if path.exists() and not stat.S_ISREG(path.stat().st_mode):
            p.error("lock, report and log must be regular files")
        for other in paths[i + 1:]:
            if path.exists() and other.exists() and os.path.samefile(path, other):
                p.error("lock, report and log must not be hard links to the same file")
    return a


# Exact common operand-consuming branches of cmdBuild in pinned 0.14.1,
# 0.15.2 and 0.16.0 src/main.zig. Later build-runner options are not this parser.
FRONTEND_VALUES = frozenset({"--build-file", "--zig-lib-dir", "--build-runner",
                             "--cache-dir", "--global-cache-dir", "--system",
                             "--debug-log", "--debug-target", "--color", "--seed"})
FRONTEND_STAGES = (FRONTEND_VALUES, FRONTEND_VALUES | {"--debug-libc"})  # 14; 15/16
RUNNER_VALUES = FRONTEND_VALUES | {"-p", "--prefix", "--prefix-lib-dir", "--prefix-exe-dir",
                                  "--prefix-include-dir", "--sysroot", "--search-prefix", "--libc",
                                  "--summary", "--maxrss", "--debounce", "--port",
                                  "--libc-runtimes", "--glibc-runtimes", "--test-timeout",
                                  "--error-style", "--multiline-errors"}


def validate_build_tokens(arguments, values):
    i = 0
    while i < len(arguments):
        arg = arguments[i]
        if arg == "--":
            return  # only a boundary not already consumed as an option value
        if arg.startswith("@"):
            raise ValueError("zig build response files before -- are unsupported")
        if arg in values:
            if i + 1 == len(arguments):
                raise ValueError(f"missing zig build option value: {arg}")
            if arguments[i + 1].startswith("@"):
                raise ValueError("zig build response-like option values before -- are unsupported")
            i += 2
            continue
        if arg.startswith("-j") and arg != "-j1":
            raise ValueError("zig build must use -j1")
        i += 1


def sequential_command(command, zig_names):
    command = list(command)
    if Path(command[0]).name in zig_names and command[1:2] == ["build"]:
        # The frontend scans --prefix -j2 as a job override before the runner
        # consumes prefix's operand. Validate both stages before inserting -j1.
        for frontend in FRONTEND_STAGES:
            validate_build_tokens(command[2:], frontend)
            validate_build_tokens(command[2:], RUNNER_VALUES | frontend)
        command.insert(2, "-j1")
    return command


def write_chunk(output, report, limit, chunk):
    remaining = max(0, limit - report["output_bytes"])
    output.write(chunk[:remaining])
    report["output_bytes"] += len(chunk)


def drain_pipe(fd, output, report, limit, cancelled, deadline):
    # Cleanup may be unconfirmed: a surviving writer must never keep this
    # final phase running. Bound reads/bytes/time even if every read has data.
    for _ in range(16):
        if cancelled() or time.monotonic() >= deadline:
            return True
        try:
            chunk = os.read(fd, 65536)
        except BlockingIOError:
            return True
        if not chunk:
            return False
        write_chunk(output, report, limit, chunk)
    return True


SLOT_MIB = 1024


def physical_mib():
    try:
        return os.sysconf("SC_PHYS_PAGES") * os.sysconf("SC_PAGE_SIZE") // (1024 * 1024)
    except (ValueError, OSError):
        return 16 * 1024


def default_budget_mib():
    value = os.environ.get("AIR2LEAN_BUILD_MEM_MIB")
    return positive(value) if value else physical_mib() * 3 // 4


def workspace(cwd):
    """The Lake workspace a workload in cwd may write: the git top level (a check tree under a
    checkout's .lake and a package that requires the checkout by path, like tests/diff, write
    into it too), else cwd itself."""
    try:
        top = subprocess.run(["git", "-C", str(cwd), "rev-parse", "--show-toplevel"],
                             stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, timeout=5,
                             check=True, text=True).stdout.strip()
        return Path(top).resolve() if top else cwd
    except (OSError, subprocess.SubprocessError):
        return cwd


class Admission:
    """The locks a workload holds while it runs (module docstring). flock locks end with their
    descriptors, also when the guard dies; lock files are never unlinked (waiters reuse them)."""

    def __init__(self, a):
        self.a = a
        self.directory = Path(str(a.lock) + ".d")
        self.capacity = max(1, int(a.mem_budget_mib // SLOT_MIB))
        self.weight = self.capacity if a.exclusive else min(self.capacity, max(1, math.ceil(a.rss_mib / SLOT_MIB)))
        self.workspace = workspace(a.cwd)
        self.handles = []

    def evidence(self):
        return {"budget_mib": self.a.mem_budget_mib, "slot_mib": SLOT_MIB, "capacity": self.capacity,
                "weight": self.weight, "exclusive": self.a.exclusive, "workspace": str(self.workspace),
                "shared_workspace": self.a.shared_workspace}

    def open(self, name):
        handle = (self.directory / name if name else self.a.lock).open("a")
        self.handles.append(handle)
        return handle

    def acquire(self, cancelled):
        """None once every lock is held; "cancelled" or "lock_busy" (--lock-wait exceeded)."""
        deadline = time.monotonic() + self.a.lock_wait

        def wait():
            if cancelled[0]:
                return "cancelled"
            if time.monotonic() >= deadline:
                return "lock_busy"
            time.sleep(min(0.05, self.a.lock_wait))
            return "cancelled" if cancelled[0] else None

        def take(handle, mode):
            while True:
                if cancelled[0]:
                    return "cancelled"
                try:
                    fcntl.flock(handle, mode | fcntl.LOCK_NB)
                    return None
                except BlockingIOError:
                    if refused := wait():
                        return refused

        self.a.lock.parent.mkdir(parents=True, exist_ok=True)
        self.directory.mkdir(exist_ok=True)
        digest = hashlib.sha256(str(self.workspace).encode()).hexdigest()[:16]
        # The workspace first: waiting for one's own checkout must not hold up the queue.
        refused = take(self.open("ws-" + digest), fcntl.LOCK_SH if self.a.shared_workspace else fcntl.LOCK_EX)
        queue, main = self.open("queue"), self.open(None)
        if self.a.exclusive:
            # It waits until no other workload runs, but never while holding the queue: that would
            # stop every admission behind the longest running workload (a convoy). So it may wait
            # until --lock-wait on a machine that is never idle.
            while not refused:
                refused = take(queue, fcntl.LOCK_EX)
                if refused:
                    break
                try:
                    fcntl.flock(main, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    return None  # the queue is released below; the exclusive lock stays
                except BlockingIOError:
                    refused = None
                finally:
                    fcntl.flock(queue, fcntl.LOCK_UN)
                refused = wait()
            return refused
        refused = refused or take(queue, fcntl.LOCK_EX)
        refused = refused or take(main, fcntl.LOCK_SH)
        if refused:
            return refused
        # Only the queue holder collects, so slots taken so far stay taken until the rest free up.
        free, held = [self.open("slot-%03d" % i) for i in range(self.capacity)], 0
        while True:
            for handle in list(free):
                if held == self.weight:
                    break
                try:
                    fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    continue
                free.remove(handle)
                held += 1
            if held == self.weight:
                fcntl.flock(queue, fcntl.LOCK_UN)  # admitted: the next acquirer may collect
                return None
            if refused := wait():
                return refused

    def release(self):
        for handle in self.handles:
            handle.close()
        self.handles = []


def run(a):
    cancelled = [None]
    def cancel(sig, _frame):
        cancelled[0] = sig
    previous = {sig: signal.signal(sig, cancel) for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)}
    previous[signal.SIGCHLD] = signal.signal(signal.SIGCHLD, signal.SIG_DFL)
    lock = None
    child = None
    tree = None
    cleanup_confirmed = False
    selector = selectors.DefaultSelector()
    report = {"schema": 1, "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "cwd": str(a.cwd), "requested_command": a.command, "profile": a.profile,
              "phase": a.phase, "cache_label": a.cache,
              "host": {"system": platform.system(), "machine": platform.machine()},
              "budget": {"timeout_seconds": a.timeout, "rss_mib": a.rss_mib,
                         "sample_interval_seconds": a.interval, "term_grace_seconds": a.grace,
                         "jobs": a.jobs, "lean_threads": a.lean_threads},
              "lock": str(a.lock), "log": str(a.log), "outcome": "setup_error", "exit_code": 70,
              "child_status": None, "peak_sampled_rss_kib": 0, "samples": 0,
              "output_bytes": 0, "log_truncated": False, "drain_incomplete": False}
    started = time.monotonic()
    try:
        names = {"zig", "zig-air", "zig-unlocked", *a.zig_name}
        command = sequential_command(a.command, names)
        lock = Admission(a)
        report["admission"] = lock.evidence()
        lock_start = time.monotonic()
        refused = lock.acquire(cancelled)
        if refused == "cancelled":
            report.update(outcome="cancelled", exit_code=128 + cancelled[0])
            return report
        if refused:
            report.update(outcome="lock_busy", exit_code=75)
            return report
        report["lock_wait_seconds"] = round(time.monotonic() - lock_start, 3)
        # Execution fingerprints belong to the acquired-lock state, not the
        # state before a different worktree's build finished.
        report["command"] = command
        fingerprints = {}
        report["guard"] = file_evidence(__file__, fingerprints)
        report["revision"] = revision(a.cwd)
        report["inputs"] = [file_evidence(a.cwd / path, fingerprints) for path in a.input]
        tools = [command[0], sys.executable, "ps", *a.tool]
        report["tools"] = [file_evidence(path, fingerprints) if (path := executable(tool, a.cwd)) else
                           {"requested": tool, "unavailable": True} for tool in tools]
        for path in ("lean-toolchain", "zig-patch/versions.toml"):
            if (a.cwd / path).is_file():
                report.setdefault("pins", []).append(file_evidence(a.cwd / path, fingerprints))
        if cancelled[0]:
            report.update(outcome="cancelled", exit_code=128 + cancelled[0])
            return report
        a.log.parent.mkdir(parents=True, exist_ok=True)
        with a.log.open("wb") as output:
            # scripts/par.py sizes its worker pool by AIR2LEAN_JOBS and AIR2LEAN_MEM_MIB.
            # AIR2LEAN_GUARD_MODE tells a timing workload whether it runs alone (--exclusive).
            overrides = {"LEAN_NUM_THREADS": str(a.lean_threads), "ELAN_NO_OVERRIDE_NOTICE": "1",
                         "AIR2LEAN_JOBS": str(a.jobs), "AIR2LEAN_MEM_MIB": str(int(a.rss_mib)),
                         "AIR2LEAN_GUARD_MODE": "exclusive" if a.exclusive else "shared"}
            env = os.environ | overrides
            report["environment_overrides"] = overrides
            try:
                child = subprocess.Popen(command, cwd=a.cwd, env=env, stdout=subprocess.PIPE,
                                         stderr=subprocess.STDOUT, start_new_session=True)
            except OSError as error:
                report.update(outcome="spawn_error", exit_code=127, error=str(error)[:256])
                return report
            report["drain_incomplete"] = True
            tree = Tree(child.pid)
            os.set_blocking(child.stdout.fileno(), False)
            selector.register(child.stdout, selectors.EVENT_READ)
            build_start = time.monotonic()
            next_sample = build_start
            reason = None
            code = None
            while True:
                now = time.monotonic()
                if cancelled[0]:
                    reason, code = "cancelled", 128 + cancelled[0]
                elif now - build_start >= a.timeout:
                    reason, code = "timeout", 124
                if now >= next_sample:
                    rows = processes()
                    owned = tree.owned(rows)
                    rss = sum(rows[pid]["rss_kib"] for pid in owned)
                    report["samples"] += 1
                    report["peak_sampled_rss_kib"] = max(report["peak_sampled_rss_kib"], rss)
                    next_sample = now + a.interval
                    if not reason and rss > a.rss_mib * 1024:
                        reason, code = "rss_limit", 125
                    if not reason and parallel_zig(rows, owned, names, a.jobs):
                        reason, code = "parallel_zig", 126
                status = peek_status(child)
                if reason:
                    cleanup_confirmed = stop_tree(child, tree, a.grace)
                    break
                if status is not None:
                    rows = processes()
                    if tree.owned(rows):
                        reason, code = "orphaned_children", 71
                        cleanup_confirmed = stop_tree(child, tree, a.grace)
                    else:
                        cleanup_confirmed = True
                        reason = "success" if status == 0 else "child_failed"
                        code = status if status >= 0 else 128 - status
                    break
                for key, _events in selector.select(min(a.interval, 0.05)):
                    # Bounded read batches allow cancellation even with endless output.
                    for _ in range(16):
                        try:
                            chunk = os.read(key.fd, 65536)
                        except BlockingIOError:
                            break
                        if not chunk:
                            selector.unregister(key.fileobj)
                            break
                        write_chunk(output, report, a.log_bytes, chunk)
            report["drain_incomplete"] = drain_pipe(
                child.stdout.fileno(), output, report, a.log_bytes, lambda: cancelled[0],
                min(time.monotonic() + 0.05, build_start + a.timeout))
            if cancelled[0]:
                reason, code = "cancelled", 128 + cancelled[0]
            report.update(outcome=reason, exit_code=code, child_status=peek_status(child),
                          workload_seconds=round(time.monotonic() - build_start, 3),
                          log_truncated=report["output_bytes"] > a.log_bytes or report["drain_incomplete"])
        report["log_sha256"] = digest(a.log)
        report["log_bytes"] = a.log.stat().st_size
        report["outputs"] = [file_evidence(a.cwd / path) for path in a.output]
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        report.update(outcome="guard_error", exit_code=70, error=str(error)[:256])
    finally:
        if child is not None:
            try:
                if not cleanup_confirmed and not stop_tree(child, tree, a.grace):
                    report.update(outcome="cleanup_failed", exit_code=70)
            except (OSError, RuntimeError, subprocess.SubprocessError) as error:
                report.update(outcome="cleanup_failed", exit_code=70, error=str(error)[:256])
            finally:
                try:
                    report["child_status"] = child.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    report.update(outcome="cleanup_failed", exit_code=70)
                child.stdout.close()
        selector.close()
        if lock is not None:
            lock.release()
        for sig, handler in previous.items():
            signal.signal(sig, handler)
        report["log_truncated"] = report["output_bytes"] > a.log_bytes or report["drain_incomplete"]
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        atomic_report(a.report, report)
    return report


def main():
    a = parse_args(sys.argv[1:])
    report = run(a)
    print(json.dumps({key: report[key] for key in ("outcome", "exit_code", "elapsed_seconds", "peak_sampled_rss_kib")}))
    return report["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
