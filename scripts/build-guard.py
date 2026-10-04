#!/usr/bin/env python3
"""Serialize POSIX build workloads and record reactive resource-budget evidence."""

import argparse
import datetime
import fcntl
import hashlib
import json
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


def parallel_zig(rows, owned, names):
    # Linux comm truncates to 15 bytes. Prefix collisions are intentionally
    # conservative: refusing ambiguous parallel work is safer than missing it.
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
    return len(zig - ancestors) > 1


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
    p.add_argument("--lock-wait", type=float, default=0)
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
    if not 0 <= a.lock_wait < float("inf") or not 0 <= a.log_bytes <= 16 * 1024 * 1024:
        p.error("invalid lock wait or log size (maximum 16 MiB)")
    if len(json.dumps(a.command).encode()) > 32 * 1024 or len(a.profile) > 128:
        p.error("command/profile exceeds evidence limits")
    if len(a.input) > 32 or len(a.output) > 32 or len(a.tool) > 32 or len(a.zig_name) > 32:
        p.error("at most 32 inputs, outputs, tools or extra Zig names")
    if len(json.dumps([str(path) for path in [a.cwd, a.lock, a.report, a.log, *a.input, *a.output]]
                      + a.tool + a.zig_name).encode()) > 16 * 1024:
        p.error("metadata paths exceed evidence limits")
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


def sequential_command(command, zig_names):
    command = list(command)
    if Path(command[0]).name in zig_names and command[1:2] == ["build"]:
        # Inject the actual build option at a guaranteed option position. A
        # value named -j1 or an application argument after -- is not this flag.
        values = {"-p", "--prefix", "--prefix-lib-dir", "--prefix-exe-dir",
                  "--prefix-include-dir", "--sysroot", "--search-prefix", "--libc",
                  "--zig-lib-dir", "--build-file", "--cache-dir", "--global-cache-dir",
                  "--color", "--summary", "--seed", "--maxrss", "--debug-log"}
        result = command[:2] + ["-j1"]
        i = 2
        while i < len(command):
            arg = command[i]
            if arg == "--":
                result.extend(command[i:])
                break
            if arg in values:
                if i + 1 == len(command):
                    raise ValueError(f"missing zig build option value: {arg}")
                result.extend(command[i:i + 2])
                i += 2
                continue
            if arg.startswith("@"):
                raise ValueError("zig build response files can hide parallel job options")
            if arg.startswith("-j"):
                jobs = command[i + 1] if arg == "-j" and i + 1 < len(command) else arg[2:]
                if jobs != "1":
                    raise ValueError("zig build must use -j1")
                i += 2 if arg == "-j" else 1
                continue
            result.append(arg)
            i += 1
        command = result
    return command


def write_chunk(output, report, limit, chunk):
    remaining = max(0, limit - report["output_bytes"])
    output.write(chunk[:remaining])
    report["output_bytes"] += len(chunk)


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
                         "sample_interval_seconds": a.interval, "term_grace_seconds": a.grace},
              "lock": str(a.lock), "log": str(a.log), "outcome": "setup_error", "exit_code": 70,
              "child_status": None, "peak_sampled_rss_kib": 0, "samples": 0,
              "output_bytes": 0, "log_truncated": False}
    started = time.monotonic()
    try:
        names = {"zig", "zig-air", "zig-unlocked", *a.zig_name}
        command = sequential_command(a.command, names)
        a.lock.parent.mkdir(parents=True, exist_ok=True)
        lock = a.lock.open("a")
        lock_start = time.monotonic()
        while True:
            if cancelled[0]:
                report.update(outcome="cancelled", exit_code=128 + cancelled[0])
                return report
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                if time.monotonic() - lock_start >= a.lock_wait:
                    report.update(outcome="lock_busy", exit_code=75)
                    return report
                time.sleep(min(0.05, a.lock_wait))
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
            overrides = {"LEAN_NUM_THREADS": "1", "ELAN_NO_OVERRIDE_NOTICE": "1"}
            env = os.environ | overrides
            report["environment_overrides"] = overrides
            try:
                child = subprocess.Popen(command, cwd=a.cwd, env=env, stdout=subprocess.PIPE,
                                         stderr=subprocess.STDOUT, start_new_session=True)
            except OSError as error:
                report.update(outcome="spawn_error", exit_code=127, error=str(error)[:256])
                return report
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
                    if not reason and parallel_zig(rows, owned, names):
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
            # Drain output already in the pipe after the entire workload stopped.
            while True:
                try:
                    chunk = os.read(child.stdout.fileno(), 65536)
                except BlockingIOError:
                    break
                if not chunk:
                    break
                write_chunk(output, report, a.log_bytes, chunk)
            report.update(outcome=reason, exit_code=code, child_status=peek_status(child),
                          workload_seconds=round(time.monotonic() - build_start, 3),
                          log_truncated=report["output_bytes"] > a.log_bytes)
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
            lock.close()  # never unlink a flock inode: concurrent waiters reuse it
        for sig, handler in previous.items():
            signal.signal(sig, handler)
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
