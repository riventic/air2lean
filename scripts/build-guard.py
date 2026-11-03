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
- Fairness: acquirers queue on `<lock>.d/queue`; the one holding it (the head) collects its slots
  while later ones wait behind it, so a large workload is not starved by small ones.
- Backfill: short of its slots, the head keeps only a reservation, ceil(weight x waited /
  --backfill-ramp) slots (default 900 s; all of them from then on), and publishes the part of it
  that it does not hold yet in `<lock>.d/heads/` (flock-held). A normal guard waiting behind it,
  with no drain ticket queued, may run ahead in what is left: it takes all its slots at once, and
  only when the head's published unmet reservation is free besides them (serialized by
  `<lock>.d/register`). So the head's admission is never delayed by more than the ramp plus the
  backfilled workloads already running, each bounded by its --timeout. A queue holder that
  publishes nothing (a guard of an older checkout) gets no backfill.
- Drain tickets: a merge guard (AIR2LEAN_GUARD_PRIORITY=merge or --priority merge, only for the
  coordinator's integration gate) and an `--exclusive` guard take a ticket
  `<lock>.d/merge/<ns>-<pid>-<lane>`, flock-held by its guard. While a ticket is queued no normal
  guard is admitted, and one still collecting slots gives them back (it runs nothing yet); running
  workloads are never touched. Tickets are served in arrival order, merge and exclusive alike: the
  head merge guard collects its slots, the head exclusive guard holds the queue until every
  running workload has ended and then runs alone. So an exclusive guard waits at most for the
  longest running workload plus the ticket holders ahead of it, a merge guard for the ones ahead
  of it; neither lane can starve the other (a strict priority either way would let a stream of
  one lane starve the other). Without a ticket the order is that of normal guards. A dead guard's
  ticket is not held, so the next guard to look removes it. The directory keeps its name from
  the merge lane: guards of checkouts since then treat every ticket as a merge ticket, so they
  wait behind an exclusive one too.
- Usage-aware charge (Linux only). --rss-mib stays the hard limit, but a workload whose command
  ran before is charged its measured need instead: the guard keeps the last 5 runs of each
  command (`<lock>.d/history/<key>.json`; the key is the command with its workspace path
  abstracted, its directory in the workspace, the phase, profile, jobs and Lean threads), and
  after 2 successes among them, with none stopped at its limit, preempted or SIGKILLed (exit 137,
  the OOM killer), it holds the slots of ceil(1.3 x the largest sampled peak of those successes)
  MiB instead of those of --rss-mib. The declared limits of the running workloads still add up to
  at most 1.5 x the budget: an overcommitted workload registers its excess (declared minus held
  slots) in `<lock>.d/running/`, flock-held, the registered excess stays within 0.5 x the budget,
  and a workload that would break that holds its declared slots instead. Backstop: when
  MemAvailable falls below max(2 GiB, 10% of RAM), the youngest overcommitted workload is stopped
  (outcome `preempted`, at most one per 5 s and lock) and the guard runs it again holding its
  declared slots, within what is left of --lock-wait and --timeout; the report keeps the stopped
  run in `preempted_run`, the log its output. Never overcommitted: macOS (no MemAvailable), a
  cgroup-limited process (a container's --memory: MemAvailable does not show it), --lock-wait 0
  (a preempted run could not wait), --exclusive and --no-overcommit.
Never take a private lock lane (another AIR2LEAN_BUILD_LOCK) to get around a wait: the budget
is only a bound when every heavy workload of the machine goes through the same lock.
--lock-wait bounds the whole admission; exit 75 (lock_busy) when it is exceeded."""

import argparse
import contextlib
import datetime
import fcntl
import hashlib
import importlib.util
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


# One ps attempt gets PS_TIMEOUT seconds: on the shared dev Mac under heavy load ps took more
# than 5 s. The memory cap must not stay unenforced for long, so the sampling loop tolerates
# failed or slow samples only for SAMPLE_STALE seconds since the last good sample: four full
# attempts, so ps stalls of ~10-15 s (seen under load) are ridden out, while the cap is never
# blind for much longer than a minute, after that the guard stops the workload (guard_error).
PS_TIMEOUT = 15
SAMPLE_STALE = 60


def processes(timeout=PS_TIMEOUT):
    # Both macOS and Linux ps provide these columns. lstart distinguishes reused
    # PIDs when following observed descendants; it has one-second resolution.
    env = os.environ | {"LC_ALL": "C"}
    result = subprocess.run(["ps", "-axo", "pid=,ppid=,pgid=,rss=,lstart=,stat=,comm="],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=timeout, check=True, text=True, env=env)
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


def signal_workload(child, tree, sig, ps_timeout=PS_TIMEOUT):
    try:
        rows = processes(ps_timeout)
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


def stop_tree(child, tree, grace, ps_timeout=PS_TIMEOUT):
    # Keep the global lock until both the leader and observed descendants stop.
    # If ps fails, the original group can still be stopped without guessing PIDs.
    signal_workload(child, tree, signal.SIGTERM, ps_timeout)
    end = time.monotonic() + grace
    while time.monotonic() < end:
        try:
            rows = processes(ps_timeout)
            owned = tree.owned(rows)
            if not owned:
                return True
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError):
            pass
        time.sleep(min(0.05, max(0, end - time.monotonic())))
    signal_workload(child, tree, signal.SIGKILL, ps_timeout)
    end = time.monotonic() + 5
    while time.monotonic() < end:
        try:
            if not tree.owned(processes(ps_timeout)):
                return True
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError):
            return False
        time.sleep(0.01)
    return False


class Sampler:
    """Process tables for the monitoring loop. A failed or slow ps is retried at the next
    sample and the last good table is not reused; only when no sample succeeded for `stale`
    seconds does it raise (the guard then aborts and stops the workload)."""

    def __init__(self, ps_timeout, stale):
        self.ps_timeout = ps_timeout
        self.stale = stale
        self.last_good = time.monotonic()
        self.failures = 0

    def sample(self):
        """The rows, or None for a failed sample inside the stale window."""
        try:
            rows = processes(self.ps_timeout)
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
            self.failures += 1
            if time.monotonic() - self.last_good >= self.stale:
                raise RuntimeError(f"no process sample for {self.stale} s, last error: "
                                   f"{type(error).__name__} {error}"[:256]) from error
            return None
        self.last_good = time.monotonic()
        return rows

    def require(self):
        """Rows of a decision that cannot be made without them (the workload has exited)."""
        while (rows := self.sample()) is None:
            time.sleep(0.05)
        return rows


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


PRIORITIES = ("normal", "merge")


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
    p.add_argument("--ps-timeout", type=positive, default=PS_TIMEOUT,
                   help="seconds one ps sample may take")
    p.add_argument("--sample-stale", type=positive, default=SAMPLE_STALE,
                   help="abort when no ps sample succeeded for this many seconds")
    p.add_argument("--jobs", type=int, default=1,
                   help="parallel jobs the workload may run (AIR2LEAN_JOBS, leaf Zig compilers)")
    p.add_argument("--lean-threads", type=int, default=1, help="LEAN_NUM_THREADS of the workload")
    p.add_argument("--lock-wait", type=float, default=0)
    p.add_argument("--mem-budget-mib", type=positive, default=None,
                   help="memory budget of all guarded workloads (AIR2LEAN_BUILD_MEM_MIB, else 75%% of RAM)")
    p.add_argument("--exclusive", action="store_true",
                   help="run alone: no other guarded workload of this lock meanwhile (timing runs); "
                        "while it waits, no new workload is admitted")
    p.add_argument("--no-overcommit", action="store_true",
                   help="hold the slots of --rss-mib, whatever earlier runs of the command needed")
    p.add_argument("--backfill-ramp", type=float, default=BACKFILL_RAMP,
                   help="seconds over which a waiting queue head's reservation grows to all its slots "
                        "(backfill: smaller workloads may run in the rest meanwhile; 0: reserve at once)")
    p.add_argument("--shared-workspace", action="store_true",
                   help="share the Lake workspace with other shared workloads (writes nothing Lake owns)")
    p.add_argument("--priority", choices=PRIORITIES, default=None,
                   help="admission lane (AIR2LEAN_GUARD_PRIORITY, else normal); merge is only for the "
                        "coordinator's integration gate")
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
    if a.priority is None:
        a.priority = os.environ.get("AIR2LEAN_GUARD_PRIORITY") or "normal"
        if a.priority not in PRIORITIES:
            p.error(f"AIR2LEAN_GUARD_PRIORITY must be one of {', '.join(PRIORITIES)}")
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


def default_lock():
    return Path(os.environ.get("AIR2LEAN_BUILD_LOCK", str(Path.home() / ".cache/air2lean/build.lock")))


def free_mib(lock=None, budget_mib=None):
    """MiB of the budget no guarded workload holds right now: the slots nobody has locked (a
    snapshot, for sizing a workload before it asks for admission; admission itself still waits
    for the slots it requests)."""
    lock = (lock or default_lock()).expanduser()
    capacity = max(1, int((budget_mib or default_budget_mib()) // SLOT_MIB))
    directory = Path(str(lock) + ".d")
    free = 0
    for i in range(capacity):
        try:
            with (directory / ("slot-%03d" % i)).open("a") as handle:
                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                free += 1  # closing the descriptor releases it
        except BlockingIOError:
            pass
        except FileNotFoundError:
            free += 1  # no guard has used this lock yet
    return free * SLOT_MIB


def lake_cache_env():
    """Lake's artifact cache settings of scripts/cas.py run when AIR2LEAN_CAS_DIR is set, else
    none, so every Lake of one guarded workload runs in the same mode. In one checkout Lake can
    judge a module up to date with the cache and stale without it. A workload that ran some Lake
    builds through `cas.py run` (scripts/fixtures.py) and others plain (the extractor's own build,
    scripts/assumptions.py) rebuilt root modules in place between a compiler-owned audit's
    binding and its check ("compiler-owned Unit imported inputs changed"), and under the units
    running beside it."""
    if not os.environ.get("AIR2LEAN_CAS_DIR"):
        return {}
    path = Path(__file__).with_name("cas.py")
    if not path.is_file():
        return {}
    spec = importlib.util.spec_from_file_location("air2lean_cas", path)
    cas = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cas)
    return cas.lake_env()


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


# Usage-aware charge (module docstring).
HISTORY_RUNS = 5        # recent runs of a command kept and considered
CHARGE_MARGIN = 1.3     # charge = margin x the largest recent peak
DECLARED_BOUND = 1.5    # declared limits of the running workloads <= bound x budget
PREEMPT_HOLDOFF = 5     # seconds between two preemptions under one lock
BACKFILL_RAMP = 900     # seconds after which the queue head reserves all its slots (--backfill-ramp)
BACKFILL_EVERY = 1.0    # seconds between two backfill attempts of one waiting guard
UNSAFE_OUTCOMES = ("rss_limit", "preempted")
KILLED = 128 + signal.SIGKILL  # exit code of a workload SIGKILLed from outside (the OOM killer)


def command_key(a, workspace):
    """The history key: the command (its workspace path abstracted, so every checkout of one
    command shares it), its directory in the workspace and what else shapes its memory."""
    command = [part.replace(str(workspace), "<workspace>") for part in a.command]
    text = json.dumps([command, os.path.relpath(a.cwd, workspace), a.phase, a.profile, a.jobs, a.lean_threads])
    return hashlib.sha256(text.encode()).hexdigest()[:32]


def history_charge(runs, declared_mib):
    """(MiB to hold, None) from a command's recent runs, or (declared_mib, why not less). Only
    successes measure the need; a run stopped at its limit, preempted or SIGKILLed (exit 137, the
    OOM killer) keeps the command at its declared charge while it is among the recent runs."""
    recent = [run for run in runs[-HISTORY_RUNS:] if isinstance(run, dict)]
    if any(run.get("outcome") in UNSAFE_OUTCOMES or run.get("exit_code") == KILLED for run in recent):
        return declared_mib, "a recent run hit its limit, was preempted or was killed"
    peaks = [run["peak_mib"] for run in recent
             if run.get("outcome") == "success" and isinstance(run.get("peak_mib"), (int, float))]
    if len(peaks) < 2:
        return declared_mib, "fewer than 2 recent successes"
    return min(declared_mib, max(SLOT_MIB, math.ceil(CHARGE_MARGIN * max(peaks)))), None


def read_runs(handle):
    """The run list of a history file (anything else reads as none)."""
    try:
        runs = json.loads(handle.read() or "[]")
    except ValueError:
        return []
    return runs if isinstance(runs, list) else []


def cgroup_limited():
    """Whether a cgroup limits this process's memory below the machine's (a container's
    --memory, a systemd slice): MemAvailable does not show the pressure of that limit."""
    try:
        lines = Path("/proc/self/cgroup").read_text().splitlines()
    except OSError:
        return False
    machine = physical_mib() * 1024 * 1024
    for line in lines:
        _, controllers, path = line.split(":", 2)
        if controllers == "":  # cgroup v2
            root, name = Path("/sys/fs/cgroup"), "memory.max"
        elif "memory" in controllers.split(","):
            root, name = Path("/sys/fs/cgroup/memory"), "memory.limit_in_bytes"
        else:
            continue
        group = Path(path)
        for directory in (group, *group.parents):  # the limit of any enclosing group applies
            try:
                value = (root / directory.relative_to("/") / name).read_text().strip()
            except (OSError, ValueError):
                continue
            if value != "max" and value.isdigit() and int(value) < machine:
                return True
    return False


def mem_available_mib():
    """MemAvailable of /proc/meminfo in MiB; None without one (macOS)."""
    try:
        with open("/proc/meminfo") as handle:
            for line in handle:
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) // 1024
    except (OSError, ValueError, IndexError):
        pass
    return None


def backstop_mib():
    return max(2048, physical_mib() // 10)


def held_entries(directory):
    """{name: JSON content} of the entries of a registry directory (merge tickets, overcommitted
    workloads), oldest first by name. Their guards hold their flocks (also against their own
    later opens), so an entry nobody holds belongs to a dead guard: it is removed."""
    try:
        names = sorted(name for name in os.listdir(directory) if not name.startswith("."))
    except FileNotFoundError:
        return {}
    entries = {}
    for name in names:
        try:
            with (directory / name).open("rb") as handle:
                try:
                    fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    entry = json.loads(handle.read() or "{}")
                    entries[name] = entry if isinstance(entry, dict) else {}
                    continue
                (directory / name).unlink(missing_ok=True)
        except (FileNotFoundError, ValueError):
            pass
    return entries


def publish_entry(directory, name, content, handle_of):
    """Create directory/name holding content, flock-held through handle_of(path): it is written
    and locked under a hidden name and renamed only then, so no reader takes it for a dead one."""
    directory.mkdir(exist_ok=True)
    handle = handle_of(directory / ("." + name))
    fcntl.flock(handle, fcntl.LOCK_EX)
    handle.write(json.dumps(content))
    handle.flush()
    os.rename(directory / ("." + name), directory / name)
    return handle


class Admission:
    """The locks a workload holds while it runs (module docstring). flock locks end with their
    descriptors, also when the guard dies; lock files are never unlinked (waiters reuse them)."""

    def __init__(self, a):
        self.a = a
        self.directory = Path(str(a.lock) + ".d")
        self.capacity = max(1, int(a.mem_budget_mib // SLOT_MIB))
        self.declared = self.capacity if a.exclusive else self.slots(a.rss_mib)
        self.weight = self.declared  # the slots it holds: `plan` may charge fewer
        self.workspace = workspace(a.cwd)
        self.history = self.directory / "history" / (command_key(a, self.workspace) + ".json")
        self.running = self.directory / "running"
        self.registered = None  # its entry in `running` while it is overcommitted
        self.overcommit = False
        self.why_declared = self.charge_mib = self.history_runs = self.preempted_at_mib = None
        self.backstop = backstop_mib()
        self.next_backstop_check = 0.0
        # The admission lane: an exclusive guard drains in arrival order with merge guards, so a
        # merge priority adds nothing to it.
        self.priority = "exclusive" if a.exclusive else a.priority
        self.tickets = self.directory / "merge"
        self.ticket = None
        self.heads = self.directory / "heads"
        self.head = None  # (entry name, handle, unmet slots) while this guard is the waiting queue head
        self.backfilled = False
        self.next_backfill = 0.0
        self.waited = False
        self.handles = []

    def slots(self, mib):
        return min(self.capacity, max(1, math.ceil(mib / SLOT_MIB)))

    def evidence(self):
        return {"budget_mib": self.a.mem_budget_mib, "slot_mib": SLOT_MIB, "capacity": self.capacity,
                "weight": self.weight, "exclusive": self.a.exclusive, "workspace": str(self.workspace),
                "shared_workspace": self.a.shared_workspace, "priority": self.priority,
                "declared_slots": self.declared, "overcommit": self.overcommit,
                "charge_mib": self.charge_mib, "history_runs": self.history_runs,
                "why_declared": self.why_declared, "preempted_at_available_mib": self.preempted_at_mib,
                "backfilled": self.backfilled}

    def open(self, name):
        """A handle on `<lock>.d/name` (a path: that path; None: `<lock>`), held until release."""
        handle = (self.directory / name if name else self.a.lock).open("a")
        self.handles.append(handle)
        return handle

    def runs(self):
        """The recorded recent runs of this guard's command (oldest first)."""
        try:
            with self.history.open() as handle:
                fcntl.flock(handle, fcntl.LOCK_SH)
                return read_runs(handle)
        except FileNotFoundError:
            return []

    def record(self, report):
        """Append this run (outcome, exit code, sampled peak) to the command's history."""
        peak = math.ceil(report["peak_sampled_rss_kib"] / 1024) if report["samples"] else None
        self.history.parent.mkdir(exist_ok=True)
        with self.history.open("a+") as handle:
            fcntl.flock(handle, fcntl.LOCK_EX)
            handle.seek(0)
            runs = read_runs(handle)[-(HISTORY_RUNS - 1):]
            runs.append({"utc": report["started_utc"], "outcome": report["outcome"],
                         "exit_code": report["exit_code"], "peak_mib": peak})
            handle.seek(0)
            handle.truncate()
            handle.write(json.dumps(runs))

    def overcommit_refused(self):
        """Why this guard holds its declared slots whatever its history says, else None."""
        if self.a.exclusive:
            return "--exclusive"
        if self.a.no_overcommit:
            return "--no-overcommit"
        if not self.a.lock_wait:
            return "--lock-wait 0 (a preempted run could not wait to run again)"
        if mem_available_mib() is None:
            return "no MemAvailable (not Linux)"
        if cgroup_limited():
            return "a cgroup memory limit (MemAvailable does not show its pressure)"
        return None

    def plan(self):
        """Charge the command's measured need when its history allows (module docstring)."""
        if refused := self.overcommit_refused():
            self.why_declared = refused
            return
        runs = self.runs()
        self.history_runs = len(runs[-HISTORY_RUNS:])
        self.charge_mib, self.why_declared = history_charge(runs, self.a.rss_mib)
        self.weight = self.slots(self.charge_mib)

    def within_bound(self):
        """Whether the declared limits of the running workloads stay within DECLARED_BOUND x the
        budget with this one overcommitted. Held slots never exceed the budget, so it suffices that
        the excess of the overcommitted workloads (declared minus held slots, registered under
        `registry`) stays within (DECLARED_BOUND - 1) x the budget, whatever else is admitted
        (guards at their declared charge, guards of older checkouts)."""
        excess = sum(entry.get("excess_slots", 0) for entry in held_entries(self.running).values())
        return excess + self.declared - self.weight <= (DECLARED_BOUND - 1) * self.capacity

    def register(self):
        """Publish this workload's excess (declared minus held slots) while it runs."""
        name = "%020d-%d" % (time.time_ns(), os.getpid())
        publish_entry(self.running, name, {"pid": os.getpid(), "excess_slots": self.declared - self.weight},
                      self.open)
        self.registered = name
        self.overcommit = True

    def unregister(self):
        if self.registered:
            (self.running / self.registered).unlink(missing_ok=True)
            self.registered = None

    def preempt(self):
        """The backstop: whether this workload is to stop now, being the youngest overcommitted
        workload while MemAvailable is below the backstop (at most one per PREEMPT_HOLDOFF). The
        chosen one leaves the registry at once, so the next one can be chosen during its teardown.
        MemAvailable is read once a second; the choice is made under the marker's flock, so two
        guards never both choose within one hold-off."""
        if not self.registered or time.monotonic() < self.next_backstop_check:
            return False
        self.next_backstop_check = time.monotonic() + 1
        available = mem_available_mib()
        if available is None or available >= self.backstop:
            return False
        with (self.directory / "preempted").open("a+") as marker:  # the last preemption's time
            try:
                fcntl.flock(marker, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                return False  # another guard is choosing now
            marker.seek(0)
            try:
                last = float(marker.read() or 0)
            except ValueError:
                last = 0.0
            if time.time() - last < PREEMPT_HOLDOFF:
                return False
            if list(held_entries(self.running))[-1:] != [self.registered]:  # every entry is overcommitted
                return False
            marker.seek(0)
            marker.truncate()
            marker.write(str(time.time()))
        self.preempted_at_mib = available
        self.unregister()
        return True

    def queued_tickets(self):
        """Names of the tickets of the merge and exclusive guards waiting for admission, oldest
        first (`held_entries`)."""
        return list(held_entries(self.tickets))

    def join_queue(self):
        """Take a ticket named by the arrival time and the lane (`publish_entry`)."""
        name = "%020d-%d-%s" % (time.time_ns(), os.getpid(), self.priority)
        publish_entry(self.tickets, name, {}, self.open)
        self.ticket = name

    def leave_queue(self):
        if self.ticket:
            (self.tickets / self.ticket).unlink(missing_ok=True)
            self.ticket = None

    def my_turn(self):
        """Ticket holders go in arrival order and ahead of normal guards: a normal guard's turn
        comes when no ticket is queued."""
        queued = self.queued_tickets()
        return not queued or queued[0] == self.ticket

    @contextlib.contextmanager
    def registry(self):
        """The short lock under which an admission checks the declared bound and registers: the
        queue head and backfilling guards admit outside each other's queue lock."""
        with (self.directory / "register").open("a") as handle:
            fcntl.flock(handle, fcntl.LOCK_EX)
            yield

    def reservation(self, waited):
        """Slots the waiting queue head keeps after `waited` seconds: a share of its weight that
        grows linearly to all of it over --backfill-ramp."""
        if self.a.backfill_ramp <= 0 or waited >= self.a.backfill_ramp:
            return self.weight
        return min(self.weight, math.ceil(self.weight * waited / self.a.backfill_ramp))

    def publish_head(self, unmet):
        """As the waiting queue head, publish the slots it reserves but does not hold yet (a new
        entry, then the old one goes: a reader may count both, never neither)."""
        if self.head and self.head[2] == unmet:
            return
        name = "%020d-%d" % (time.time_ns(), os.getpid())
        handle = publish_entry(self.heads, name, {"pid": os.getpid(), "unmet": unmet}, self.open)
        self.clear_head()
        self.head = (name, handle, unmet)

    def clear_head(self):
        if self.head:
            name, handle, _ = self.head
            (self.heads / name).unlink(missing_ok=True)
            self.handles.remove(handle)
            handle.close()
            self.head = None

    def admit_overcommitted(self):
        """Under `registry`: register this workload's excess if it stays within the bound; else
        fall back to the declared slots (False: collect them first)."""
        if self.weight == self.declared:
            return True
        if self.within_bound():
            self.register()
            return True
        self.weight = self.declared
        self.why_declared = f"declared limits would exceed {DECLARED_BOUND} x budget"
        return False

    def backfill(self, main, slots, locked):
        """Whether this normal guard, waiting behind the queue head, ran ahead of it: it takes
        all its slots at once, and only if the head's unmet reservation stays free besides them,
        so the head is never delayed beyond its reservation. A queue holder that publishes no
        reservation (a guard of an older checkout) gets no backfill."""
        if self.a.exclusive or self.priority != "normal" or time.monotonic() < self.next_backfill:
            return False
        self.next_backfill = time.monotonic() + BACKFILL_EVERY
        with self.registry():
            heads = held_entries(self.heads)
            if not heads or not self.my_turn() or not locked(main, fcntl.LOCK_SH):
                fcntl.flock(main, fcntl.LOCK_UN)  # (a no-op unless held)
                return False
            need = self.weight + sum(max(0, int(entry.get("unmet", 0))) for entry in heads.values())
            taken = []
            for handle in slots:
                if len(taken) == need:
                    break
                if locked(handle, fcntl.LOCK_EX):
                    taken.append(handle)
            keep = taken[:self.weight] if len(taken) == need else []
            for handle in taken[len(keep):]:
                fcntl.flock(handle, fcntl.LOCK_UN)
            if keep and self.admit_overcommitted():
                self.backfilled = True
                return True
            for handle in (*keep, main):
                fcntl.flock(handle, fcntl.LOCK_UN)
            return False

    def announce(self):
        queued = self.queued_tickets()
        exclusive = sum(name.endswith("-exclusive") for name in queued)
        print(f"build-guard: waiting for admission, {self.priority} priority, {self.weight} slot(s), "
              f"{len(queued) - exclusive} merge and {exclusive} exclusive guard(s) queued: {self.a.cwd}",
              file=sys.stderr, flush=True)

    def acquire(self, cancelled):
        """None once every lock is held; "cancelled" or "lock_busy" (--lock-wait exceeded)."""
        deadline = time.monotonic() + self.a.lock_wait

        def wait():
            if cancelled[0]:
                return "cancelled"
            if time.monotonic() >= deadline:
                return "lock_busy"
            if not self.waited:
                self.waited = True
                self.announce()
            time.sleep(min(0.05, self.a.lock_wait))
            return "cancelled" if cancelled[0] else None

        def locked(handle, mode):
            try:
                fcntl.flock(handle, mode | fcntl.LOCK_NB)
                return True
            except BlockingIOError:
                return False

        def take(handle, mode):
            while True:
                if cancelled[0]:
                    return "cancelled"
                if locked(handle, mode):
                    return None
                if refused := wait():
                    return refused

        self.a.lock.parent.mkdir(parents=True, exist_ok=True)
        self.directory.mkdir(exist_ok=True)
        self.plan()
        started = time.monotonic()
        digest = hashlib.sha256(str(self.workspace).encode()).hexdigest()[:16]
        # The workspace first: waiting for one's own checkout must not hold up the queue.
        if refused := take(self.open("ws-" + digest), fcntl.LOCK_SH if self.a.shared_workspace else fcntl.LOCK_EX):
            return refused
        queue, main = self.open("queue"), self.open(None)
        # An exclusive guard collects `<lock>` itself instead of slots: nothing else runs then.
        slots = [] if self.a.exclusive else [self.open("slot-%03d" % i) for i in range(self.capacity)]
        if self.priority != "normal":
            self.join_queue()
        while True:
            while not self.my_turn():
                if refused := wait():
                    return refused
            # The queue holder (the head) collects; a guard waiting behind it may backfill.
            while not locked(queue, fcntl.LOCK_EX):
                if self.backfill(main, slots, locked):
                    return None
                if refused := wait():
                    return refused
            if not self.a.exclusive and (refused := take(main, fcntl.LOCK_SH)):
                return refused
            # Only the queue holder collects. Short of its weight it keeps its reservation (growing
            # with its wait) and publishes the part it lacks, which backfilling guards leave free.
            # An exclusive head keeps the queue and its ticket until the running workloads end
            # (the drain): no other guard is admitted meanwhile.
            free, held = list(slots), []
            while self.my_turn():
                if self.a.exclusive:
                    admitted = locked(main, fcntl.LOCK_EX)
                else:
                    for handle in list(free):
                        if len(held) < self.weight and locked(handle, fcntl.LOCK_EX):
                            free.remove(handle)
                            held.append(handle)
                    admitted = len(held) == self.weight
                    if admitted:
                        with self.registry():  # the bound, also against backfilling guards
                            admitted = self.admit_overcommitted()
                        if not admitted:
                            continue  # collect the declared slots
                    else:
                        keep = self.reservation(time.monotonic() - started)
                        while len(held) > keep:
                            handle = held.pop()
                            fcntl.flock(handle, fcntl.LOCK_UN)
                            free.append(handle)
                        self.publish_head(keep - len(held))
                if admitted:
                    self.clear_head()
                    fcntl.flock(queue, fcntl.LOCK_UN)  # admitted: the next acquirer may collect
                    self.leave_queue()
                    return None
                if refused := wait():
                    return refused
            # A ticket older than this guard's is queued, and this guard runs nothing yet: it gives
            # back what it collected so far and goes behind it. Running workloads are not touched.
            self.clear_head()
            for handle in (main, queue, *slots):
                fcntl.flock(handle, fcntl.LOCK_UN)

    def release(self):
        self.leave_queue()
        self.clear_head()
        self.unregister()
        for handle in self.handles:
            handle.close()
        self.handles = []

    def grant(self):
        """What a guard nested in this workload may inherit (INHERIT, `inherited`)."""
        return {"pid": os.getpid(), "lock": str(self.a.lock), "workspace": str(self.workspace),
                "rss_mib": self.a.rss_mib, "exclusive": self.a.exclusive,
                "shared_workspace": self.a.shared_workspace}


# A guard's workload runs with INHERIT set to its admission (`Admission.grant`). A guard started
# inside that workload (a phase of scripts/full-build.sh) holds no locks of its own: the outer
# guard's admission covers it when it is the same lock and Lake workspace, a limit within the
# outer one, no stronger exclusivity, and the granting guard is its ancestor. The outer guard
# keeps sampling the whole tree against its own limit; the nested one enforces its own limit and
# writes its own report. A nested guard of the same workspace that cannot inherit would wait for
# the workspace lock its ancestor holds: it fails instead (`inheritance_refused`, exit 75).
INHERIT = "AIR2LEAN_GUARD_ADMISSION"


def ancestors(pid=None):
    rows = processes()
    pid, seen = (os.getpid() if pid is None else pid), set()
    while pid in rows and pid not in seen and pid > 1:
        seen.add(pid)
        pid = rows[pid]["parent"]
    return seen | {pid}


def inherited(lock):
    """(grant, None) when the enclosing guard's admission covers this guard, (None, reason) when
    an enclosing guard of the same lock and workspace does not, (None, None) without one."""
    try:
        grant = json.loads(os.environ.get(INHERIT) or "null")
    except ValueError:
        grant = None
    if not isinstance(grant, dict) or grant.get("lock") != str(lock.a.lock) \
            or grant.get("workspace") != str(lock.workspace):
        return None, None
    try:
        if not isinstance(grant.get("pid"), int) or grant["pid"] not in ancestors():
            return None, None  # a stale variable, not an enclosing guard
    except (OSError, subprocess.SubprocessError, RuntimeError, ValueError):
        return None, "the enclosing guard could not be confirmed (ps failed)"
    if not isinstance(grant.get("rss_mib"), (int, float)) or lock.a.rss_mib > grant["rss_mib"]:
        return None, f"--rss-mib {lock.a.rss_mib} exceeds the enclosing guard's {grant.get('rss_mib')}"
    if lock.a.exclusive and not grant.get("exclusive"):
        return None, "--exclusive inside a shared admission"
    if not lock.a.shared_workspace and grant.get("shared_workspace"):
        return None, "an exclusive workspace inside a shared-workspace admission"
    return grant, None


def run(a, preempted=None):
    """One guarded run; `preempted`: the record of the run the backstop stopped before it."""
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
                         "ps_timeout_seconds": a.ps_timeout, "sample_stale_seconds": a.sample_stale,
                         "jobs": a.jobs, "lean_threads": a.lean_threads},
              "lock": str(a.lock), "log": str(a.log), "outcome": "setup_error", "exit_code": 70,
              "child_status": None, "peak_sampled_rss_kib": 0, "samples": 0, "failed_samples": 0,
              "output_bytes": 0, "log_truncated": False, "drain_incomplete": False}
    if preempted:
        report["preempted_run"] = preempted
    started = time.monotonic()
    try:
        names = {"zig", "zig-air", "zig-unlocked", *a.zig_name}
        command = sequential_command(a.command, names)
        lock = Admission(a)
        report["admission"] = lock.evidence()
        lock_start = time.monotonic()
        grant, reason = inherited(lock)
        if reason:
            print(f"build-guard: cannot run inside the enclosing guard's admission: {reason}",
                  file=sys.stderr, flush=True)
            report.update(outcome="inheritance_refused", exit_code=75, error=reason)
            return report
        if grant:
            report["admission"]["inherited_from"] = grant
        refused = None if grant else lock.acquire(cancelled)
        if refused == "cancelled":
            report.update(outcome="cancelled", exit_code=128 + cancelled[0])
            return report
        if refused:
            report.update(outcome="lock_busy", exit_code=75)
            return report
        report["lock_wait_seconds"] = round(time.monotonic() - lock_start, 3)
        if lock.waited:
            print(f"build-guard: admitted after {report['lock_wait_seconds']} s, {lock.priority} priority",
                  file=sys.stderr, flush=True)
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
        # After a preemption the log keeps the stopped run's output (`main`).
        with a.log.open("ab" if preempted else "wb") as output:
            # scripts/par.py sizes its worker pool by AIR2LEAN_JOBS and AIR2LEAN_MEM_MIB.
            # AIR2LEAN_GUARD_MODE tells a timing workload whether it runs alone (--exclusive).
            overrides = {"LEAN_NUM_THREADS": str(a.lean_threads), "ELAN_NO_OVERRIDE_NOTICE": "1",
                         "AIR2LEAN_JOBS": str(a.jobs), "AIR2LEAN_MEM_MIB": str(int(a.rss_mib)),
                         "AIR2LEAN_GUARD_MODE": "exclusive" if a.exclusive else "shared",
                         INHERIT: json.dumps(lock.grant(), sort_keys=True), **lake_cache_env()}
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
            sampler = Sampler(a.ps_timeout, a.sample_stale)
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
                    rows = sampler.sample()
                    next_sample = time.monotonic() + a.interval
                    if rows is not None:
                        owned = tree.owned(rows)
                        rss = sum(rows[pid]["rss_kib"] for pid in owned)
                        report["samples"] += 1
                        report["peak_sampled_rss_kib"] = max(report["peak_sampled_rss_kib"], rss)
                        if not reason and rss > a.rss_mib * 1024:
                            reason, code = "rss_limit", 125
                        if not reason and parallel_zig(rows, owned, names, a.jobs):
                            reason, code = "parallel_zig", 126
                    if not reason and lock.preempt():  # also when ps stalls under memory pressure
                        reason, code = "preempted", 75
                    report["failed_samples"] = sampler.failures
                status = peek_status(child)
                if reason:
                    cleanup_confirmed = stop_tree(child, tree, a.grace, a.ps_timeout)
                    break
                if status is not None:
                    if tree.owned(sampler.require()):
                        reason, code = "orphaned_children", 71
                        cleanup_confirmed = stop_tree(child, tree, a.grace, a.ps_timeout)
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
                if not cleanup_confirmed and not stop_tree(child, tree, a.grace, a.ps_timeout):
                    report.update(outcome="cleanup_failed", exit_code=70)
            except (OSError, RuntimeError, subprocess.SubprocessError) as error:
                # Keep the first error (e.g. the sampling abort): it is the root cause.
                report.update(outcome="cleanup_failed", exit_code=70)
                report.setdefault("error", str(error)[:256])
            finally:
                try:
                    report["child_status"] = child.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    report.update(outcome="cleanup_failed", exit_code=70)
                child.stdout.close()
        selector.close()
        if lock is not None:
            report["admission"].update(lock.evidence())
            if child is not None and "inherited_from" not in report["admission"]:
                try:
                    lock.record(report)
                except OSError as error:
                    print(f"build-guard: warning: run history not recorded: {error}", file=sys.stderr, flush=True)
            lock.release()
        if cancelled[0] and report["outcome"] == "preempted":  # a cancellation during the teardown
            report.update(outcome="cancelled", exit_code=128 + cancelled[0])
        for sig, handler in previous.items():
            signal.signal(sig, handler)
        report["log_truncated"] = report["output_bytes"] > a.log_bytes or report["drain_incomplete"]
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        atomic_report(a.report, report)
    return report


def main():
    a = parse_args(sys.argv[1:])
    report = run(a)
    if report["outcome"] == "preempted":
        # The backstop stopped it: run it again holding its declared slots (module docstring),
        # within what is left of --lock-wait and --timeout, so the caller's bounds still hold.
        print("build-guard: preempted (memory low, the youngest overcommitted workload); "
              "running it again at --rss-mib", file=sys.stderr, flush=True)
        a.no_overcommit = True
        a.lock_wait = max(0.0, a.lock_wait - report.get("lock_wait_seconds", 0))
        a.timeout = max(1.0, a.timeout - report.get("workload_seconds", 0))
        report = run(a, preempted={key: report.get(key) for key in (
            "started_utc", "lock_wait_seconds", "workload_seconds", "peak_sampled_rss_kib", "admission")})
    print(json.dumps({key: report[key] for key in ("outcome", "exit_code", "elapsed_seconds", "peak_sampled_rss_kib")}))
    return report["exit_code"]


if __name__ == "__main__":
    sys.exit(main())
