#!/usr/bin/env python3
"""Run independent jobs on a bounded number of workers; print their output in job order.

    par.py [--jobs N] [--mem-mib M] [--log-dir DIR] -- COMMAND... ::: ITEM...
    par.py --print-jobs [--jobs N] [--mem-mib M] [--count K]

One job per ITEM: COMMAND with every `{}` in its arguments replaced by the item (the item is
appended when no argument contains `{}`). For a list of shell commands: `-- bash -c {} ::: ...`.

Workers (`workers`): --jobs, else $AIR2LEAN_JOBS, else the CPU count (the process's CPU affinity
and a Linux cgroup CPU quota, so `docker --cpus 4` counts 4). With --mem-mib (the peak memory of
one job), at most budget/M jobs run at once; the budget is $AIR2LEAN_MEM_MIB, else 80% of the
physical memory or of a lower cgroup memory limit. scripts/build-guard.py exports both variables
(its --jobs, default 1, and its --rss-mib), so a guarded run stays within its lane's budget.
Each job gets AIR2LEAN_JOBS=1: a job does not start a parallel run of its own.

Output: each job's stdout and stderr are captured separately and written to this process's
stdout and stderr in job order, each chunk to the stream it came from and in the order it
arrived. The first unfinished job streams live, so with one worker the output is exactly that of
running the jobs one after another. --log-dir DIR also writes each job's combined output to
DIR/<item>.log.

Exit status: 0 when every job succeeded; otherwise the status of the first failed job in job
order (a job killed by a signal: 128 + signal), after a list of every failed job on stderr. Every
job runs to completion; a failure does not cancel the others. SIGINT, SIGTERM and SIGHUP stop
every running job's process group (TERM, then KILL after 10 seconds) and exit 128 + signal.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
import os
from pathlib import Path
import re
import selectors
import signal
import subprocess
import sys
import tempfile
import time

MEM_FRACTION = 0.8
GRACE_SECONDS = 10
CGROUP = Path('/sys/fs/cgroup')


def _read(path: str) -> str | None:
    try:
        return (CGROUP / path).read_text()
    except OSError:
        return None


def cpu_count() -> int:
    """CPUs this process may use: affinity, then a Linux cgroup (v2 or v1) CPU quota."""
    try:
        count = len(os.sched_getaffinity(0))
    except AttributeError:  # macOS
        count = os.cpu_count() or 1
    quota = None
    text = _read('cpu.max')
    if text and text.split()[0] != 'max':
        limit, period = text.split()[:2]
        quota = int(limit) / int(period)
    else:
        limit, period = _read('cpu/cpu.cfs_quota_us'), _read('cpu/cpu.cfs_period_us')
        if limit and period and int(limit) > 0:
            quota = int(limit) / int(period)
    if quota:
        count = min(count, max(1, int(quota + 0.5)))
    return max(1, count)


def memory_budget_mib() -> int:
    """$AIR2LEAN_MEM_MIB, else 80% of the physical memory or of a lower cgroup limit."""
    if os.environ.get('AIR2LEAN_MEM_MIB'):
        return positive_int(os.environ['AIR2LEAN_MEM_MIB'], 'AIR2LEAN_MEM_MIB')
    total = os.sysconf('SC_PAGE_SIZE') * os.sysconf('SC_PHYS_PAGES')
    for path in ('memory.max', 'memory/memory.limit_in_bytes'):
        text = _read(path)
        if text and text.strip().isdigit():
            total = min(total, int(text))
    return max(1, int(total * MEM_FRACTION) >> 20)


def positive_int(text: str, what: str) -> int:
    if not re.fullmatch(r'[1-9][0-9]*', text.strip()):
        raise SystemExit(f'par: {what} must be a positive integer, not {text!r}')
    return int(text)


def workers(jobs: int | None = None, mem_mib: int | None = None, count: int | None = None) -> int:
    """The number of jobs to run at once."""
    if jobs is None:
        env = os.environ.get('AIR2LEAN_JOBS')
        jobs = positive_int(env, 'AIR2LEAN_JOBS') if env else cpu_count()
    if mem_mib:
        jobs = min(jobs, max(1, memory_budget_mib() // mem_mib))
    if count is not None:
        jobs = min(jobs, max(1, count))
    return max(1, jobs)


@dataclass
class Job:
    name: str
    argv: list[str]
    cwd: str | None = None
    env: dict | None = None


@dataclass
class _Running:
    job: Job
    process: subprocess.Popen
    spool: object  # binary temporary file: the captured bytes, in arrival order
    chunks: list = field(default_factory=list)  # (stream number 1|2, byte count)
    open_streams: int = 2
    status: int | None = None


class Interrupted(Exception):
    def __init__(self, sig: int):
        super().__init__(f'interrupted by signal {sig}')
        self.status = 128 + sig


def _status(code: int) -> int:
    return code if code >= 0 else 128 - code


def run(jobs: list[Job], max_workers: int, out=None, err=None, log_dir: Path | None = None) -> list[int]:
    """Run `jobs`, at most `max_workers` at once; return their exit statuses in job order."""
    out = out or sys.stdout.buffer
    err = err or sys.stderr.buffer
    streams = {1: out, 2: err}
    statuses: list[int | None] = [None] * len(jobs)
    running: dict[int, _Running] = {}
    finished: dict[int, _Running] = {}
    selector = selectors.DefaultSelector()
    head = 0  # the first job whose output is not yet fully written
    started = 0
    received = []

    def on_signal(sig, _frame):
        received.append(sig)

    previous = {sig: signal.signal(sig, on_signal) for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)}

    def write(stream: int, data: bytes):
        streams[stream].write(data)
        streams[stream].flush()

    def replay(entry: _Running):
        """Write a finished or head job's buffered chunks."""
        entry.spool.seek(0)
        for stream, size in entry.chunks:
            write(stream, entry.spool.read(size))
        entry.chunks.clear()
        entry.spool.seek(0)
        entry.spool.truncate()

    def start(index: int):
        job = jobs[index]
        env = dict(job.env if job.env is not None else os.environ, AIR2LEAN_JOBS='1')
        try:
            process = subprocess.Popen(job.argv, cwd=job.cwd, env=env, stdin=subprocess.DEVNULL,
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        except OSError as error:
            message = f'par: {job.name}: cannot start {job.argv[0]}: {error}\n'.encode()
            entry = _Running(job, None, tempfile.TemporaryFile(), open_streams=0, status=127)
            entry.spool.write(message)
            entry.chunks.append((2, len(message)))
            finished[index] = entry
            return
        entry = _Running(job, process, tempfile.TemporaryFile())
        running[index] = entry
        for number, pipe in ((1, process.stdout), (2, process.stderr)):
            os.set_blocking(pipe.fileno(), False)
            selector.register(pipe, selectors.EVENT_READ, (index, number))

    def stop_all():
        for sig in (signal.SIGTERM, signal.SIGKILL):
            for entry in running.values():
                try:
                    os.killpg(entry.process.pid, sig)
                except (ProcessLookupError, PermissionError):
                    pass
            deadline = time.monotonic() + GRACE_SECONDS
            while time.monotonic() < deadline and any(e.process.poll() is None for e in running.values()):
                time.sleep(0.05)
        for entry in running.values():
            entry.process.wait()

    def advance():
        """Write every finished job at the head, then the new head's buffered output."""
        nonlocal head
        while head < len(jobs):
            if head in finished:
                entry = finished.pop(head)
                replay(entry)
                entry.spool.close()
                statuses[head] = entry.status
                head += 1
                continue
            if head in running:
                replay(running[head])
            break

    try:
        while head < len(jobs):
            if received:
                stop_all()
                # Keep what the stopped jobs wrote, in job order, for the diagnosis.
                for index in sorted(set(finished) | set(running)):
                    entry = finished.get(index) or running[index]
                    replay(entry)
                raise Interrupted(received[0])
            while started < len(jobs) and len(running) < max_workers:
                start(started)
                started += 1
            advance()
            if not running:
                continue
            for key, _events in selector.select(timeout=0.1):
                index, number = key.data
                entry = running[index]
                try:
                    data = os.read(key.fd, 65536)
                except BlockingIOError:
                    continue
                if not data:
                    selector.unregister(key.fileobj)
                    key.fileobj.close()
                    entry.open_streams -= 1
                    continue
                if index == head:
                    write(number, data)
                else:
                    entry.spool.write(data)
                    entry.chunks.append((number, len(data)))
                if log_dir is not None:
                    _log(log_dir, entry.job.name, data)
            for index in [i for i, e in running.items() if e.open_streams == 0]:
                entry = running.pop(index)
                entry.status = _status(entry.process.wait())
                finished[index] = entry
        return statuses
    finally:
        selector.close()
        for sig, handler in previous.items():
            signal.signal(sig, handler)


def _log(log_dir: Path, name: str, data: bytes):
    with open(log_dir / (name + '.log'), 'ab') as handle:
        handle.write(data)


def safe_name(item: str) -> str:
    return re.sub(r'[^A-Za-z0-9._-]', '_', item)[:128] or '_'


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    command: list[str] = []
    if '--' in argv:
        split = argv.index('--')
        argv, command = argv[:split], argv[split + 1:]
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0],
                                     usage='%(prog)s [options] -- COMMAND... ::: ITEM...')
    parser.add_argument('--jobs', type=lambda v: positive_int(v, '--jobs'))
    parser.add_argument('--mem-mib', type=lambda v: positive_int(v, '--mem-mib'),
                        help='peak memory of one job (MiB): bounds the workers by the memory budget')
    parser.add_argument('--log-dir', type=Path, help="also write each job's output to DIR/<item>.log")
    parser.add_argument('--print-jobs', action='store_true', help='print the number of workers and exit')
    parser.add_argument('--count', type=int, help='with --print-jobs: the number of jobs')
    args = parser.parse_args(argv)
    if args.print_jobs:
        print(workers(args.jobs, args.mem_mib, args.count))
        return 0
    if ':::' not in command or command.index(':::') == 0:
        parser.error('expected -- COMMAND... ::: ITEM...')
    split = command.index(':::')
    template, items = command[:split], command[split + 1:]
    if not any('{}' in arg for arg in template):
        template = template + ['{}']
    jobs = [Job(item, [arg.replace('{}', item) for arg in template]) for item in items]
    if not jobs:
        return 0
    names = [safe_name(job.name) for job in jobs]
    if len(set(names)) != len(names):
        parser.error('items must be distinct')
    if args.log_dir is not None:
        args.log_dir.mkdir(parents=True, exist_ok=True)
        for name in names:
            (args.log_dir / (name + '.log')).write_bytes(b'')
        for job, name in zip(jobs, names):
            job.name = name
    try:
        statuses = run(jobs, workers(args.jobs, args.mem_mib, len(jobs)), log_dir=args.log_dir)
    except Interrupted as stop:
        return stop.status
    failed = [(job, status) for job, status in zip(jobs, statuses) if status]
    if failed:
        sys.stderr.write(f'par: {len(failed)} of {len(jobs)} jobs failed: '
                         + ', '.join(f'{job.name} (exit {status})' for job, status in failed) + '\n')
        return failed[0][1]
    return 0


if __name__ == '__main__':
    sys.exit(main())
