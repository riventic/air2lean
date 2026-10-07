#!/usr/bin/env python3
"""Bounded stage execution and atomic artifact publication for the shell workflows.

  safe-output.py run [--timeout SECONDS] [--grace SECONDS] -- COMMAND...
  safe-output.py publish (--overwrite | --no-clobber) SOURCE DESTINATION

`run` starts COMMAND in a new session/process group. A timeout or SIGINT/SIGTERM/SIGHUP
sends TERM to the whole group, then KILL after the grace period, and waits for the
leader before exiting. A leader that exits while group members remain has not finished
its stage: the members are killed and the stage fails. Exit status: the command's own
status, 124 on timeout, 125 for leftover descendants, 128+N after signal N.

`publish` copies SOURCE into a temporary file beside DESTINATION, fsyncs it, then
atomically renames it (--overwrite) or hard-links it (--no-clobber, refusing an existing
DESTINATION even when it appears concurrently) and fsyncs the directory. A failure or
interruption at any point leaves DESTINATION exactly as before; it never holds a prefix.
"""
import argparse
import os
from pathlib import Path
import signal
import stat
import subprocess
import sys
import tempfile
import time

TIMEOUT, DESCENDANTS = 124, 125
MAX_ARTIFACT = 1024 * 1024 * 1024


class Refused(Exception):
    pass


def _group_alive(pgid):
    try:
        os.killpg(pgid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def _signal_group(pgid, signum):
    try:
        os.killpg(pgid, signum)
    except (ProcessLookupError, PermissionError):
        pass


def _stop_group(child, grace):
    """TERM, then KILL, the whole group; return only once the leader and members are gone."""
    _signal_group(child.pid, signal.SIGTERM)
    deadline = time.monotonic() + grace
    while time.monotonic() < deadline:
        # Probe members only after reaping: an unreaped leader keeps killpg(0) succeeding.
        if child.poll() is not None and not _group_alive(child.pid):
            return
        time.sleep(0.02)
    # One KILL, sent while the last probe saw members (or the unreaped leader pins the PGID).
    # Afterwards only probe: once the group empties its PGID may be reused by an unrelated group.
    _signal_group(child.pid, signal.SIGKILL)
    child.wait()
    deadline = time.monotonic() + max(grace, 1.0)
    while _group_alive(child.pid) and time.monotonic() < deadline:
        time.sleep(0.02)


def run(argv, timeout, grace):
    received = []

    def handler(signum, frame):
        received.append(signum)
    for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        signal.signal(signum, handler)
    child = subprocess.Popen(argv, start_new_session=True)
    deadline = None if timeout <= 0 else time.monotonic() + timeout
    failure = None
    try:
        while child.poll() is None:
            if received:
                failure = 128 + received[0]
                break
            if deadline is not None and time.monotonic() >= deadline:
                failure = TIMEOUT
                break
            time.sleep(0.02)
        if failure is None:
            if not _group_alive(child.pid):
                status = child.returncode
                return status if status >= 0 else 128 - status
            failure = DESCENDANTS
    except BaseException:
        _stop_group(child, grace)
        raise
    _stop_group(child, grace)
    if failure == TIMEOUT:
        print(f'error: stage exceeded its {timeout:g}s timeout; its process group was stopped', file=sys.stderr)
    elif failure == DESCENDANTS:
        print('error: stage exited with live child processes; they were stopped', file=sys.stderr)
    else:
        print(f'error: stage interrupted by signal {failure - 128}; its process group was stopped', file=sys.stderr)
    return failure


def _destination(path):
    path = Path(os.path.abspath(path))
    if not path.parent.is_dir():
        raise Refused(f'output directory does not exist: {path.parent}')
    if path.is_symlink() or (path.exists() and not path.is_file()):
        raise Refused(f'output must be a regular file path (no symlinks or directories): {path}')
    return path


def publish(source, destination, overwrite):
    destination = _destination(destination)
    fd = os.open(source, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
    with os.fdopen(fd, 'rb') as stream:
        info = os.fstat(stream.fileno())
        if not stat.S_ISREG(info.st_mode):
            raise Refused(f'staged artifact is not a regular file: {source}')
        if info.st_size > MAX_ARTIFACT:
            raise Refused(f'staged artifact exceeds {MAX_ARTIFACT} bytes: {source}')
        if not overwrite and destination.exists():
            raise Refused(f'refusing to overwrite existing output (--no-clobber): {destination}')
        try:
            mode = stat.S_IMODE(destination.stat().st_mode)
        except FileNotFoundError:
            umask = os.umask(0)
            os.umask(umask)
            mode = 0o666 & ~umask
        handle = tempfile.NamedTemporaryFile(dir=destination.parent, prefix='.' + destination.name + '.',
                                             suffix='.partial', delete=False)
        temporary = Path(handle.name)
        try:
            with handle:
                while chunk := stream.read(1024 * 1024):
                    handle.write(chunk)
                handle.flush()
                os.fchmod(handle.fileno(), mode)
                os.fsync(handle.fileno())
            if overwrite:
                os.replace(temporary, destination)
            else:
                try:
                    os.link(temporary, destination)  # Atomic no-clobber, including concurrent writers.
                except FileExistsError:
                    raise Refused(f'refusing to overwrite existing output (--no-clobber): {destination}')
        finally:
            temporary.unlink(missing_ok=True)
    directory = os.open(destination.parent, os.O_RDONLY)
    try:
        os.fsync(directory)
    except OSError:
        pass  # Some filesystems reject directory fsync; the rename itself is still atomic.
    finally:
        os.close(directory)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest='command', required=True)
    runner = commands.add_parser('run')
    runner.add_argument('--timeout', type=float, default=0, help='seconds; 0 disables')
    runner.add_argument('--grace', type=float, default=2)
    runner.add_argument('argv', nargs=argparse.REMAINDER)
    publisher = commands.add_parser('publish')
    policy = publisher.add_mutually_exclusive_group(required=True)
    policy.add_argument('--overwrite', action='store_true')
    policy.add_argument('--no-clobber', action='store_true')
    publisher.add_argument('source')
    publisher.add_argument('destination')
    args = parser.parse_args(argv)
    if args.command == 'run':
        command = args.argv[1:] if args.argv[:1] == ['--'] else args.argv
        if not command or args.timeout < 0 or args.grace < 0:
            parser.error('run needs -- COMMAND and nonnegative --timeout/--grace')
        return run(command, args.timeout, args.grace)

    def interrupted(signum, frame):
        raise KeyboardInterrupt  # Unwind through publish() so the temporary file is removed.
    for signum in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(signum, interrupted)
    try:
        publish(args.source, args.destination, args.overwrite)
    except (OSError, Refused) as error:
        print(f'error: {error}; output was not changed', file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print('error: publication interrupted; output was not changed', file=sys.stderr)
        return 130
    return 0


if __name__ == '__main__':
    sys.exit(main())
