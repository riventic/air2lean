#!/usr/bin/env python3
"""ROOT-only serial qualification of the opt-in timed scheduler; never probe versions."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[3]
FILES = (
    "ZigLean/Time.lean", "ZigLean/Conc/TimedSched.lean",
    "tests/roadmap/deadline-futex/Kernel.lean",
    "tests/roadmap/deadline-futex/Runtime.lean",
    "tests/roadmap/deadline-futex/root-runtime.py",
    "tests/roadmap/deadline-futex/test_runtime_recipe.py",
    "docs/deadline-runtime.md", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
    "ZigLean/Basic.lean", "ZigLean/Mem/Basic.lean", "ZigLean/Mem/Thread.lean",
)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def commands(root):
    return [
        ("build-time", ["lake", "build", "ZigLean.Time"]),
        ("build-timed-scheduler", ["lake", "build", "ZigLean.Conc.TimedSched"]),
        ("kernel", ["lake", "env", "lean", "-R", str(root),
                    str(root / "tests/roadmap/deadline-futex/Kernel.lean")]),
        ("runtime", ["lake", "env", "lean", "-R", str(root), "--run",
                     str(root / "tests/roadmap/deadline-futex/Runtime.lean")]),
    ]


def qualification_files(root):
    """Retain the transitive local Lean imports; toolchain imports are ROOT's premise."""
    names = set(FILES)
    pending = [name for name in FILES if name.endswith(".lean")]
    while pending:
        name = pending.pop()
        for line in (root / name).read_text().splitlines():
            match = re.fullmatch(r"\s*import\s+([\w. ]+)\s*", line)
            if not match:
                continue
            for module in match.group(1).split():
                path = module.replace(".", "/") + ".lean"
                if module.startswith("ZigLean") and path not in names:
                    if not (root / path).is_file():
                        raise RuntimeError("missing local imported source: " + path)
                    names.add(path)
                    pending.append(path)
    return sorted(names)


class RecipeInterrupted(BaseException):
    """Raised synchronously after an INT/TERM request is safely recorded."""
    def __init__(self, signum):
        self.signum = signum
        super().__init__("signal " + str(signum))


def install_handlers(handler):
    return {sig: signal.signal(sig, handler) for sig in (signal.SIGINT, signal.SIGTERM)}


def restore_handlers(handlers):
    for sig, handler in handlers.items():
        signal.signal(sig, handler)


def cleanup_process_group(process, grace_seconds=2, reap_seconds=2):
    """Keep the leader unreaped until TERM and KILL have both reached the group.

    Adapted from tests/roadmap/weak-cas/qualify.py; no unrelated harness import.
    """
    errors = []
    interrupted = None
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(process.pid, sig)
        except ProcessLookupError:
            pass
        except OSError as error:
            errors.append(str(error))
        if sig == signal.SIGTERM:
            try:
                time.sleep(grace_seconds)
            except BaseException as error:
                interrupted = error
    try:
        code = process.wait(timeout=reap_seconds)
    except (subprocess.TimeoutExpired, OSError) as error:
        errors.append(str(error))
        code = None
    if interrupted is not None:
        interrupted.cleanup_errors = errors
        raise interrupted
    return code, errors


class CommandStartError(RuntimeError):
    pass


def require_supervision():
    if not callable(getattr(os, "waitid", None)) or not all(
            hasattr(os, name) for name in ("P_PID", "WEXITED", "WNOWAIT", "WNOHANG")):
        raise RuntimeError("execution requires POSIX non-reaping waitid; use ROOT's Linux container")


def exited_without_reaping(process):
    info = os.waitid(os.P_PID, process.pid, os.WEXITED | os.WNOWAIT | os.WNOHANG)
    return info is not None and info.si_pid != 0


def run_command(argv, cwd, log, timeout, interrupts=None):
    """CLI signal handlers record requests instead of raising during creation/cleanup.

    WNOWAIT preserves the process-group anchor until every
    cleanup signal has been sent, including after a normal leader exit. No Popen.wait polling or KeyboardInterrupt grace reap.
    """
    require_supervision()
    interrupts = [] if interrupts is None else interrupts
    if interrupts:
        raise RecipeInterrupted(interrupts[0])
    # Validate deadline arithmetic before creating a process; even huge positive ints
    # must not strand a spawned group on float-conversion overflow.
    deadline = time.monotonic() + timeout
    with log.open("w") as output:
        try:
            process = subprocess.Popen(argv, cwd=cwd, stdout=output, stderr=subprocess.STDOUT,
                                       start_new_session=True)
        except OSError as error:
            raise CommandStartError(str(error)) from error
        cleanup_done = False
        try:
            while True:
                if interrupts:
                    raise RecipeInterrupted(interrupts[0])
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    code, errors = cleanup_process_group(process)
                    cleanup_done = True
                    if interrupts:
                        error = RecipeInterrupted(interrupts[0])
                        error.cleanup_errors = errors
                        raise error
                    return code, True, errors
                if exited_without_reaping(process):
                    if interrupts:
                        raise RecipeInterrupted(interrupts[0])
                    # The leader has exited but remains the group anchor. Clear any
                    # remaining workers before reaping; normal exit needs no TERM grace.
                    code, errors = cleanup_process_group(process, grace_seconds=0)
                    cleanup_done = True
                    if interrupts:
                        error = RecipeInterrupted(interrupts[0])
                        error.cleanup_errors = errors
                        raise error
                    return code, False, errors
                time.sleep(min(0.05, remaining))
        except BaseException as error:
            # Every reap follows group cleanup. Avoid repeating cleanup or signaling
            # an already reaped numeric PID after an unrelated Python error.
            if not cleanup_done and process.returncode is None:
                _, errors = cleanup_process_group(process)
                error.cleanup_errors = errors
            raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute", action="store_true", help="ROOT's existing serialized lane only")
    parser.add_argument("--artifacts", type=Path, default=Path(tempfile.gettempdir()))
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if args.execute and os.environ.get("AIR2LEAN_ROOT_LANE") != "1":
        parser.error("execution requires AIR2LEAN_ROOT_LANE=1 from ROOT's owned lane")
    report = {
        "schema": 1, "status": "prepared", "source_root": str(ROOT),
        "scope": "opt-in single-caller timed scheduler foundation",
        "source_adapter": "unsupported; no translated API qualification",
        "native": "not run", "os_correspondence": "not claimed",
        "execution_host": "POSIX non-reaping waitid required; ROOT Linux container",
        "cancellation": "explicit no-cancellation environment only",
        "fairness": "not assumed", "termination": "no-result snapshots permitted",
        "source_isolation": "ROOT must execute from externally frozen inputs; final hashes detect persistent drift only",
        "source_hashes": {name: digest(ROOT / name) for name in qualification_files(ROOT)},
        "steps": [],
    }
    if not args.execute:
        report["commands"] = commands(ROOT)
        print(json.dumps(report, indent=2))
        return 0
    args.artifacts.mkdir(parents=True, exist_ok=True)
    artifacts = Path(tempfile.mkdtemp(prefix="deadline-runtime-", dir=args.artifacts))
    report["artifacts"] = str(artifacts)
    interrupts = []
    handlers = install_handlers(lambda sig, _frame: interrupts.append(sig))

    def save():
        (artifacts / "report.json").write_text(json.dumps(report, indent=2) + "\n")

    try:
        report["status"] = "running"
        save()
        for name, expected in report["source_hashes"].items():
            destination = artifacts / "sources" / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, destination)
            if digest(destination) != expected:
                raise RuntimeError("retained input differs from initial hash: " + name)
        for name, argv in commands(ROOT):
            if interrupts:
                raise RecipeInterrupted(interrupts[0])
            log = artifacts / (name + ".log")
            entry = {"name": name, "argv": argv, "log": str(log), "status": "running"}
            report["steps"].append(entry)
            save()
            start = time.monotonic()
            try:
                code, timed_out, cleanup_errors = run_command(argv, ROOT, log, args.timeout, interrupts)
            except BaseException as error:
                entry.update(elapsed_seconds=time.monotonic() - start,
                             status="interrupted" if isinstance(error, (KeyboardInterrupt, RecipeInterrupted))
                             else "failed_to_start" if isinstance(error, CommandStartError) else "failed",
                             error=type(error).__name__ + ": " + str(error),
                             cleanup_errors=getattr(error, "cleanup_errors", []))
                save()
                raise
            entry.update(exit_code=code, elapsed_seconds=time.monotonic() - start,
                         cleanup_errors=cleanup_errors,
                         status="timeout" if timed_out else "failed_cleanup" if cleanup_errors
                         else "passed" if code == 0 else "failed")
            save()
            if timed_out or code != 0 or cleanup_errors:
                raise RuntimeError(f"{name}: {entry['status']}; retained {log}")
        # Detect persistent source drift. ROOT's external freeze excludes transient edits.
        changed = [name for name, value in report["source_hashes"].items()
                   if digest(ROOT / name) != value]
        if changed:
            raise RuntimeError("source changed during qualification: " + ", ".join(changed))
        if interrupts:
            raise RecipeInterrupted(interrupts[0])
        report["status"] = "passed"
    except (KeyboardInterrupt, RecipeInterrupted) as error:
        report.update(status="interrupted", error=type(error).__name__ + ": " + str(error))
        report["interrupt_exit_code"] = 128 + error.signum if isinstance(error, RecipeInterrupted) else 130
        save()
    except Exception as error:
        report.update(status="failed", error=str(error))
    finally:
        restore_handlers(handlers)
        report["artifact_hashes"] = {
            str(path.relative_to(artifacts)): digest(path)
            for path in sorted(artifacts.rglob("*")) if path.is_file() and path.name != "report.json"
        }
        save()
        print(f"Deadline runtime {report['status']}: {artifacts / 'report.json'}")
    return 0 if report["status"] == "passed" else report.get("interrupt_exit_code", 1)


if __name__ == "__main__":
    raise SystemExit(main())
