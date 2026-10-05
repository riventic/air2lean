#!/usr/bin/env python3
"""Compiler-free, bounded timeout-cleanup regressions."""
import importlib.util
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("weak_cas_qualify", Path(__file__).with_name("qualify.py"))
qualify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(qualify)


class CleanupTests(unittest.TestCase):
    def test_signals_before_reap_even_when_term_exits_leader(self):
        events = []

        class Leader:
            pid = 123

            def wait(self, timeout):
                events.append(("reap", timeout))
                return -signal.SIGTERM

        with patch.object(qualify.os, "killpg", side_effect=lambda pid, sig: events.append(sig)), \
                patch.object(qualify.time, "sleep", side_effect=lambda seconds: events.append("grace")):
            result = qualify.cleanup_process_group(Leader(), grace_seconds=0.01, reap_seconds=0.2)
        self.assertEqual(events, [signal.SIGTERM, "grace", signal.SIGKILL, ("reap", 0.2)])
        self.assertEqual(result["status"], "completed")

    def test_signal_and_bounded_reap_failures_recorded(self):
        class Leader:
            pid = 123

            def wait(self, timeout):
                self.timeout = timeout
                raise subprocess.TimeoutExpired("fixture", timeout)

        leader = Leader()
        with patch.object(qualify.os, "killpg", side_effect=PermissionError("fixture denied")), \
                patch.object(qualify.time, "sleep"):
            result = qualify.cleanup_process_group(leader, reap_seconds=0.2)
        self.assertEqual(leader.timeout, 0.2)
        self.assertEqual([x["signal"] for x in result["attempts"]], ["SIGTERM", "SIGKILL"])
        self.assertEqual(len(result["errors"]), 3)
        self.assertEqual(result["status"], "failed")

    def test_early_leader_exit_still_kills_term_ignoring_child(self):
        # Both processes expire independently if the tested cleanup is broken. At most
        # one descendant is created. Linux caps address space at 32 MiB; macOS
        # rejects that rlimit, so check the same 32 MiB resident-memory budget.
        program = """
import os, signal, sys
signal.alarm(4)
pid = os.fork()
if pid == 0:
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    signal.alarm(4)
    with open(sys.argv[1] + '.tmp', 'w') as stream:
        stream.write(str(os.getpid()))
    os.rename(sys.argv[1] + '.tmp', sys.argv[1])
while True:
    signal.pause()
"""
        def limit_memory():
            resource.setrlimit(resource.RLIMIT_AS, (32 * 1024 * 1024, 32 * 1024 * 1024))

        with tempfile.TemporaryDirectory(prefix="weak-cas-cleanup-") as directory:
            ready = Path(directory) / "child.pid"
            proc = subprocess.Popen([sys.executable, "-c", program, ready],
                                    start_new_session=True,
                                    preexec_fn=limit_memory if sys.platform.startswith("linux") else None,
                                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            try:
                deadline = time.monotonic() + 1
                while not ready.exists() and time.monotonic() < deadline:
                    time.sleep(0.01)
                self.assertTrue(ready.exists(), "finite child did not become ready")
                child = int(ready.read_text())
                memory = subprocess.run(["ps", "-o", "rss=", "-p", f"{proc.pid},{child}"],
                                        capture_output=True, text=True, timeout=0.5, check=True)
                resident = [int(value) for value in memory.stdout.split()]
                self.assertEqual(len(resident), 2)
                self.assertTrue(all(value <= 32 * 1024 for value in resident), resident)
                with self.assertRaises(subprocess.TimeoutExpired):
                    proc.wait(timeout=0.05)
                result = qualify.cleanup_process_group(proc, grace_seconds=0.1, reap_seconds=1)
                self.assertEqual(result["status"], "completed", result)
                self.assertEqual(result["leader_exit_code"], -signal.SIGTERM)
                # A killed orphan may remain as a zombie until the host's init reaps it.
                deadline = time.monotonic() + 1
                while True:
                    state = subprocess.run(["ps", "-o", "stat=", "-p", str(child)],
                                           capture_output=True, text=True, timeout=0.5).stdout.strip()
                    if not state or state.startswith("Z") or time.monotonic() >= deadline:
                        break
                    time.sleep(0.01)
                self.assertTrue(not state or state.startswith("Z"), state)
            finally:
                # Keep the PID anchor for independent cleanup of a failing test. Once
                # reaped, the child's own alarm remains the independent fallback.
                if proc.returncode is None:
                    try:
                        os.killpg(proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    proc.wait(timeout=1)


if __name__ == "__main__":
    unittest.main()
