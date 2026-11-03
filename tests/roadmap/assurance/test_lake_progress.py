#!/usr/bin/env python3
"""A Lake run of the audit's generated workspaces fails closed when it hangs
(`assumptions.run_lake`): a process group with neither output nor CPU time for the idle limit is
stopped with a "lake hung" diagnostic, a run that keeps either going is left alone, and nothing of
the group outlives the run or a stopped auditor. Stand-in commands, no Lean."""
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

sys.dont_write_bytecode = True
SCRIPTS = Path(__file__).resolve().parents[3] / "scripts"
sys.path.insert(0, str(SCRIPTS))
import assumptions  # noqa: E402

PY = sys.executable
# A stand-in that starts a grandchild (`sleep 60`) in its group and records its pid in MARKER.
GRANDCHILD = ("import subprocess, sys; child = subprocess.Popen(['sleep', '60']); "
              "open(sys.argv[1], 'w').write(str(child.pid)); print('started', flush=True); {rest}")


def alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    # A zombie (exited, not yet reaped by its new parent) is gone for this purpose.
    state = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], capture_output=True, text=True).stdout
    return bool(state.strip()) and not state.strip().startswith("Z")


class RunLake(unittest.TestCase):
    def setUp(self):
        self.scratch = Path(tempfile.mkdtemp())
        self.marker = self.scratch / "pid"

    def run_lake(self, script: str, idle: float, *args):
        return assumptions.run_lake([PY, "-c", script, *args], Path.cwd(), dict(os.environ),
                                    poll=0.2, idle_seconds=idle)

    def assert_gone(self, pid: int):
        deadline = time.monotonic() + 10
        while alive(pid) and time.monotonic() < deadline:
            time.sleep(0.1)
        self.assertFalse(alive(pid), "a process of the Lake run's group outlived it")

    def test_result_like_subprocess_run(self):
        result = self.run_lake("import sys; print('out'); print('err', file=sys.stderr); sys.exit(3)", 5)
        self.assertEqual((result.returncode, result.stdout, result.stderr), (3, "out\n", "err\n"))

    def test_idle_group_is_stopped(self):
        start = time.monotonic()
        with self.assertRaisesRegex(RuntimeError, r"^lake hung: no output and under 1 s of CPU time .* for 0\.0[0-9]* min"):
            self.run_lake(GRANDCHILD.format(rest="child.wait()"), 2.0, str(self.marker))
        self.assertLess(time.monotonic() - start, 30)
        self.assert_gone(int(self.marker.read_text()))

    def test_leftovers_of_a_finished_run_are_stopped(self):
        result = self.run_lake(GRANDCHILD.format(rest="sys.exit(0)"), 30, str(self.marker))
        self.assertEqual(result.returncode, 0)
        self.assert_gone(int(self.marker.read_text()))

    def test_a_stopped_auditor_stops_its_lake_run(self):
        script = ("import os, sys; from pathlib import Path; sys.path.insert(0, sys.argv[1]); import assumptions; "
                  f"assumptions.run_lake([sys.executable, '-c', {GRANDCHILD.format(rest='child.wait()')!r}, sys.argv[2]], "
                  "Path.cwd(), dict(os.environ), poll=0.2, idle_seconds=60)")
        auditor = subprocess.Popen([PY, "-c", script, str(SCRIPTS), str(self.marker)])
        deadline = time.monotonic() + 10
        while not (self.marker.exists() and self.marker.read_text()) and time.monotonic() < deadline:
            time.sleep(0.05)
        auditor.send_signal(signal.SIGTERM)
        self.assertEqual(auditor.wait(timeout=30), 128 + signal.SIGTERM)
        self.assert_gone(int(self.marker.read_text()))

    def test_cpu_without_output_is_progress(self):
        # Linux `ps` shows CPU time in whole seconds: the limit stays well above that resolution.
        result = self.run_lake("import time\nend = time.time() + 8\nwhile time.time() < end: pass\nprint('done')", 4.0)
        self.assertEqual((result.returncode, result.stdout), (0, "done\n"))

    def test_output_without_cpu_is_progress(self):
        result = self.run_lake("import time\nfor i in range(8):\n    print(i, flush=True); time.sleep(0.5)", 2.0)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout.split(), [str(i) for i in range(8)])

    def test_an_unobservable_group_fails_closed(self):
        with mock.patch.object(assumptions, "group_cpu_seconds", return_value=None), \
                self.assertRaisesRegex(RuntimeError, r"^lake progress unobservable"):
            self.run_lake("import time; time.sleep(20)", 1.0)

    def test_limit_from_the_environment(self):
        for value, seconds in (("0", 0.0), ("2.5", 150.0), (None, 900.0)):
            with mock.patch.dict(os.environ, {assumptions.LAKE_IDLE_MINUTES: value} if value else {}):
                if value is None:
                    os.environ.pop(assumptions.LAKE_IDLE_MINUTES, None)
                self.assertEqual(assumptions.lake_idle_seconds(), seconds)
        for value in ("-1", "x", "inf", "nan"):
            with mock.patch.dict(os.environ, {assumptions.LAKE_IDLE_MINUTES: value}), \
                    self.assertRaisesRegex(ValueError, "AIR2LEAN_LAKE_IDLE_MINUTES"):
                assumptions.lake_idle_seconds()
        with mock.patch.dict(os.environ, {assumptions.LAKE_IDLE_MINUTES: "0"}):
            result = assumptions.run_lake([PY, "-c", "import time; time.sleep(1.5)"], Path.cwd(),
                                          dict(os.environ), poll=0.2)
        self.assertEqual(result.returncode, 0)

    def test_cpu_seconds(self):
        for text, seconds in (("0:00.03", 0.03), ("12:34.50", 754.5), ("00:01:02", 62),
                              ("1-02:03:04", 93784), ("1:02:03.00", 3723)):
            self.assertAlmostEqual(assumptions.cpu_seconds(text), seconds)

    def test_group_cpu_seconds(self):
        busy = subprocess.Popen([PY, "-c", "import time\nend = time.time() + 2.5\nwhile time.time() < end: pass"],
                                start_new_session=True)
        try:
            time.sleep(2)
            self.assertGreaterEqual(assumptions.group_cpu_seconds(busy.pid), 0.5)
        finally:
            busy.wait()


if __name__ == "__main__":
    unittest.main()
