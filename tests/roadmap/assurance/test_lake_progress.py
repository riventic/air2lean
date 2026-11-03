#!/usr/bin/env python3
"""The generated workspaces' `lake build` fails closed when it hangs (`assumptions.lake_build`): a
process tree with neither output nor CPU time for the idle limit is stopped with a "lake hung"
diagnostic, and a build that keeps either going is left alone. Stand-in commands, no Lean."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "scripts"))
import assumptions  # noqa: E402

PY = sys.executable


def alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    return True


class LakeBuild(unittest.TestCase):
    def build(self, script: str, idle: float, env=None):
        return assumptions.lake_build([PY, "-c", script], Path.cwd(), env or dict(os.environ),
                                      poll=0.2, idle_seconds=idle)

    def test_result_like_subprocess_run(self):
        result = self.build("import sys; print('out'); print('err', file=sys.stderr); sys.exit(3)", 5)
        self.assertEqual((result.returncode, result.stdout, result.stderr), (3, "out\n", "err\n"))

    def test_idle_tree_is_stopped(self):
        with tempfile.TemporaryDirectory() as scratch:
            marker = Path(scratch) / "pid"
            # The idle process is a grandchild: the whole tree goes, not just the direct child.
            script = ("import subprocess, sys, time; print('started', flush=True); "
                      f"child = subprocess.Popen(['sleep', '60']); open({str(marker)!r}, 'w').write(str(child.pid)); "
                      "child.wait()")
            start = time.monotonic()
            with self.assertRaisesRegex(RuntimeError, r"^lake hung: no CPU time and no output .* for 0\.0[0-9]* min"):
                self.build(script, 1.0)
            self.assertLess(time.monotonic() - start, 30)
            grandchild = int(marker.read_text())
            for _ in range(50):
                if not alive(grandchild):
                    break
                time.sleep(0.1)
            self.assertFalse(alive(grandchild), "the hung build's process tree must be stopped")

    def test_cpu_without_output_is_progress(self):
        # Linux `ps` shows CPU time in whole seconds: the limit stays well above that resolution.
        result = self.build("import time\nend = time.time() + 6\nwhile time.time() < end: pass\nprint('done')", 2.5)
        self.assertEqual((result.returncode, result.stdout), (0, "done\n"))

    def test_output_without_cpu_is_progress(self):
        result = self.build("import time\nfor i in range(6):\n    print(i, flush=True); time.sleep(0.5)", 1.0)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout.split(), [str(i) for i in range(6)])

    def test_limit_from_environment_and_zero_disables(self):
        os.environ[assumptions.LAKE_IDLE_MINUTES] = "0"
        try:
            result = assumptions.lake_build([PY, "-c", "import time; time.sleep(1.5)"], Path.cwd(),
                                            dict(os.environ), poll=0.2)
        finally:
            del os.environ[assumptions.LAKE_IDLE_MINUTES]
        self.assertEqual(result.returncode, 0)

    def test_cpu_seconds(self):
        for text, seconds in (("0:00.03", 0.03), ("12:34.50", 754.5), ("00:01:02", 62),
                              ("1-02:03:04", 93784), ("1:02:03.00", 3723)):
            self.assertAlmostEqual(assumptions.cpu_seconds(text), seconds)

    def test_tree_cpu_seconds(self):
        busy = subprocess.Popen([PY, "-c", "import time\nend = time.time() + 2\nwhile time.time() < end: pass"])
        try:
            time.sleep(1.5)
            self.assertGreaterEqual(assumptions.tree_cpu_seconds(busy.pid), 0.5)
        finally:
            busy.wait()


if __name__ == "__main__":
    unittest.main()
