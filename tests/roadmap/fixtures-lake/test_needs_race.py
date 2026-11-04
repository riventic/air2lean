"""scripts/assumptions.py `needs_first` with a real Lake (ledger `lake-needs-race`,
docs/upstream/lake-concurrent-needs.md).

A generated library `needs` a module's `:olean` and `:depTrace` (`module_needs`), as the
assurance-extraction driver and the kernel-replay receipts do. Lake 4.34 fetches each facet key of
`needs` in a pool task of its own, and the two tasks create the jobs of the module's import closure
twice. A `(sync := true)` continuation of one copy then blocks on the other copy, and the build can
deadlock at 0% CPU. With the needed oleans first on the command line (`needs_first`), Lake creates
every job once, on its build thread.

The control (the generated module alone on the command line) shows that Lake still duplicates
the jobs. When a toolchain update fixes that, the control fails: delete `needs_first` and close
the ledger row.
"""
import importlib.util
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("air2lean_assumptions", ROOT / "scripts/assumptions.py")
assumptions = importlib.util.module_from_spec(spec)
spec.loader.exec_module(assumptions)

CHAIN = 24  # modules below the needed one: enough for the two tasks to overlap
PANIC = "`Task.get` called from a `(sync := true)` task"


def lake(cwd: Path, args: list[str], timeout: float = 600) -> tuple[int | None, str]:
    """`lake ARGS` in `cwd` with one Lean thread and without the shared artifact cache: (exit
    status, output), status None when Lake is still running after `timeout` s (its process group
    is then stopped)."""
    env = {k: v for k, v in os.environ.items() if k != "AIR2LEAN_CAS_DIR" and not k.startswith("LAKE_")}
    env["LEAN_NUM_THREADS"] = "1"
    process = subprocess.Popen(["lake", *args], cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, start_new_session=True)
    try:
        output, _ = process.communicate(timeout=timeout)
        return process.returncode, output
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        output, _ = process.communicate()
        return None, output


def jobs(output: str) -> int:
    found = re.search(r"Build completed successfully \((\d+) jobs?\)", output)
    if found is None:
        raise AssertionError(f"no Lake job count in:\n{output[-4000:]}")
    return int(found.group(1))


class NeedsRace(unittest.TestCase):
    def test_needed_oleans_first_create_each_job_once(self):
        tmp = tempfile.TemporaryDirectory(prefix="air2lean-needs-race-test.")
        self.addCleanup(tmp.cleanup)
        dep, ws = Path(tmp.name) / "dep", Path(tmp.name) / "ws"
        for package in (dep, ws):
            (package / ("Dep" if package == dep else "W")).mkdir(parents=True)
            shutil.copy(ROOT / "lean-toolchain", package / "lean-toolchain")
        (dep / "lakefile.toml").write_text('name = "dep"\n[[lean_lib]]\nname = "Dep"\n')
        for i in range(CHAIN):
            imports = "".join(f"import Dep.M{j}\n" for j in (i - 1, i - 2) if j >= 0)
            (dep / f"Dep/M{i}.lean").write_text(f"{imports}def m{i} : Nat := {i}\n")
        (dep / "Dep/Top.lean").write_text(f"import Dep.M{CHAIN - 1}\nimport Dep.M{CHAIN - 2}\n")
        status, output = lake(dep, ["build", "Dep.Top"])
        self.assertEqual(status, 0, output)

        needs = assumptions.module_needs(["Dep.Top"], [(dep / ".lake/build/lib/lean").resolve()], [dep])
        self.assertEqual(needs, ["@dep/+Dep.Top:olean", "@dep/+Dep.Top:depTrace"])
        (ws / "lakefile.toml").write_text(
            'name = "ws"\n[[require]]\nname = "dep"\npath = "../dep"\n[[lean_lib]]\nname = "W"\n'
            'roots = ["W.R"]\nneeds = [' + ", ".join(f'"{key}"' for key in needs) + "]\n")
        (ws / "W/R.lean").write_text("def r : Nat := 0\n")

        targets = assumptions.needs_first(needs, ["W.R"])
        self.assertEqual(targets, ["@dep/+Dep.Top:olean", "W.R"])
        status, output = lake(ws, ["build", *targets])
        self.assertEqual(status, 0, output)
        status, output = lake(ws, ["build", *targets])  # up to date: every job replayed once
        self.assertEqual(status, 0, output)
        self.assertNotIn(PANIC, output)
        once = jobs(output)
        self.assertLessEqual(once, CHAIN + 8, output)  # a job per module, a few for the rest

        status, control = lake(ws, ["build", "W.R"], timeout=120)
        if status is not None:  # a deadlocked control shows the race as well
            self.assertEqual(status, 0, control)
            self.assertGreater(jobs(control), once + CHAIN // 2,
                               "Lake no longer creates the jobs of a library's needs twice: delete "
                               "assumptions.needs_first and close ledger row lake-needs-race")


if __name__ == "__main__":
    unittest.main()
