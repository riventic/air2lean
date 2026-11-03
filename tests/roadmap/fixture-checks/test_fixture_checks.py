#!/usr/bin/env python3
"""scripts/fixture-checks.py: a unit runs unless a pass of exactly its inputs is recorded.

The regression for the false green of a reused pass (docs/ci.md#full-build): a unit whose input
is reached by a path built in code (tests/roadmap/callbacks/mutants.py reaches
`ROADMAP / "asm-effects"`) kept the key of its last pass after that input changed, and the stale
pass was reused while the check failed. A key now covers everything a unit can read
(`run_inputs`: every file of the checkout, the Lake build outputs, the toolchains, the
environment), not the files its text names. Here a synthetic unit reads a file whose path no
text of the unit names; it stands for a file of the checkout (`run_inputs` is replaced by one
that reads it), and `RunInputs` checks the real `run_inputs` on a scratch checkout.
Offline: no toolchain, no Lean.
"""
import contextlib
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("air2lean_fixture_checks", ROOT / "scripts/fixture-checks.py")
fc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fc)


def no_toolchain(kind, version):
    raise fc.Unavailable("no %s Zig %s in this test" % (kind, version))


class Passes(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="air2lean fixture-checks ")
        self.addCleanup(temp.cleanup)
        self.temp = Path(temp.name)
        self.cas = self.temp / "cas"
        self.cas.mkdir()
        self.hidden = self.temp / "hidden"
        self.hidden.mkdir()
        self.runs = self.temp / "runs"
        # The path is assembled at run time: no text of the unit spells out "hidden/input".
        self.unit = {"name": "synthetic: hidden input", "job": "synthetic", "rows": ["synthetic"],
                     "zig": "0.0.0", "checks": ["tests/roadmap/synthetic/check.sh"],
                     "run": 'echo run >> "$RUNS"\nf="$HIDDEN_DIR"/in""put\necho "read $f"\n[ "$(cat "$f")" = ok ]\n',
                     "env": {"HIDDEN_DIR": str(self.hidden), "RUNS": str(self.runs)}, "runner": fc.HOST,
                     "skipped": [], "error": None, "toolchains": {"patched": [], "stock": []}}
        # The hidden file stands for a file of the checkout: an input of every unit.
        inputs = lambda tree: {"checkout": (self.hidden / "input").read_text()}
        for patch in (mock.patch.object(fc, "discover", lambda tree: [dict(self.unit)]),
                      mock.patch.object(fc, "resolve", no_toolchain),
                      mock.patch.object(fc, "run_inputs", inputs),
                      mock.patch.object(fc, "PASSES", self.temp / "passes"),
                      mock.patch.object(fc, "IN_CI", False),  # these tests also run in CI
                      mock.patch.dict(os.environ, {"AIR2LEAN_CAS_DIR": str(self.cas)})):
            patch.start()
            self.addCleanup(patch.stop)

    def run_checks(self, *argv):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            status = fc.main(["--jobs", "1", "--logs", str(self.temp / "logs"), *argv])
        return status, out.getvalue(), err.getvalue()

    def runs_of_unit(self):
        return len(self.runs.read_text().split()) if self.runs.exists() else 0

    def test_an_edit_of_an_input_runs_the_unit_again(self):
        (self.hidden / "input").write_text("ok\n")
        status, out, err = self.run_checks()
        self.assertEqual(status, 0, out + err)
        (self.hidden / "input").write_text("broken\n")
        status, out, err = self.run_checks()
        self.assertEqual(status, 1, out + err)  # rerun, not the first run's pass
        self.assertIn("1 failed", out)
        self.assertIn("FAILED synthetic: hidden input", err)
        self.assertEqual(self.run_checks()[0], 1)  # a failure records no pass
        self.assertEqual(self.runs_of_unit(), 3)
        (self.hidden / "input").write_text("ok\n")
        self.assertEqual(self.run_checks()[0], 0)  # the first run's inputs: its pass, no run
        self.assertEqual(self.runs_of_unit(), 3)
        self.assertEqual(list(self.cas.iterdir()), [])  # no pass is published to the shared store

    def test_a_pass_of_the_same_inputs_is_reused_unless_rerun(self):
        (self.hidden / "input").write_text("ok\n")
        self.assertEqual(self.run_checks("--pending")[0], 1)
        self.assertEqual(self.run_checks()[0], 0)
        status, out, _ = self.run_checks()
        self.assertEqual((status, self.runs_of_unit()), (0, 1))
        self.assertIn("a pass of the same inputs is recorded", out)
        self.assertIn("0 units (0 checks) run, 0 failed, 1 with a recorded pass", out)
        self.assertEqual(self.run_checks("--pending")[0], 0)
        self.assertEqual(self.run_checks("--rerun")[0], 0)
        self.assertEqual(self.runs_of_unit(), 2)
        self.unit["run"] += "true\n"  # another CI step: another key
        self.assertEqual(self.run_checks()[0], 0)
        self.assertEqual(self.runs_of_unit(), 3)

    def test_ci_never_reuses_or_records_a_pass(self):
        (self.hidden / "input").write_text("ok\n")
        self.assertEqual(self.run_checks()[0], 0)  # a local run records its pass
        with mock.patch.object(fc, "IN_CI", True):
            for _ in range(2):
                self.assertEqual(self.run_checks()[0], 0)
            self.assertEqual(self.run_checks("--pending")[0], 1)
        self.assertEqual(self.runs_of_unit(), 3)
        self.assertEqual(len(list((self.temp / "passes").iterdir())), 1)  # only the local one

    def test_no_pass_when_an_input_changes_during_the_run(self):
        (self.hidden / "input").write_text("ok\n")
        self.unit["run"] = 'echo run >> "$RUNS"\nprintf "ok\\n\\n" > "$HIDDEN_DIR/input"\n'
        status, out, _ = self.run_checks()
        self.assertEqual(status, 0)
        self.assertIn("the inputs changed during the run: no pass is recorded", out)
        (self.hidden / "input").write_text("ok\n")
        self.run_checks()
        self.assertEqual(self.runs_of_unit(), 2)
        self.assertFalse((self.temp / "passes").exists())

    def test_there_is_no_selection_by_key(self):
        # `--base REF` chose the units by the key's files; it is rejected, not ignored.
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as exit_:
            fc.main(["--base", "HEAD"])
        self.assertEqual(exit_.exception.code, 2)

    def test_prepare_resolves_every_units_toolchains_each_time(self):
        self.unit["toolchains"] = {"patched": [], "stock": ["0.16.0"]}
        resolved = []
        with mock.patch.object(fc, "resolve", lambda kind, version: resolved.append((kind, version)) or "zig"):
            for _ in range(2):
                self.assertEqual(self.run_checks("--prepare")[0], 0)
        self.assertEqual(resolved, [("stock", "0.16.0")] * 2)

    def test_a_unit_that_rebuilds_a_root_module_fails_the_run(self):
        # The race of 2026-10-20: a unit rebuilt root modules in place while others imported them.
        shared = self.temp / "build"
        (shared / "M").mkdir(parents=True)
        (shared / "M" / "A.olean").write_text("a")
        (shared / "M" / "A.trace").write_text("t")
        (self.hidden / "input").write_text("ok\n")
        self.unit["env"]["SHARED"] = str(shared)
        with mock.patch.object(fc, "SHARED", shared):
            self.assertEqual(self.run_checks()[0], 0)
            self.unit["run"] = 'printf t2 > "$SHARED/M/A.trace"\n'  # an up-to-date check: no race
            self.assertEqual(self.run_checks()[0], 0)
            self.unit["run"] = 'rm "$SHARED/M/A.olean"; printf b > "$SHARED/M/A.olean"\n'
            status, out, err = self.run_checks()
        self.assertEqual(status, 1, out + err)
        self.assertIn("build outputs changed while the units ran", err)
        self.assertIn("M/A.olean", err)


class RunInputs(unittest.TestCase):
    """`run_inputs` covers every file of a scratch checkout, the Lake build outputs and the
    environment, but not the run's own variables."""

    def test_every_file_build_output_and_variable_is_an_input(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / "tracked").write_text("1")
            (root / ".gitignore").write_text(".lake/\n")
            subprocess.run(["git", "-C", str(root), "add", "tracked", ".gitignore"], check=True)
            (root / "untracked").write_text("1")
            build = root / "tests/roadmap/.lake/build/lib/lean"
            build.mkdir(parents=True)
            (build / "M.olean").write_text("1")
            (root / ".lake/assurance").mkdir(parents=True)
            with mock.patch.object(fc, "ROOT", root), \
                    mock.patch.object(fc.GENERATED, "paths", lambda root: set()), \
                    mock.patch.object(fc.AS, "lake_env", lambda name: directory), \
                    mock.patch.object(fc.AS, "toolchain_runtime_sha256", lambda path: "lean"), \
                    mock.patch.dict(os.environ, {"AIR2LEAN_JOBS": "1"}):
                key = lambda: fc.digest(fc.run_inputs(fc.Tree()))
                first = key()
                (root / ".lake/assurance/cache.json").write_text("{}")  # a cache: no input
                for variable in ("AIR2LEAN_JOBS", "PWD", "CLAUDE_CODE_SESSION_ID", "WARP_X"):
                    os.environ[variable] = "changed"
                self.assertEqual(key(), first)
                for change in (lambda: (root / "tracked").write_text("2"),
                               lambda: (root / "untracked").write_text("2"),
                               lambda: (root / "new").write_text(""),
                               lambda: (build / "M.olean").write_text("2"),
                               lambda: os.environ.__setitem__("SOME_NEW_VARIABLE", "1")):
                    before = key()
                    change()
                    self.assertNotEqual(key(), before)


if __name__ == "__main__":
    unittest.main()
