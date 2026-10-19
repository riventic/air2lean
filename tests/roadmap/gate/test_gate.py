"""scripts/gate.py: which units the gate runs, in which order, and how a run treats them.

The units are derived from scripts/preflight.sh and scripts/regen.py, so these tests run over
the real repository: every preflight check and PR-scoped regen step is a unit or is run by one.
Every unit runs in the checkout, every time (docs/ci.md#parked-precise-input-tracking).
"""
import importlib.util
from pathlib import Path
import sys
import tempfile
import types
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location("air2lean_gate", ROOT / "scripts/gate.py")
gate = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = gate  # dataclasses resolve annotations through sys.modules
spec.loader.exec_module(gate)


class Units(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.units = gate.units("BASE", check=False)
        cls.by_name = {u.name: u for u in cls.units}

    def test_every_preflight_check_is_run(self):
        steps = {name for name, scope, _, _ in gate.REGEN.STEPS if scope == "pr"}
        covered = {c for name, c in gate.regen_checks().items() if name in steps}
        text = (ROOT / "scripts/preflight.sh").read_text()
        checks = gate.preflight_checks(text)
        # Every `check` line, also one inside an `if` block.
        self.assertEqual(len(checks), sum(l.lstrip().startswith("check '") for l in text.splitlines()))
        self.assertIn("generated modules are fresh translations", [label for label, _ in checks])
        for label, argv in checks:
            with self.subTest(label=label):
                script = gate.script_of(argv)
                self.assertTrue("preflight:" + label in self.by_name
                                or script in ("scripts/generated.py", "scripts/full-build.sh")
                                or tuple(gate.normalized(argv)) in covered, label)
        # The generated-module check is one of them: regen:gen runs it, not a second unit.
        self.assertIn(("scripts/gen-integrity.py", "check"), covered)
        self.assertFalse(any("gen-integrity" in " ".join(map(str, u.argv)) for u in self.units))

    def test_every_pr_regen_step_is_a_unit(self):
        for name, scope, _, _ in gate.REGEN.STEPS:
            if scope == "pr" and name != "translator":
                self.assertIn("regen:" + name, self.by_name)
            if scope == "tree":
                self.assertNotIn("regen:" + name, self.by_name)

    def test_writers_run_one_at_a_time(self):
        regen = [u for u in self.units if u.name.startswith("regen:")]
        for earlier, later in zip(regen, regen[1:]):
            self.assertIn(earlier.name, later.after)
        for u in self.units:
            if u.name.startswith("preflight:"):
                self.assertIn(regen[-1].name, u.after)
            if u.name.startswith("regen:"):
                self.assertEqual(u.requires, ("full-build",))
                self.assertNotIn("--check", u.argv)

    def test_check_mode_never_regenerates(self):
        for u in gate.units("BASE", check=True):
            if u.name.startswith("regen:"):
                self.assertIn("--check", u.argv)

    def test_proof_framework_compares_with_the_base(self):
        pf = [u for u in self.units if gate.script_of(u.argv) == "scripts/proof-framework.py"]
        self.assertEqual(len(pf), 1)
        self.assertEqual(pf[0].argv[-2:], ["--base", "BASE"])

    def test_a_check_the_gate_cannot_run_as_written_fails_closed(self):
        with mock.patch.object(gate, "preflight_checks", return_value=[("x", ["scripts/x.py", "$scratch/x"])]):
            with self.assertRaises(SystemExit):
                gate.units("BASE", check=False)
        # A check line the parser cannot read as one command is never dropped silently.
        for line in ('check "x" a \\', "check 'x' a && b", "check 'x", "  check x",
                     "python3 scripts/x.py || failed+=(x)", "  [ -n y ] && tests/x/check.sh"):
            with self.subTest(line=line), self.assertRaises(SystemExit):
                gate.preflight_checks(line + "\n")
        self.assertEqual(gate.preflight_checks('check "x y" a b  # note\ncheck() {\n'), [("x y", ["a", "b"])])

    def test_writers_of_the_generated_files_run_one_at_a_time_before_the_build(self):
        writers = [u for u in self.units if u.name.startswith(("materialize:", "fetch:"))]
        for earlier, later in zip(writers, writers[1:]):
            self.assertIn(earlier.name, later.after)
        self.assertTrue({u.name for u in writers} <= set(self.by_name["full-build"].after))

    def test_the_fixture_checks_run_after_the_regeneration(self):
        # As in the sequence the gate replaces (regen.sh, then the checks): a stale committed
        # output (the theorem inventory after a proof edit) is regenerated before a test reads it.
        self.assertIn("--no-fixtures", self.by_name["full-build"].argv)
        fixtures = self.by_name["fixtures"]
        self.assertEqual((fixtures.argv, fixtures.requires), (["bash", "scripts/fixture-checks.sh"], ("full-build",)))
        regen = [u.name for u in self.units if u.name.startswith("regen:")]
        self.assertIn(regen[-1], fixtures.after)


class Schedule(unittest.TestCase):
    def run_units(self, units):
        with tempfile.TemporaryDirectory() as logs:
            a = types.SimpleNamespace(base="HEAD", jobs=2, logs=logs, check=False)
            run = gate.Run(a, units)
            return run, run.go()

    def test_a_failed_requirement_skips_and_an_ordering_does_not(self):
        run, failed = self.run_units([gate.Unit("a", ["false"]),
                                      gate.Unit("b", ["true"], after=("a",), requires=("a",)),
                                      gate.Unit("c", ["true"], after=("a",))])
        self.assertEqual(failed, {"a", "b"})
        self.assertTrue(run.results["b"][0].startswith("skipped"))
        self.assertEqual(run.results["c"][0], "ran")

    def test_every_unit_runs_every_time(self):
        # No result of an earlier run is taken: the same passing unit runs again.
        unit = gate.Unit("t", [gate.PY, "-c", "open('README.md').read()"])
        for _ in range(2):
            run, failed = self.run_units([unit])
            self.assertEqual((failed, run.results["t"][0]), (set(), "ran"))

    def test_an_edit_during_the_run_is_found(self):
        run, _ = self.run_units([])
        self.assertEqual(run.external_changes(), [])
        head, before = run.start
        edited = dict(before, **{"scripts/gate.py": "another digest"})
        with mock.patch.object(gate, "dirty_state", return_value=edited):
            self.assertEqual(run.external_changes(), ["scripts/gate.py"])
            run.written.add("scripts/gate.py")  # a unit regenerated it: expected
            self.assertEqual(run.external_changes(), [])
        run.start = ("0" * 40, before)  # HEAD moved (a commit or checkout during the run)
        self.assertTrue(run.external_changes()[0].startswith("HEAD"))


if __name__ == "__main__":
    unittest.main()
