"""scripts/gate.py: which units the gate runs, in which order, and what a unit's pre-key names.

The units are derived from scripts/preflight.sh and scripts/regen.py, so these tests run over
the real repository: every preflight check and PR-scoped regen step is a unit or is run by one.
A unit is keyed by scripts/ci-reuse.py's traced records (tests/roadmap/ci-reuse/test_traced.py);
its pre-key names the check it runs and the files it produces.
"""
import importlib.util
import json
import os
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
CR = gate.CR


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
                self.assertIn("--check", u.check_argv)
                self.assertNotIn("--check", u.argv)

    def test_check_mode_never_regenerates(self):
        for u in gate.units("BASE", check=True):
            if u.name.startswith("regen:"):
                self.assertEqual(u.argv, u.check_argv)

    def test_proof_framework_compares_with_the_base(self):
        pf = [u for u in self.units if gate.script_of(u.argv) == "scripts/proof-framework.py"]
        self.assertEqual(len(pf), 1)
        self.assertEqual(pf[0].argv[-2:], ["--base", "BASE"])

    def test_a_check_the_gate_cannot_run_as_written_fails_closed(self):
        with mock.patch.object(gate, "preflight_checks", return_value=[("x", ["scripts/x.py", "$scratch/x"])]):
            with self.assertRaises(SystemExit):
                gate.units("BASE", check=False)

    def test_writers_of_the_generated_files_run_one_at_a_time_before_the_build(self):
        # Every traced unit gets a copy of the generated files: none may change while one runs.
        writers = [u for u in self.units if u.name.startswith(("materialize:", "fetch:"))]
        for earlier, later in zip(writers, writers[1:]):
            self.assertIn(earlier.name, later.after)
        self.assertTrue({u.name for u in writers} <= set(self.by_name["full-build"].after))

    def test_the_pre_key_names_the_check_and_its_outputs(self):
        claims = self.by_name["regen:claims"]
        self.assertEqual(claims.identity()["argv"], [str(a) for a in claims.check_argv])
        self.assertIn("--check", claims.identity()["argv"])
        materialize = next(u for u in self.units if u.name.startswith("materialize:"))
        self.assertEqual(materialize.identity()["outputs"], list(materialize.outputs))
        self.assertTrue(materialize.outputs)


class Schedule(unittest.TestCase):
    def run_units(self, units, no_cache=True):
        with tempfile.TemporaryDirectory() as logs:
            a = types.SimpleNamespace(base="HEAD", no_cache=no_cache, jobs=2, logs=logs, check=False)
            run = gate.Run(a, units, CR.Outside(ROOT))
            failed = run.go()
            run.publish()
            return run, failed

    def test_a_failed_requirement_skips_and_an_ordering_does_not(self):
        run, failed = self.run_units([gate.Unit("a", ["false"], cache=False),
                                      gate.Unit("b", ["true"], after=("a",), requires=("a",), cache=False),
                                      gate.Unit("c", ["true"], after=("a",), cache=False)])
        self.assertEqual(failed, {"a", "b"})
        self.assertTrue(run.results["b"][0].startswith("skipped"))
        self.assertEqual(run.results["c"][0], "ran")

    def test_a_traced_unit_is_recorded_and_then_reused(self):
        unit = gate.Unit("t", [gate.PY, "-c", "open('README.md').read()"])
        with tempfile.TemporaryDirectory() as cas, mock.patch.dict(os.environ, {"AIR2LEAN_CAS_DIR": cas}):
            run, failed = self.run_units([unit], no_cache=False)
            self.assertEqual((failed, run.results["t"][0]), (set(), "ran"))
            again, _ = self.run_units([unit], no_cache=False)
            # Inside a sandbox already (the gate's own run of this test) nothing is recorded.
            self.assertEqual(again.results["t"][0], "cached" if run.sound else "ran")

    def test_an_edit_during_the_run_is_found(self):
        run, _ = self.run_units([])
        self.assertEqual(run.external_changes(), [])
        empty = "4b825dc642cb6eb9a060e54bf8d69288fbee4904"  # git's empty tree: every file "changed"
        with mock.patch.object(CR, "snapshot", return_value=empty):
            edited = run.external_changes()
        self.assertIn("scripts/gate.py", edited)
        run.written |= set(edited)  # a unit regenerated them: expected
        with mock.patch.object(CR, "snapshot", return_value=empty):
            self.assertEqual(run.external_changes(), [])


if __name__ == "__main__":
    unittest.main()
