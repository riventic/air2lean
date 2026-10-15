"""scripts/gate.py: which units the gate runs, their cache keys, restricted runs and ordering.

The units are derived from scripts/preflight.sh and scripts/regen.py, so these tests run over
the real repository: every preflight check and PR-scoped regen step is a unit or is run by one.
A key changes with every input of its unit (file content, a transitive Lean import, the file
names, the gate's own sources) and not with a file outside a declaration. A restricted run reads
the declared inputs in their current state and fails on any other tracked file.
"""
import importlib.util
import os
from pathlib import Path
import subprocess
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
        for label, argv in gate.preflight_checks((ROOT / "scripts/preflight.sh").read_text()):
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


class Keys(unittest.TestCase):
    def setUp(self):
        self.keys = gate.Keys("HEAD")
        self.claims = next(u for u in gate.units("HEAD", check=False) if u.name == "regen:claims")
        self.check = next(u for u in gate.units("HEAD", check=False) if u.name.startswith("preflight:mutation"))

    def changed(self, unit, path, mutate=None):
        before = self.keys.key(unit)
        if mutate:
            mutate()
        else:
            self.keys.tree.digest(path)
            self.keys.tree._digest[path] = "changed"
        return before != self.keys.key(unit)

    def test_a_changed_input_changes_the_key(self):
        for path in ("tests/roadmap/claims/Fixture.lean", "scripts/assumptions.py", "assurance/policy.json"):
            with self.subTest(path=path):
                self.assertIn(path, self.keys.files(self.claims))
                self.assertTrue(self.changed(self.claims, path))

    def test_a_transitive_lean_import_is_an_input(self):
        # Fixture.lean imports ZigLean.Sep.Full.Witness, which imports ZigLean/Mem/Basic.lean.
        self.assertIn("ZigLean/Mem/Basic.lean", self.keys.files(self.claims))
        self.assertTrue(self.changed(self.claims, "ZigLean/Mem/Basic.lean"))

    def test_a_file_outside_the_declaration_keeps_the_key(self):
        for path in ("docs/ci.md", "Proofs/Floatops/Proofs.lean", "scripts/support-matrix.py"):
            with self.subTest(path=path):
                self.assertNotIn(path, self.keys.files(self.claims))
                self.assertFalse(self.changed(self.claims, path))
                self.assertEqual(self.keys.affected(self.claims, [path]), [])

    def test_a_whole_tree_unit_follows_every_file(self):
        self.assertIsNone(self.check.inputs)
        self.assertTrue(self.changed(self.check, "docs/ci.md"))
        self.assertEqual(self.keys.affected(self.check, ["docs/ci.md"]), ["docs/ci.md"])

    def test_file_names_and_the_gate_are_in_every_key(self):
        for unit in (self.claims, self.check):
            with self.subTest(unit=unit.name):
                self.assertTrue(self.changed(unit, None, lambda: setattr(self.keys, "names", "other")))
                self.keys = gate.Keys("HEAD")
                self.assertTrue(self.changed(unit, "scripts/gate.py"))

    def test_a_command_without_a_script_keys_the_revision(self):
        unit = gate.Unit("u", ["python3", "-m", "unittest", "discover"])
        self.assertTrue(self.keys.reads_git(unit))


class Restricted(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name).resolve() / "repo"
        self.repo.mkdir()
        for name, text in (("a.txt", "old\n"), ("b.txt", "secret\n"), ("sub/c.txt", "c\n")):
            (self.repo / name).parent.mkdir(parents=True, exist_ok=True)
            (self.repo / name).write_text(text)
        git = ["git", "-C", str(self.repo), "-c", "user.name=t", "-c", "user.email=t@t"]
        subprocess.run(git[:3] + ["init", "-q"], check=True)
        subprocess.run(git + ["add", "-A"], check=True)
        subprocess.run(git + ["commit", "-qm", "x"], check=True)
        self.log = Path(self.tmp.name) / "log"

    def run_restricted(self, argv, keep):
        return gate.restricted_run(argv, keep, self.log, root=self.repo)

    def test_declared_inputs_are_readable_and_others_are_not(self):
        self.assertEqual(self.run_restricted(["cat", "a.txt"], ["a.txt"]), 0)
        self.assertNotEqual(self.run_restricted(["cat", "b.txt"], ["a.txt"]), 0)
        self.assertNotEqual(self.run_restricted(["cat", "sub/c.txt"], ["a.txt"]), 0)

    def test_the_checkout_state_of_the_inputs_is_used(self):
        (self.repo / "a.txt").write_text("new\n")  # uncommitted edit
        (self.repo / "d.txt").write_text("d\n")    # new file
        self.assertEqual(self.run_restricted(["grep", "-q", "new", "a.txt"], ["a.txt", "d.txt"]), 0)
        self.assertEqual(self.run_restricted(["cat", "d.txt"], ["a.txt", "d.txt"]), 0)
        (self.repo / "b.txt").unlink()            # deleted in the checkout: absent there too
        self.assertEqual(self.run_restricted(["test", "!", "-e", "b.txt"], ["a.txt"]), 0)

    def test_no_worktree_is_left_behind(self):
        self.run_restricted(["true"], ["a.txt"])
        worktrees = subprocess.run(["git", "-C", str(self.repo), "worktree", "list"], capture_output=True,
                                   text=True, check=True).stdout.splitlines()
        self.assertEqual(len(worktrees), 1)


class Store(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        for patch in (mock.patch.dict(os.environ, {"AIR2LEAN_CAS_DIR": str(root / "cas")}),
                      mock.patch.object(gate, "ROOT", root)):
            patch.start()
            self.addCleanup(patch.stop)
        self.root = root

    def test_a_pass_is_found_by_its_key_and_restores_outputs(self):
        unit = gate.Unit("materialize:x", ["true"], outputs=("gen/out.json",))
        (self.root / "gen").mkdir()
        (self.root / "gen/out.json").write_text("{}\n")
        self.assertIsNone(gate.recorded("k1"))
        gate.record("k1", unit, 1.0)
        (self.root / "gen/out.json").unlink()
        entry = gate.recorded("k1")
        self.assertIsNotNone(entry)
        gate.restore(entry, unit)
        self.assertEqual((self.root / "gen/out.json").read_text(), "{}\n")
        self.assertIsNone(gate.recorded("k2"))


class Schedule(unittest.TestCase):
    def test_a_failed_requirement_skips_and_an_ordering_does_not(self):
        with tempfile.TemporaryDirectory() as logs:
            a = types.SimpleNamespace(base="HEAD", no_cache=True, jobs=2, logs=logs, check=False)
            units = [gate.Unit("a", ["false"], cache=False),
                     gate.Unit("b", ["true"], after=("a",), requires=("a",), cache=False),
                     gate.Unit("c", ["true"], after=("a",), cache=False)]
            run = gate.Run(a, units)
            failed = run.go()
        self.assertEqual(failed, {"a", "b"})
        self.assertTrue(run.results["b"][0].startswith("skipped"))
        self.assertEqual(run.results["c"][0], "ran")


if __name__ == "__main__":
    unittest.main()
