"""scripts/gate.py: which units the gate runs, their keys, restricted runs and ordering.

The units are derived from scripts/preflight.sh and scripts/regen.py, so these tests run over
the real repository: every preflight check and PR-scoped regen step is a unit or is run by one.
A key (scripts/ci-reuse.py's, over a snapshot commit of the checkout) changes with every input of
its unit (file content, a transitive Lean import, the tracked names, the gate's own sources) and
not with a file outside a declaration. A restricted run reads the declared inputs in their
current state and fails on any other tracked file.
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
CR = gate.CR


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

    def test_every_declaration_names_a_unit(self):
        self.assertTrue(set(CR.local_declarations(ROOT)) <= set(self.by_name))


class Keys(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.keys = gate.Keys("HEAD")
        units = {u.name: u for u in gate.units("HEAD", check=False)}
        cls.claims, cls.check = units["regen:claims"], units["preflight:mutation map"]

    def changed(self, unit, path):
        """Whether a different content of PATH changes the unit's key."""
        before = self.keys.key(unit)
        with mock.patch.dict(self.keys.tree, {path: ("100644", "0" * 40)}):
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

    def test_a_whole_tree_unit_follows_every_file_and_the_revision(self):
        self.assertFalse(self.keys.declared_unit(self.check))
        self.assertTrue(self.changed(self.check, "docs/ci.md"))
        self.assertEqual(self.keys.affected(self.check, ["docs/ci.md"]), ["docs/ci.md"])
        before = self.keys.key(self.check)
        with mock.patch.object(self.keys, "head", "another commit"):
            self.assertNotEqual(before, self.keys.key(self.check))

    def test_tracked_names_and_the_gate_are_in_every_key(self):
        for unit in (self.claims, self.check):
            with self.subTest(unit=unit.name):
                before = self.keys.key(unit)
                with mock.patch.dict(self.keys.tree, {"new/file.txt": ("100644", "0" * 40)}):
                    self.assertNotEqual(before, self.keys.key(unit))
                self.assertTrue(self.changed(unit, "scripts/gate.py"))
                self.assertTrue(self.changed(unit, "scripts/ci-reuse.py"))


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
        commit = CR.snapshot(self.repo)
        return gate.restricted_run(argv, CR.Inputs(keep), "test", commit, self.log, root=self.repo)

    def test_declared_inputs_are_readable_and_others_are_not(self):
        self.assertEqual(self.run_restricted(["cat", "a.txt"], ["a.txt"]), 0)
        self.assertNotEqual(self.run_restricted(["cat", "b.txt"], ["a.txt"]), 0)
        self.assertNotEqual(self.run_restricted(["cat", "sub/c.txt"], ["a.txt"]), 0)
        self.assertEqual(self.run_restricted(["cat", "sub/c.txt"], ["sub/**"]), 0)

    def test_the_checkout_state_is_used(self):
        (self.repo / "a.txt").write_text("new\n")  # uncommitted edit
        (self.repo / "d.txt").write_text("d\n")    # new file
        self.assertEqual(self.run_restricted(["grep", "-q", "new", "a.txt"], ["a.txt"]), 0)
        self.assertEqual(self.run_restricted(["cat", "d.txt"], ["d.txt"]), 0)
        (self.repo / "b.txt").unlink()            # deleted in the checkout: absent there too
        self.assertEqual(self.run_restricted(["test", "!", "-e", "b.txt"], ["a.txt"]), 0)

    def test_changing_a_withheld_file_fails(self):
        self.assertNotEqual(self.run_restricted(["rm", "b.txt"], ["a.txt"]), 0)

    def test_no_worktree_is_left_behind_and_the_checkout_is_untouched(self):
        self.run_restricted(["true"], ["a.txt"])
        worktrees = subprocess.run(["git", "-C", str(self.repo), "worktree", "list"], capture_output=True,
                                   text=True, check=True).stdout.splitlines()
        self.assertEqual(len(worktrees), 1)
        status = subprocess.run(["git", "-C", str(self.repo), "status", "--porcelain"], capture_output=True,
                                text=True, check=True).stdout
        self.assertEqual(status, "")


class Store(unittest.TestCase):
    def test_a_record_is_found_by_its_key_with_its_files(self):
        with tempfile.TemporaryDirectory() as tmp, mock.patch.dict(os.environ, {"AIR2LEAN_CAS_DIR": tmp}):
            out = Path(tmp) / "out.json"
            out.write_text("{}\n")
            self.assertIsNone(CR.lookup_local("k1"))
            self.assertTrue(CR.record_local("k1", {"unit": "u"}, [("gen/out.json", out)]))
            self.assertFalse(CR.record_local("k1", {"unit": "u"}))  # published already
            entry = CR.lookup_local("k1")
            self.assertEqual((entry / "files/gen/out.json").read_text(), "{}\n")
            self.assertIsNone(CR.lookup_local("k2"))
            CR.withdraw_local("k1")
            self.assertIsNone(CR.lookup_local("k1"))


class Schedule(unittest.TestCase):
    def run_units(self, units):
        with tempfile.TemporaryDirectory() as logs:
            a = types.SimpleNamespace(base="HEAD", no_cache=True, jobs=2, logs=logs, check=False)
            run = gate.Run(a, units)
            return run, run.go()

    def test_a_failed_requirement_skips_and_an_ordering_does_not(self):
        run, failed = self.run_units([gate.Unit("a", ["false"], cache=False),
                                      gate.Unit("b", ["true"], after=("a",), requires=("a",), cache=False),
                                      gate.Unit("c", ["true"], after=("a",), cache=False)])
        self.assertEqual(failed, {"a", "b"})
        self.assertTrue(run.results["b"][0].startswith("skipped"))
        self.assertEqual(run.results["c"][0], "ran")

    def test_an_edit_during_the_run_is_found_and_its_records_withdrawn(self):
        run, _ = self.run_units([])
        self.assertEqual(run.external_changes(), [])
        empty = "4b825dc642cb6eb9a060e54bf8d69288fbee4904"  # git's empty tree: every file "changed"
        with tempfile.TemporaryDirectory() as tmp, mock.patch.dict(os.environ, {"AIR2LEAN_CAS_DIR": tmp}):
            with mock.patch.object(CR, "snapshot", return_value=empty):
                edited = run.external_changes()
            self.assertIn("scripts/gate.py", edited)
            run.written |= set(edited)  # a unit regenerated them: expected
            with mock.patch.object(CR, "snapshot", return_value=empty):
                self.assertEqual(run.external_changes(), [])
            CR.record_local("k", {"unit": "u"})
            run.published.append("k")
            run.withdraw()
            self.assertIsNone(CR.lookup_local("k"))


if __name__ == "__main__":
    unittest.main()
