"""scripts/fixtures.py: module-name ownership and mutant verdicts (docs/build-cache.md#proof-fixtures).

A tiny repository stands in for the real one: a root package `air2lean` with the library `Lib`
and a fixture package `tests/roadmap` that requires it by path. Lake builds its few one-line
modules (seconds), without the shared artifact cache.

- Two libraries with a module of the same name: Lake builds one of them and reports success for
  both (the other is never elaborated), so the build refuses; so it does for a fixture module
  under a root of the root package.
- A mutant is killed only when the module that must fail fails itself: a failed import, a module
  that still builds or a missing expected message is no kill.
"""
import importlib.util
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("air2lean_fixtures", ROOT / "scripts/fixtures.py")
fx = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fx)


def without_cache():
    """This environment without the shared artifact cache (the tests' modules stay out of it)."""
    env = {k: v for k, v in os.environ.items() if k != "AIR2LEAN_CAS_DIR" and not k.startswith("LAKE_")}
    return mock.patch.dict(os.environ, env, clear=True)


class Repo(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="air2lean-fixtures-test.")
        self.addCleanup(tmp.cleanup)
        self.repo = Path(tmp.name).resolve()
        shutil.copy(ROOT / "lean-toolchain", self.repo / "lean-toolchain")
        self.write("lakefile.toml", 'name = "air2lean"\n[[lean_lib]]\nname = "Lib"\n')
        self.write("Lib.lean", "def lib : Nat := 1\n")
        self.package = self.repo / "tests/roadmap"
        for patch in (mock.patch.object(fx, "ROOT", self.repo), mock.patch.object(fx, "PACKAGE", self.package),
                      without_cache()):
            patch.start()
            self.addCleanup(patch.stop)

    def write(self, name, text):
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def fixtures(self, libs):
        self.write("tests/roadmap/lakefile.toml", 'name = "fixtures"\n[[require]]\nname = "air2lean"\npath = "../.."\n'
                   + "".join(f'[[lean_lib]]\nname = "{n}"\nsrcDir = "{d}"\nglobs = {g}\n' for n, d, g in libs))


class Names(Repo):
    def test_same_module_in_two_libraries(self):
        self.write("tests/roadmap/a/Eval.lean", "def x := 1\n")
        self.write("tests/roadmap/b/Eval.lean", 'def y : Nat := "not a Nat"\n')
        self.fixtures([("A", "a", '["Eval"]'), ("B", "b", '["Eval"]')])
        with self.assertRaises(SystemExit) as raised:
            fx.check_names(self.package)
        self.assertIn("module root Eval is in libraries A and B", str(raised.exception))

    def test_root_package_root(self):
        self.write("tests/roadmap/a/Lib/Extra.lean", "def z := 1\n")
        self.fixtures([("A", "a", '["Lib.+"]')])
        with self.assertRaises(SystemExit) as raised:
            fx.check_names(self.package)
        self.assertIn("module root Lib is a root of the root package", str(raised.exception))

    def test_distinct_roots(self):
        self.write("tests/roadmap/a/A/Eval.lean", "def x := 1\n")
        self.write("tests/roadmap/a/Spec.lean", "def s := 1\n")
        self.write("tests/roadmap/b/B/Eval.lean", "def y := 1\n")
        self.fixtures([("A", "a", '["A.+", "Spec"]'), ("B", "b", '["B.+"]')])
        self.assertEqual(fx.check_names(self.package), {"A": ["A.Eval", "Spec"], "B": ["B.Eval"]})
        self.assertEqual(fx.files(self.repo), ["tests/roadmap/a/A/Eval.lean", "tests/roadmap/a/Spec.lean",
                                               "tests/roadmap/b/B/Eval.lean"])


class Mutant(Repo):
    def mutant(self, base, use, expect=()):
        src = self.repo / "src"
        shutil.rmtree(src, ignore_errors=True)
        (src / "Fix").mkdir(parents=True)
        (src / "Fix/Base.lean").write_text(base)
        (src / "Fix/Use.lean").write_text("import Fix.Base\nimport Lib\n" + use)
        return fx.mutant("t", src, ["Fix.Use"], list(expect))

    def test_kill_in_the_module_itself(self):
        self.assertEqual(self.mutant("def base : Nat := 2\n", "example : base = 1 := by decide\n",
                                     ["proved that the proposition"]), 0)

    def test_failed_import_is_no_kill(self):
        self.assertEqual(self.mutant('def base : Nat := "two"\n', "example : base = 1 := by decide\n"), 1)

    def test_still_builds(self):
        self.assertEqual(self.mutant("def base : Nat := 1\n", "example : base = 1 := by decide\n"), 1)

    def test_expected_message_missing(self):
        self.assertEqual(self.mutant("def base : Nat := 2\n", "example : base = 1 := by decide\n",
                                     ["did not evaluate to"]), 1)


class Instance(unittest.TestCase):
    """`fixtures.py instance`: an instance is its primary with whole name components renamed, in
    text and path; a drifted instance, a partial-name match or an absent name fails."""

    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="air2lean-fixtures-instance-test.")
        self.addCleanup(tmp.cleanup)
        self.dir = Path(tmp.name)
        self.primary = self.dir / "Fix/V0_17_0/Model.lean"
        self.primary.parent.mkdir(parents=True)
        self.primary.write_text("import Fix.V0_17_0.Gen\nnamespace Fix.V0_17_0.Model\n"
                                "-- XV0_17_0 V0_17_0x stay\nend Fix.V0_17_0.Model\n")
        self.instance = self.dir / "Fix/V0_14_1/Model.lean"

    def test_write_then_check(self):
        self.assertEqual(fx.instance(self.primary, ["V0_17_0=V0_14_1"], True), 0)
        self.assertEqual(self.instance.read_text(), "import Fix.V0_14_1.Gen\nnamespace Fix.V0_14_1.Model\n"
                         "-- XV0_17_0 V0_17_0x stay\nend Fix.V0_14_1.Model\n")
        self.assertEqual(fx.instance(self.primary, ["V0_17_0=V0_14_1"], False), 0)

    def test_drift_fails(self):
        fx.instance(self.primary, ["V0_17_0=V0_14_1"], True)
        self.instance.write_text(self.instance.read_text() + "theorem extra : True := trivial\n")
        self.assertEqual(fx.instance(self.primary, ["V0_17_0=V0_14_1"], False), 1)

    def test_missing_instance_fails(self):
        self.assertEqual(fx.instance(self.primary, ["V0_17_0=V0_14_1"], False), 1)

    def test_absent_name_fails(self):
        with self.assertRaises(SystemExit):
            fx.instance(self.primary, ["V0_16_0=V0_14_1"], False)


class Run(Repo):
    def test_runs_built_modules_only(self):
        self.write("tests/roadmap/a/A/Main.lean", 'namespace A\ndef main : IO Unit := IO.println "a line"\nend A\n')
        self.fixtures([("A", "a", '["A.+"]')])
        out = self.repo / "out"
        # Not built yet: the run refuses instead of loading a stale or missing module.
        self.assertEqual(fx.run(out, ["A.Main:A.main"]), 1)
        self.assertEqual(fx.build(["A"]), 0)
        self.assertEqual(fx.run(out, ["A.Main:A.main"]), 0)
        self.assertEqual((out / "A.main.txt").read_text(), "a line\n")
        # A changed source is out of date until it is built again.
        self.write("tests/roadmap/a/A/Main.lean", 'namespace A\ndef main : IO Unit := IO.println "b"\nend A\n')
        self.assertEqual(fx.run(out, ["A.Main:A.main"]), 1)


class Audit(unittest.TestCase):
    """Controls of `fixtures.py audit` against this repository's extractor (tools.Assurance,
    built by scripts/assumptions.py): a Lake-built module with a `sorry` or a non-standard axiom
    is rejected, a missing named theorem too; an honest one passes."""

    def build(self, text):
        tmp = tempfile.TemporaryDirectory(prefix="air2lean-fixtures-audit-test.")
        self.addCleanup(tmp.cleanup)
        workspace = Path(tmp.name)
        # The repository's toolchain: outside the checkout elan would pick its default one, and CI
        # installs elan with none (`elan-init --default-toolchain none`), so `lake` failed at once.
        shutil.copy(ROOT / "lean-toolchain", workspace / "lean-toolchain")
        (workspace / "lakefile.toml").write_text(
            f'name = "fixtures"\n[[require]]\nname = "air2lean"\npath = "{ROOT}"\n'
            '[[lean_lib]]\nname = "AuditControl"\n')
        (workspace / "AuditControl.lean").write_text(text)
        with without_cache():
            done = fx.lake(workspace, ["build", "AuditControl"], capture=True)
        self.assertEqual(done.returncode, 0, done.stdout)  # a setup failure shows Lake's output
        return workspace / ".lake/build/lib/lean"

    def test_sorry_is_rejected(self):
        lib = self.build("theorem honest : 1 + 1 = 2 := rfl\ntheorem sorry_control : (1 : Nat) = 2 := sorry\n")
        self.assertEqual(fx.audit(["AuditControl"], ["honest"], None, lib), 1)

    def test_project_axiom_is_rejected(self):
        lib = self.build("axiom control_ax : (1 : Nat) = 2\ntheorem axiom_control : (1 : Nat) = 2 := control_ax\n")
        self.assertEqual(fx.audit(["AuditControl"], [], None, lib), 1)

    def test_definition_is_audited(self):
        """A definition whose value carries a proof (as `AllocFba.FBA.ledger`), used by no theorem."""
        lib = self.build("structure Claim where h : (1 : Nat) + 1 = 2\n"
                         "def good_claim : Claim := ⟨rfl⟩\ndef bad_claim : Claim := ⟨sorry⟩\n")
        self.assertEqual(fx.audit(["AuditControl"], ["good_claim", "bad_claim"], None, lib), 1)
        self.assertEqual(fx.audit(["AuditControl"], [], None, lib), 1)  # the sorry, unnamed

    def test_missing_theorem_is_rejected_and_honest_passes(self):
        lib = self.build("theorem honest : 1 + 1 = 2 := rfl\nstructure Claim where h : (1 : Nat) + 1 = 2\n"
                         "def good_claim : Claim := ⟨rfl⟩\n")
        self.assertEqual(fx.audit(["AuditControl"], ["honest", "gone"], None, lib), 1)
        self.assertEqual(fx.audit(["AuditControl"], ["honest", "good_claim"], None, lib), 0)


if __name__ == "__main__":
    unittest.main()
