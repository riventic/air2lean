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


class Repo(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="air2lean-fixtures-test.")
        self.addCleanup(tmp.cleanup)
        self.repo = Path(tmp.name).resolve()
        shutil.copy(ROOT / "lean-toolchain", self.repo / "lean-toolchain")
        self.write("lakefile.toml", 'name = "air2lean"\n[[lean_lib]]\nname = "Lib"\n')
        self.write("Lib.lean", "def lib : Nat := 1\n")
        self.package = self.repo / "tests/roadmap"
        env = {k: v for k, v in os.environ.items() if k != "AIR2LEAN_CAS_DIR" and not k.startswith("LAKE_")}
        for patch in (mock.patch.object(fx, "ROOT", self.repo), mock.patch.object(fx, "PACKAGE", self.package),
                      mock.patch.dict(os.environ, env, clear=True)):
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


class Audit(unittest.TestCase):
    """Controls of `fixtures.py audit` against this repository's extractor (tools.Assurance,
    built by scripts/assumptions.py): a Lake-built module with a `sorry` or a non-standard axiom
    is rejected, a missing named theorem too; an honest one passes."""

    def build(self, text):
        tmp = tempfile.TemporaryDirectory(prefix="air2lean-fixtures-audit-test.")
        self.addCleanup(tmp.cleanup)
        workspace = Path(tmp.name)
        (workspace / "lakefile.toml").write_text(
            f'name = "fixtures"\n[[require]]\nname = "air2lean"\npath = "{ROOT}"\n'
            '[[lean_lib]]\nname = "AuditControl"\n')
        (workspace / "AuditControl.lean").write_text(text)
        env = {k: v for k, v in os.environ.items() if k != "AIR2LEAN_CAS_DIR" and not k.startswith("LAKE_")}
        with mock.patch.dict(os.environ, env, clear=True):
            self.assertEqual(fx.lake(workspace, ["build", "AuditControl"], capture=True).returncode, 0)
        return workspace / ".lake/build/lib/lean"

    def test_sorry_is_rejected(self):
        lib = self.build("theorem honest : 1 + 1 = 2 := rfl\ntheorem sorry_control : (1 : Nat) = 2 := sorry\n")
        self.assertEqual(fx.audit(["AuditControl"], ["honest"], None, lib), 1)

    def test_project_axiom_is_rejected(self):
        lib = self.build("axiom control_ax : (1 : Nat) = 2\ntheorem axiom_control : (1 : Nat) = 2 := control_ax\n")
        self.assertEqual(fx.audit(["AuditControl"], [], None, lib), 1)

    def test_missing_theorem_is_rejected_and_honest_passes(self):
        lib = self.build("theorem honest : 1 + 1 = 2 := rfl\n")
        self.assertEqual(fx.audit(["AuditControl"], ["honest", "gone"], None, lib), 1)
        self.assertEqual(fx.audit(["AuditControl"], ["honest"], None, lib), 0)


if __name__ == "__main__":
    unittest.main()
