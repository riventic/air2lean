"""scripts/lean-deps.py --files / --elaborate: which Lean files the full build elaborates.

A tiny repository (one library `Lib` with `Lib/A.lean`) stands in for the real one: a file outside
the library that imports only Lean and `Lib` modules is standalone and elaborated; a file with a
fixture's own import is left to its check; an import of a `Lib` module that does not exist (a
renamed or split module, the break of the strength logs after #342) is an error for every file;
a stale cache entry is never hit (the key covers the transitive library sources).
"""
import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("lean_deps", ROOT / "scripts/lean-deps.py")
ld = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ld)


class Classify(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)
        self.saved = ld.ROOT
        ld.ROOT = self.repo
        self.addCleanup(setattr, ld, "ROOT", self.saved)
        self.write("lakefile.toml", '[[lean_lib]]\nname = "Lib"\n')
        self.write("lean-toolchain", "leanprover/lean4:test\n")
        self.write("Lib/A.lean", "def a := 1\n")
        self.write("Lib/B.lean", "import Lib.A\ndef b := a\n")

    def write(self, name, text):
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def classify(self):
        subprocess.run(["git", "init", "-q"], cwd=self.repo, check=True)
        subprocess.run(["git", "add", "-A"], cwd=self.repo, check=True)
        return ld.classify()

    def test_standalone_and_fixture(self):
        self.write("t/Log.lean", "import Lib.B\nimport Lean\n")
        self.write("t/Client.lean", "import Lib.A\nimport Fixture.Gen\n")
        self.write("t/NoImports.lean", "def x := 1\n")
        files, errors = self.classify()
        self.assertEqual(files, ["t/Log.lean"])
        self.assertEqual(errors, [])

    def test_missing_library_module_is_an_error_even_for_fixtures(self):
        self.write("t/Log.lean", "import Lib.Gone\n")
        self.write("t/Client.lean", "import Lib.Gone\nimport Fixture.Gen\n")
        files, errors = self.classify()
        self.assertEqual(files, [])
        self.assertEqual(len(errors), 2)
        self.assertTrue(all("Lib.Gone" in e for e in errors))

    def test_key_follows_transitive_library_sources(self):
        self.write("t/Log.lean", "import Lib.B\n")
        toolchain = b"tc"
        before = ld.input_key("t/Log.lean", toolchain, ld.Sources())
        self.assertEqual(before, ld.input_key("t/Log.lean", toolchain, ld.Sources()))
        self.assertEqual(ld.Sources().closure(["Lib.B", "Lean"]), {"Lib.A", "Lib.B"})
        self.write("Lib/A.lean", "def a := 2\n")  # imported by Lib.B, not by the file
        self.assertNotEqual(before, ld.input_key("t/Log.lean", toolchain, ld.Sources()))
        self.assertNotEqual(before, ld.input_key("t/Log.lean", b"other", ld.Sources()))

    def test_pending_until_every_file_passed_with_its_inputs(self):
        self.write("assurance/lean-files.json", '{"reject": []}\n')
        self.write("t/Log.lean", "import Lib.B\n")
        self.classify()
        saved = ld.REGISTRY
        ld.REGISTRY = self.repo / "assurance/lean-files.json"
        self.addCleanup(setattr, ld, "REGISTRY", saved)
        pending = lambda: ld.main(["--pending"])
        with mock.patch.dict(os.environ, {"AIR2LEAN_CAS_DIR": str(self.repo / "cas")}):
            self.assertEqual(pending(), 1)  # never elaborated
            toolchain = (self.repo / "lean-toolchain").read_bytes() + (self.repo / "lakefile.toml").read_bytes()
            store = self.repo / "cas/lean-files"
            store.mkdir(parents=True)
            (store / ld.input_key("t/Log.lean", toolchain, ld.Sources())).touch()  # what --elaborate records
            self.assertEqual(pending(), 0)
            self.write("Lib/A.lean", "def a := 2\n")
            self.assertEqual(pending(), 1)  # a transitive import changed


if __name__ == "__main__":
    unittest.main()
