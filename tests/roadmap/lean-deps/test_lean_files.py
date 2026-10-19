"""scripts/lean-deps.py --files / --elaborate: which Lean files the full build elaborates.

A tiny repository (one library `Lib` with `Lib/A.lean`) stands in for the real one: a file outside
the library that imports only Lean and `Lib` modules is standalone and elaborated; a file with a
fixture's own import is left to its check; an import of a `Lib` module that does not exist (a
renamed or split module, the break of the strength logs after #342) is an error for every file;
a stale cache entry is never hit (the key covers the transitive library sources).
"""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

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
        before = ld.input_key("t/Log.lean", toolchain, {})
        self.assertEqual(before, ld.input_key("t/Log.lean", toolchain, {}))
        self.write("Lib/A.lean", "def a := 2\n")  # imported by Lib.B, not by the file
        self.assertNotEqual(before, ld.input_key("t/Log.lean", toolchain, {}))
        self.assertNotEqual(before, ld.input_key("t/Log.lean", b"other", {}))

    def test_library_inventory_includes_roots_and_unimported_helpers(self):
        self.write('Lib.lean', 'import Lib.A\n')
        self.write('Lib/ExtractorOnly.lean', 'def state := 1\n')
        expected = {self.repo / p for p in ('Lib.lean', 'Lib/A.lean', 'Lib/B.lean', 'Lib/ExtractorOnly.lean')}
        self.assertEqual(set(ld.library_sources()), expected)
        self.assertEqual(set(ld.library_sources(self.repo)), expected)
        self.write('lakefile.toml', '[[lean_lib]]\nname = "OtherTarget"\nroots = ["Lib.B"]\n')
        self.assertEqual(set(ld.library_sources()), expected)
        self.write('Other/ExtractorOnly.lean', 'def state := 1\n')
        self.write('lakefile.toml', '[[lean_lib]]\nname = "OtherTarget"\nroots = ["Lib.B"]\nglobs = ["Other.+"]\n')
        self.assertEqual(set(ld.library_sources()), expected | {self.repo / 'Other/ExtractorOnly.lean'})
        self.write('lakefile.toml', '[[lean_lib]]\nname = "Missing"\n')
        with self.assertRaisesRegex(ValueError, 'Missing.*no Lean sources'):
            ld.library_sources()

    def test_source_inventory_rejects_directory_aliases_and_decoy_srcdir(self):
        self.write('external/Helper.lean', 'def state := 1\n')
        alias = self.repo / 'Lib/alias'
        for target in (self.repo / 'external', self.repo / 'missing', self.repo / 'Lib', alias):
            alias.symlink_to(target, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, 'source directory alias or broken link'):
                ld.library_sources()
            alias.unlink()
        (self.repo / 'Lib').rename(self.repo / 'original')
        (self.repo / 'Lib').symlink_to(self.repo / 'original', target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'source directory alias or broken link'):
            ld.library_sources()
        (self.repo / 'Lib').unlink()
        (self.repo / 'original').rename(self.repo / 'Lib')
        (self.repo / 'Lib/Helper.lean').symlink_to(self.repo / 'external/Helper.lean')
        self.assertIn(self.repo / 'Lib/Helper.lean', ld.library_sources())
        for config in ('srcDir = "external"\n[[lean_lib]]\nname = "Lib"\n',
                       '[[lean_lib]]\nname = "Lib"\nsrcDir = "external"\n'):
            self.write('lakefile.toml', config)
            with self.assertRaisesRegex(ValueError, 'unsupported Lake srcDir'):
                ld.library_sources()
        self.write('lakefile.toml', '[[lean_lib]]\nname = "OtherTarget"\nroots = ["../Outside"]\n')
        with self.assertRaisesRegex(ValueError, 'invalid configured Lake library root'):
            ld.library_sources()
        self.write('lakefile.toml', '[[lean_lib]]\nname = "Lib"\nglobs = ["*"]\n')
        with self.assertRaisesRegex(ValueError, 'unsupported Lake source glob'):
            ld.library_sources()


if __name__ == "__main__":
    unittest.main()
