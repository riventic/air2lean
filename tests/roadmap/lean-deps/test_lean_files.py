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

    def test_pinned_header_grammar_and_comment_noise(self):
        source = ('/- import Lib.Missing /- nested -/ -/\nmodule prelude\n'
                  'public /- note -/ meta import\nLib.A import all Lib.B\n'
                  '-- import Lib.MissingAgain\n'
                  'def text := r##"\nimport Lib.StringNoise\n"##\n')
        self.write('t/Log.lean', source)
        self.assertEqual(ld.import_names(source), ['Lib.A', 'Lib.B'])
        self.assertEqual(ld.imports(self.repo / 't/Log.lean'), {'Lib.A', 'Lib.B'})
        self.assertEqual(self.classify(), (['t/Log.lean'], []))
        self.assertEqual(ld.import_names('import Lib.A Lib.NotAnotherImport\n'), ['Lib.A'])

    def test_shared_mask_preserves_positions_and_literal_boundaries(self):
        source = ('/- outer\n /- import Lib.Fake -/ -/\n'
                  'def x := "escaped \\\" -- /- text"\n'
                  'def y := r###"raw \\"\nimport Lib.Fake\n"###\n'
                  "def c := '\\u0022'\n"
                  'def «name--with-comment-symbols» := 0\n')
        clean = ld.strip_comments(source)
        self.assertEqual(len(clean), len(source))
        self.assertEqual([i for i, c in enumerate(clean) if c == '\n'],
                         [i for i, c in enumerate(source) if c == '\n'])
        self.assertNotIn('Lib.Fake', clean)
        self.assertIn('«name--with-comment-symbols»', clean)
        for source in ('/- unterminated', 'def x := "unterminated', 'def x := r##"unterminated'):
            with self.subTest(source=source), self.assertRaisesRegex(ValueError, 'unterminated'):
                ld.strip_comments(source)

    def test_unsupported_import_spelling_is_a_clear_error(self):
        for name in ('Lib.«A.B»', 'Lib/A', 'Lib.\\A', 'Lib.Α', 'Lib.'):
            self.write('t/Unsupported.lean', f'import {name}\n')
            with self.subTest(name=name):
                with self.assertRaisesRegex(ValueError, 'Unsupported.lean: Lean import: unsupported module spelling'):
                    ld.imports(self.repo / 't/Unsupported.lean')
                with self.assertRaisesRegex(ValueError, 'unsupported module spelling'):
                    ld.repo_modules([self.repo / 't/Unsupported.lean'])
                with self.assertRaisesRegex(ValueError, 'unsupported module spelling'):
                    self.classify()

    def test_key_follows_modified_imports_and_ignores_comment_imports(self):
        self.write('t/Log.lean', 'module\npublic meta import Lib.B\n')
        self.write('Lib/B.lean', 'module\n/- import Lib.Missing -/\nimport all Lib.A\ndef b := a\n')
        key = ld.input_key('t/Log.lean', b'tc', {})
        self.write('Lib/A.lean', 'def a := 3\n')
        self.assertNotEqual(key, ld.input_key('t/Log.lean', b'tc', {}))


if __name__ == "__main__":
    unittest.main()
