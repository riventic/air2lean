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

    def test_source_roots_include_explicit_roots_and_glob_prefixes(self):
        self.assertEqual(ld.lib_roots(), {'Lib'})
        self.assertEqual(ld.lib_roots(self.repo, strict_sources=True), {'Lib'})
        self.write('lakefile.toml', '[[lean_lib]]\nname = "OtherTarget"\nroots = ["Lib.B"]\n')
        self.assertEqual(ld.lib_roots(strict_sources=True), {'Lib'})
        self.write('lakefile.toml', '[[lean_lib]]\nname = "OtherTarget"\nroots = ["Lib.B"]\nglobs = ["Other.+"]\n')
        self.assertEqual(ld.lib_roots(strict_sources=True), {'Lib', 'Other'})

    def test_source_roots_reject_decoy_srcdir_and_unbounded_globs(self):
        self.write('external/Lib/A.lean', 'def state := 1\n')
        for config in ('srcDir = "external"\n[[lean_lib]]\nname = "Lib"\n',
                       '[[lean_lib]]\nname = "Lib"\nsrcDir = "external"\n'):
            self.write('lakefile.toml', config)
            with self.assertRaisesRegex(ValueError, 'unsupported Lake srcDir'):
                ld.lib_roots(strict_sources=True)
        self.write('lakefile.toml', '[[lean_lib]]\nname = "Lib"\nglobs = ["*"]\n')
        with self.assertRaisesRegex(ValueError, 'unsupported Lake source glob'):
            ld.lib_roots(strict_sources=True)

    def fake_lake_query(self, targets):
        # Lake's answers in the tiny repo: transitive imports by the file headers, a library's
        # modules by its globs (as Lake assigns them when the lakefile is well-formed).
        libs = {lib["name"]: lib.get("globs", []) for lib in
                ld.tomllib.loads((self.repo / "lakefile.toml").read_text())["lean_lib"]}
        out = []
        for t in targets:
            name, facet = t.rsplit(":", 1)
            if facet == "modules":
                out.append(self.owned.get(name, libs[name]))
                continue
            seen, todo = set(), sorted(ld.imports(ld.module_file(name)))
            while todo:
                m = todo.pop()
                if m not in seen and ld.module_file(m).is_file():
                    seen.add(m)
                    todo += sorted(ld.imports(ld.module_file(m)))
            out.append(sorted(seen))
        return out

    def test_precompiled_deps_are_the_import_closure(self):
        # docs/build-cache.md#precompiled-fsym: `<P>Deps` holds what P's modules import.
        self.owned = {}
        saved = ld.lake_query
        ld.lake_query = self.fake_lake_query
        self.addCleanup(setattr, ld, "lake_query", saved)
        self.write("Lib/C.lean", "import Lib.B\ndef c := b\n")
        self.write("lakefile.toml", '[[lean_lib]]\nname = "Lib"\n\n[[lean_lib]]\nname = "P"\n'
                   'roots = ["Lib.C"]\nglobs = ["Lib.C"]\nprecompileModules = true\n\n'
                   '[[lean_lib]]\nname = "PDeps"\nroots = ["Lib.C"]\nglobs = []\n')
        self.assertEqual(ld.precompiled_deps(), {"PDeps": ["Lib.A", "Lib.B"]})
        self.assertEqual(ld.precompiled(write=False), 1)
        self.assertEqual(ld.precompiled(write=True), 0)
        self.assertEqual(ld.precompiled(write=False), 0)
        self.assertIn('name = "PDeps"\nroots = ["Lib.C"]\nglobs = [\n  "Lib.A",\n  "Lib.B",\n]',
                      (self.repo / "lakefile.toml").read_text())
        self.owned = {"PDeps": ["Lib.A"]}  # Lake hands Lib.B to another library (order, overlap)
        self.assertEqual(ld.precompiled(write=False), 1)
        self.owned = {}
        self.write("Lib/B.lean", "def b := 1\n")  # no longer imports Lib.A: the list is stale
        self.assertEqual(ld.precompiled(write=False), 1)
        text = (self.repo / "lakefile.toml").read_text()
        self.write("lakefile.toml", text.replace('[[lean_lib]]\nname = "PDeps"', '[[lean_lib]]\n# x\nname = "PDeps"'))
        with self.assertRaisesRegex(SystemExit, "needs a library PDeps"):
            ld.precompiled(write=True)  # a layout write cannot edit fails, not loops
        self.write("Lib/C.lean", "import Lib.Gone\n")
        self.write("lakefile.toml", '[[lean_lib]]\nname = "P"\nglobs = ["Lib.Gone"]\nprecompileModules = true\n')
        with self.assertRaisesRegex(SystemExit, "must name existing modules"):
            ld.precompiled_deps()


if __name__ == "__main__":
    unittest.main()
