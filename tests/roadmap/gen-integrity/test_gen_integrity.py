#!/usr/bin/env python3
"""Generated-module integrity gate: synthetic fail-closed fixtures and, when the translator is
built, the real repository (every committed generated module is a fresh translation)."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location("gen_integrity", ROOT / "scripts/gen-integrity.py")
gi = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gi)

# Stub translator: the output is `def <name> := 0` per AIR function, in name order, after a
# profile record whose zig_version is the input's; it prints errors as the real one does.
STUB = """\
import json, sys
from pathlib import Path
air, out = Path(sys.argv[1]), Path(sys.argv[3])
docs = [json.loads(p.read_text()) for p in sorted(air.glob('*.json'))]
if len({d['zig_version'] for d in docs}) > 1:
    sys.exit("mixed AIR profiles: field 'zig_version' differs")
header = '-- air2lean-profile: {}\\n'.format(json.dumps(dict(stub=docs[0]['zig_version']))) if docs else ''
out.write_text(header + 'import ZigLean\\n' + ''.join(f"def {d['name'].replace('.', '_')} := 0\\n" for d in sorted(docs, key=lambda d: d['name'])))
"""


def air(name, version="0.16.0", schema=11):
    return json.dumps(dict(schema=schema, zig_version=version, name=name, body=[]))


class Fixture:
    def __init__(self, base):
        self.root = base / "repo"
        self.translator = base / "air2lean"
        self.translator.write_text(f"#!{sys.executable}\n{STUB}")
        self.translator.chmod(0o755)
        self.files = {
            "compatibility.json": json.dumps({"zig": {"versions": [{"version": "0.16.0"}, {"version": "0.15.2"}]}}),
            "examples/demo/demo.zig": "",
            "tests/golden/demo/air/demo.f.json": air("demo.f", "0.15.2"),
            "tests/golden/demo/air/math.sub__anon_7.json": air("math.sub__anon_7"),
            "tests/golden/demo/air/math.sub__anon_9.json": air("math.sub__anon_9"),
            "tests/golden/0.16.0/demo/air-linux/math.sub__anon_12.json": air("math.sub__anon_12"),
            "Proofs/Demo/Gen.lean": "import ZigLean\ndef demo_f := 0\ndef math_sub__anon_12 := 0\n",
            "tests/golden/0.15.2/demo/Gen.lean":
                "import ZigLean\ndef demo_f := 0\ndef math_sub__anon_7 := 0\ndef math_sub__anon_9 := 0\n",
        }
        for rel, text in self.files.items():
            self.write(rel, text)
        self.git("init", "-q")
        self.git("add", "-A")

    def write(self, rel, text):
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def git(self, *args):
        subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True)

    def run(self, *argv):
        err, out = io.StringIO(), io.StringIO()
        with contextlib.redirect_stderr(err), contextlib.redirect_stdout(out):
            status = gi.main([*argv, "--translator", str(self.translator)] if argv[0] != "list" else list(argv))
        return status, out.getvalue(), err.getvalue()


class SyntheticTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.fx = Fixture(Path(self.temp.name))
        self.saved = gi.ROOT, gi.FIXTURES, gi.EXCEPTIONS
        gi.ROOT, gi.FIXTURES, gi.EXCEPTIONS = self.fx.root, [], {}

    def tearDown(self):
        gi.ROOT, gi.FIXTURES, gi.EXCEPTIONS = self.saved
        self.temp.cleanup()

    def assertFails(self, fragment, *argv):
        status, _, err = self.fx.run(*(argv or ("check",)))
        self.assertEqual(status, 1, err)
        self.assertIn(fragment, err)

    def test_overlays_replace_every_instance_and_pass(self):
        status, _, err = self.fx.run("check")
        self.assertEqual(status, 0, err)
        self.assertIn("ok demo 0.16.0 linux: Proofs/Demo/Gen.lean", err)
        self.assertIn("ok demo 0.15.2 linux: tests/golden/0.15.2/demo/Gen.lean", err)

    def test_hand_added_definition_fails(self):
        path = self.fx.root / "Proofs/Demo/Gen.lean"
        path.write_text(path.read_text() + "def handWritten := 1\n")
        self.assertFails("Proofs/Demo/Gen.lean [demo 0.16.0 linux]: not the fresh translation")

    def test_missing_overlay_input_fails(self):
        (self.fx.root / "tests/golden/0.16.0/demo/air-linux/math.sub__anon_12.json").unlink()
        self.assertFails("Proofs/Demo/Gen.lean [demo 0.16.0 linux]: not the fresh translation")

    def test_uncovered_generated_module_fails(self):
        self.fx.write("tests/roadmap/x/X/Gen.lean", "import ZigLean\n")
        self.fx.git("add", "-A")
        self.assertFails("tests/roadmap/x/X/Gen.lean: tracked generated module with no retranslation rule")

    def test_profile_record_marks_a_generated_module(self):
        self.fx.write("tests/roadmap/x/Other.lean", '-- air2lean-profile: {}\nimport ZigLean\n')
        self.fx.git("add", "-A")
        self.assertFails("tests/roadmap/x/Other.lean: tracked generated module with no retranslation rule")

    def test_malformed_profile_record_is_not_ignored(self):
        path = self.fx.root / "Proofs/Demo/Gen.lean"
        path.write_text('-- air2lean-profile: {"bogus": 1}\n' + path.read_text())
        self.assertFails("unsupported generated profile record")

    def test_exact_fixture_compares_the_profile_record(self):
        self.fx.write("tests/roadmap/x/air/x.f.json", air("x.f"))
        self.fx.write("tests/roadmap/x/X/Gen.lean", "import ZigLean\ndef x_f := 0\n")
        self.fx.git("add", "-A")
        gi.FIXTURES = [("tests/roadmap/x/X/Gen.lean", "tests/roadmap/x/air", [], "exact")]
        self.assertFails("tests/roadmap/x/X/Gen.lean [tests/roadmap/x/X/Gen.lean]: not the fresh translation")
        gi.FIXTURES = [("tests/roadmap/x/X/Gen.lean", "tests/roadmap/x/air", [], "body")]
        self.assertEqual(self.fx.run("check")[0], 0)

    def test_exception_needs_its_file_and_no_importer(self):
        gi.EXCEPTIONS = {"tests/roadmap/x/old/X/Gen.lean": "historical"}
        self.assertFails("listed exception no longer exists")
        self.fx.write("tests/roadmap/x/old/X/Gen.lean", "import ZigLean\n")
        self.fx.write("tests/roadmap/x/old/X/Proofs.lean", "import ZigLean\nimport X.Gen\n")
        self.fx.git("add", "-A")
        self.assertFails("tests/roadmap/x/old/X/Proofs.lean: imports the non-generated exception")
        (self.fx.root / "tests/roadmap/x/old/X/Proofs.lean").unlink()
        self.fx.git("add", "-A")
        self.assertEqual(self.fx.run("check")[0], 0)

    def test_attest_accepts_only_the_files_own_translation(self):
        status, out, err = self.fx.run("attest", "Proofs/Demo/Gen.lean")
        self.assertEqual(status, 0, err)
        record, = json.loads(out)["files"]
        self.assertEqual(record["fresh_translation_of"], ["demo 0.16.0 linux"])
        # Verification never swaps another version's translation in: that is not this file's.
        (self.fx.root / "Proofs/Demo/Gen.lean").write_text(
            (self.fx.root / "tests/golden/0.15.2/demo/Gen.lean").read_text())
        self.assertFails("Proofs/Demo/Gen.lean: not a fresh translation", "attest")
        (self.fx.root / "Proofs/Demo/Gen.lean").write_text("import ZigLean\ndef handWritten := 1\n")
        self.assertFails("Proofs/Demo/Gen.lean: not a fresh translation", "attest")


@unittest.skipUnless(os.access(ROOT / ".lake/build/bin/air2lean", os.X_OK), "translator not built")
class RepositoryTests(unittest.TestCase):
    def test_every_committed_generated_module_is_fresh(self):
        result = subprocess.run([sys.executable, "-B", str(ROOT / "scripts/gen-integrity.py"), "check"],
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
