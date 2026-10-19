#!/usr/bin/env python3
"""Generated-module integrity gate: synthetic fail-closed fixtures and, when the translator is
built, the real repository (every committed generated module is a fresh translation)."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

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
namespace = sys.argv[sys.argv.index('--namespace') + 1] if '--namespace' in sys.argv else ''
output = header + 'import ZigLean\\n' + (f'namespace {namespace}\\n' if namespace else '')
output += ''.join(f"def {d['name'].replace('.', '_')} := 0\\n" for d in sorted(docs, key=lambda d: d['name']))
output += f'end {namespace}\\n' if namespace else ''
if '--canon-certificate' in sys.argv:
    print(json.dumps(dict(kind='canon-debug-native-binding', version=1, functions=len(docs), changed=True)))
else:
    out.write_text(output)
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
        status, _, err = self.fx.run("write")
        self.assertEqual(status, 0, err)
        self.fx.git("add", "-A")

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

    def enroll(self):
        self.fx.write("examples/demo/zig-versions", "0.15.2\n")
        shutil.rmtree(self.fx.root / "tests/golden/0.16.0/demo")
        (self.fx.root / "tests/golden/0.15.2/demo/Gen.lean").unlink()
        # A complete toy export for each host, rather than a legacy mixed-profile overlay.
        for path in (self.fx.root / "tests/golden/demo/air").glob("*.json"):
            doc = json.loads(path.read_text())
            doc.update(schema=12, zig_version="0.15.2", profile={"zig_version": "0.15.2", "target_triple": "x86_64-linux"})
            path.write_text(json.dumps(doc))
            for host, target in (("darwin", "aarch64-macos"), ("linux-aarch64", "aarch64-linux")):
                other = dict(doc, profile=dict(doc["profile"], target_triple=target))
                self.fx.write(f"tests/golden/0.15.2/demo/air-{host}/{path.name}", json.dumps(other))
        self.assertEqual(self.fx.run("write")[0], 0)
        public = (self.fx.root / "Proofs/Demo/Gen.lean").read_bytes()
        self.fx.write("examples/demo/all-cases", "complete golden family\n")
        status, _, err = self.fx.run("write")
        self.assertEqual(status, 0, err)
        self.assertEqual((self.fx.root / "Proofs/Demo/Gen.lean").read_bytes(), public)
        self.fx.git("add", "-A")
        return [case for case in gi.all_cases() if case.namespaced]

    def test_complete_family_outputs_have_disjoint_namespaces_and_duplicate_short_names(self):
        cases = self.enroll()
        self.assertEqual({(c.version, c.host) for c in cases}, {
            ("0.15.2", "linux"), ("0.15.2", "darwin"), ("0.15.2", "linux-aarch64")})
        namespaces = {c.args[c.args.index("--namespace") + 1] for c in cases}
        self.assertEqual(len(namespaces), 3)
        for case in cases:
            text = (self.fx.root / case.path).read_text()
            namespace = case.args[case.args.index("--namespace") + 1]
            self.assertIn(f"namespace {namespace}\n", text)
            self.assertIn("def demo_f := 0\n", text)  # the same short name in every separate API
            self.assertEqual(case.args[case.args.index("--prefix") + 1], "demo.")
        aggregate = (self.fx.root / "Proofs/Demo/Cases.lean").read_text()
        self.assertEqual(sum(line.startswith("import ") for line in aggregate.splitlines()), 3)
        status, out, err = self.fx.run("case-check")
        self.assertEqual(status, 0, err)
        self.assertEqual(out, "Proofs.Demo.Cases\n")

    def test_missing_case_and_aggregate_import_fail_with_case_identity(self):
        case = self.enroll()[0]
        (self.fx.root / case.path).unlink()
        self.assertFails(case.path, "case-coverage")
        self.assertEqual(self.fx.run("write")[0], 0)
        path = self.fx.root / "Proofs/Demo/Cases.lean"
        path.write_text(path.read_text().splitlines()[0] + "\n")
        status, _, err = self.fx.run("case-targets")
        self.assertEqual(status, 1, err)
        self.assertIn("missing or changed complete case imports", err)
        self.assertIn(case.label, err)

    def test_inactive_case_body_and_profile_are_checked_without_a_selector(self):
        case = next(c for c in self.enroll() if c.host == "darwin")
        path = self.fx.root / case.path
        original = path.read_bytes()
        path.write_bytes(original + b"def extra := 1\n")
        self.assertFails(case.label, "case-check")
        path.write_bytes(original.replace(b'"0.15.2"', b'"0.17.0"', 1))
        self.assertFails(case.label, "case-check")
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
            gi.main(["case-check", "--only", "linux"])
        self.assertEqual(error.exception.code, 2)

    def test_deleting_generation_entry_and_its_output_cannot_delete_golden_expectation(self):
        cases = self.enroll()
        omitted = next(case for case in cases if case.host == "darwin")
        remaining = [case for case in cases if case != omitted]
        (self.fx.root / omitted.path).unlink()
        aggregate = self.fx.root / "Proofs/Demo/Cases.lean"
        omitted_import = "import " + omitted.path[:-5].replace("/", ".")
        aggregate.write_text("\n".join(line for line in aggregate.read_text().splitlines()
                                       if line != omitted_import) + "\n")
        # Simulate removal from the producer mapping, without changing the golden universe.
        with mock.patch.object(gi, "namespaced_cases", return_value=remaining):
            status, _, err = self.fx.run("case-coverage")
        self.assertEqual(status, 1, err)
        self.assertIn(omitted.label, err)
        self.assertIn("supported golden case has no namespaced retranslation rule", err)
        self.assertIn("missing or changed complete case imports", err)

    def test_changed_inactive_air_and_new_older_version_cannot_disappear(self):
        self.enroll()
        self.fx.write("tests/golden/0.15.2/demo/air-darwin/demo.new.json", air("demo.new", "0.15.2"))
        self.assertFails("demo 0.15.2 darwin namespaced", "case-check")
        self.fx.write("examples/demo/zig-versions", "0.15.2\n0.14.1\n")
        self.assertFails("demo 0.14.1 linux namespaced", "case-coverage")

    def test_recorded_older_golden_survives_deleted_version_selection(self):
        self.enroll()
        self.fx.write("tests/golden/0.14.1/demo/air-linux/demo.f.json", air("demo.f", "0.14.1"))
        self.assertFails("demo 0.14.1 linux namespaced", "case-coverage")

    def test_inconsistent_case_profile_cannot_downgrade_to_legacy_during_write(self):
        case = next(c for c in self.enroll() if c.host == "darwin")
        path = self.fx.root / case.path
        before = path.read_bytes()
        air_path = self.fx.root / "tests/golden/0.15.2/demo/air-darwin/demo.f.json"
        doc = json.loads(air_path.read_text())
        doc["profile"]["target_triple"] = "x86_64-linux"
        air_path.write_text(json.dumps(doc))
        self.assertFails("legacy downgrade refused", "write")
        self.assertEqual(path.read_bytes(), before)

    def test_selected_write_does_not_rewrite_an_unselected_aggregate(self):
        self.enroll()
        path = self.fx.root / "Proofs/Demo/Cases.lean"
        path.write_text("-- deliberately stale aggregate\n")
        before = path.read_bytes()
        self.assertFails("missing or changed complete case imports", "write", "--only", "unrelated-fixture")
        self.assertEqual(path.read_bytes(), before)

    def test_case_coverage_rejects_an_empty_air_input_set(self):
        self.enroll()
        shutil.rmtree(self.fx.root / "tests/golden/demo/air")
        shutil.rmtree(self.fx.root / "tests/golden/0.15.2/demo")
        self.assertFails("namespaced case or AIR input missing", "case-coverage")

    def test_new_host_and_duplicate_case_identity_fail_closed(self):
        self.enroll()
        self.fx.write("tests/golden/0.15.2/demo/air-freebsd/demo.f.json", air("demo.f", "0.15.2"))
        self.assertFails("demo 0.15.2 freebsd namespaced", "case-coverage")
        self.fx.write("examples/demo/zig-versions", "0.15.2\n0.15.2\n")
        self.assertFails("duplicate namespaced case output", "case-coverage")

    def test_marker_deletion_and_extra_output_are_not_silent_coverage(self):
        self.enroll()
        extra = self.fx.write("Proofs/Demo/Gen/V9_9_9/H_6c696e7578/Gen.lean", "import ZigLean\n")
        self.assertFails("orphan or extra case-family output", "case-coverage")
        extra.unlink()
        (self.fx.root / "examples/demo/all-cases").unlink()
        self.assertFails("orphan or extra case-family output", "case-coverage")

    def test_case_family_namespace_collisions_fail_before_generation(self):
        self.enroll()
        self.fx.write("examples/Demo/Demo.zig", "")
        self.fx.write("examples/Demo/all-cases", "complete family\n")
        # Spell both paths explicitly: a case-insensitive filesystem cannot enumerate both.
        markers = [self.fx.root / f"examples/{name}/all-cases" for name in ("demo", "Demo")]
        with mock.patch.object(Path, "glob", return_value=markers):
            with self.assertRaisesRegex(ValueError, "share namespace Demo"):
                gi.enrolled_families()

    def test_event_base_ratchet_catches_marker_and_output_deletion_across_two_commits(self):
        self.enroll()
        self.fx.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "enroll")
        base = subprocess.check_output(["git", "-C", str(self.fx.root), "rev-parse", "HEAD"], text=True).strip()
        (self.fx.root / "examples/demo/all-cases").unlink()
        # Enumerate files independently after marker removal, just as a real withdrawal can.
        for path in (self.fx.root / "Proofs/Demo/Gen").rglob("*.lean"):
            path.unlink()
        (self.fx.root / "Proofs/Demo/Cases.lean").unlink()
        self.fx.git("add", "-A")
        self.fx.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "withdraw")
        self.fx.write("note.txt", "second commit\n")
        self.fx.git("add", "-A")
        self.fx.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "prose")
        self.assertEqual(self.fx.run("case-coverage")[0], 0)  # M/O alone cannot remember the old family.
        self.assertFails("supported case family withdrawn", "enrollment", "--base", base)
        with mock.patch.dict(os.environ, GITHUB_ACTIONS="true", AIR2LEAN_CASE_BASE=""):
            self.assertFails("authenticated pre-update", "enrollment")
        self.assertFails("authenticated pre-update", "enrollment", "--base", "0" * 40)
        self.assertFails("is unavailable", "enrollment", "--base", "1" * 40)
        head = subprocess.check_output(["git", "-C", str(self.fx.root), "rev-parse", "HEAD"], text=True).strip()
        self.assertEqual(self.fx.run("enrollment", "--base", head)[0], 0)  # no transition at HEAD

    def test_local_default_main_baseline_and_ci_missing_base_are_distinct(self):
        self.enroll()
        self.fx.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "enroll")
        head = subprocess.check_output(["git", "-C", str(self.fx.root), "rev-parse", "HEAD"], text=True).strip()
        self.fx.git("update-ref", "refs/remotes/origin/main", head)
        with mock.patch.dict(os.environ, GITHUB_ACTIONS="", clear=False):
            os.environ.pop("AIR2LEAN_CASE_BASE", None)
            self.assertEqual(self.fx.run("enrollment")[0], 0)
            (self.fx.root / "examples/demo/all-cases").unlink()
            self.assertFails("supported case family withdrawn", "enrollment")
            self.fx.git("update-ref", "-d", "refs/remotes/origin/main")
            self.assertFails("origin/main is unavailable", "enrollment")
        with mock.patch.dict(os.environ, GITHUB_ACTIONS="true", AIR2LEAN_CASE_BASE=""):
            self.assertFails("authenticated pre-update", "enrollment")

    def test_baseline_retains_withdrawn_host_and_version_even_when_all_outputs_are_removed(self):
        cases = self.enroll()
        for path in (self.fx.root / "tests/golden/demo/air").glob("*.json"):
            doc = json.loads(path.read_text())
            for host, target in (("linux", "x86_64-linux"), ("darwin", "aarch64-macos")):
                other = dict(doc, zig_version="0.14.1", profile={"zig_version": "0.14.1", "target_triple": target})
                self.fx.write(f"tests/golden/0.14.1/demo/air-{host}/{path.name}", json.dumps(other))
        self.fx.write("tests/golden/0.15.2/demo/Gen-darwin.lean", "import ZigLean\n")
        self.fx.write("tests/golden/0.14.1/demo/Gen-darwin.lean", "import ZigLean\n")
        self.assertEqual(self.fx.run("write")[0], 0)
        self.fx.git("add", "-A")
        self.fx.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "cases")
        base = subprocess.check_output(["git", "-C", str(self.fx.root), "rev-parse", "HEAD"], text=True).strip()
        darwin = next(c for c in cases if c.host == "darwin")
        shutil.rmtree(self.fx.root / "tests/golden/0.15.2/demo/air-darwin")
        (self.fx.root / "tests/golden/0.15.2/demo/Gen-darwin.lean").unlink()
        (self.fx.root / darwin.path).unlink()
        shutil.rmtree(self.fx.root / "tests/golden/0.14.1")
        for case in gi.all_cases():
            # Removed version's outputs are found independently from the now-reduced mapping.
            self.assertNotEqual(case.version, "0.14.1")
        for path in (self.fx.root / "Proofs/Demo/Gen/V0_14_1").rglob("*.lean"):
            path.unlink()
        current = gi.all_cases()
        for rel, content in gi.case_aggregates(c.path for c in current if c.namespaced).items():
            self.fx.write(rel, content.decode())
        self.assertEqual(self.fx.run("case-coverage")[0], 0)  # current-only coverage cannot remember deletion
        status, _, err = self.fx.run("enrollment", "--base", base)
        self.assertEqual(status, 1, err)
        self.assertIn("demo 0.15.2 darwin: supported golden case withdrawn", err)
        self.assertIn("demo 0.14.1 darwin: supported golden case withdrawn", err)
        self.assertIn("demo 0.14.1 linux: supported golden case withdrawn", err)

    def test_baseline_retains_an_air_only_host_with_git_quoted_unicode_filenames(self):
        cases = self.enroll()
        self.fx.git("config", "core.quotePath", "true")
        directory = self.fx.root / "tests/golden/0.15.2/demo/air-darwin"
        for path in directory.glob("*.json"):
            path.rename(path.with_name("é-" + path.name))
        self.assertFalse((directory.parent / "Gen-darwin.lean").exists())
        self.fx.git("add", "-A")
        self.fx.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "unicode host")
        base = subprocess.check_output(["git", "-C", str(self.fx.root), "rev-parse", "HEAD"], text=True).strip()
        shutil.rmtree(directory)
        (self.fx.root / next(c.path for c in cases if c.host == "darwin")).unlink()
        for rel, content in gi.case_aggregates(c.path for c in gi.all_cases() if c.namespaced).items():
            self.fx.write(rel, content.decode())
        self.assertEqual(self.fx.run("case-coverage")[0], 0)
        self.assertFails("demo 0.15.2 darwin: supported golden case withdrawn", "enrollment", "--base", base)

    def test_hand_added_definition_fails(self):
        path = self.fx.root / "Proofs/Demo/Gen.lean"
        path.write_text(path.read_text() + "def handWritten := 1\n")
        self.assertFails("Proofs/Demo/Gen.lean [demo 0.16.0 linux]: not the fresh translation")

    def test_absent_translator_certificate_fails_closed(self):
        self.fx.translator.write_text(self.fx.translator.read_text().replace(
            "if '--canon-certificate' in sys.argv:", "if False:"))
        self.assertFails("translator did not emit native canonicalization binding evidence", "certify")

    def test_certificate_stdout_keeps_original_arguments_and_program(self):
        case = gi.all_cases()[0]
        # A future option accepted by the translator needs no Python option-grammar update.
        case.args += ["--future-semantic-option", "--timing-json"]
        work = Path(self.temp.name) / "translation"
        work.mkdir()
        translator = gi.Translator(str(self.fx.translator), work)
        program = translator.output(0, case)
        arguments = translator.arguments[0].copy()
        with mock.patch.object(gi.subprocess, "run", wraps=subprocess.run) as run:
            certificate = translator.certificate(0, case)
        self.assertEqual(run.call_args.args[0], [str(self.fx.translator), *arguments, "--canon-certificate"])
        self.assertEqual(translator.arguments[0], arguments)
        self.assertEqual((work / "Gen0.lean").read_bytes(), program)
        self.assertEqual(json.loads(certificate), dict(kind='canon-debug-native-binding', version=1,
                                                    functions=2, changed=True))

    def test_shared_module_certification_requires_every_case(self):
        path = "Proofs/Demo/Gen.lean"
        self.fx.write("tests/roadmap/shared/air/demo.f.json", air("demo.f"))
        self.fx.write("tests/roadmap/shared/air/math.sub__anon_12.json", air("math.sub__anon_12"))
        gi.FIXTURES = [(path, "tests/roadmap/shared/air", ["--namespace", "Demo"], "body")]
        self.assertEqual(self.fx.run("write")[0], 0)
        self.fx.git("add", "-A")
        expected = [(index, case.label) for index, case in enumerate(gi.all_cases())]
        with mock.patch.object(gi.canon_certification, "certify") as certify:
            status, _, err = self.fx.run("certify")
        self.assertEqual(status, 0, err)
        self.assertEqual([(index, case.label) for index, case in certify.call_args.args[1]], expected)
        self.assertEqual(sum(case.path == path for _, case in certify.call_args.args[1]), 2)

    def test_invalid_certificate_propagates_from_certifier(self):
        with mock.patch.object(gi.canon_certification, "certify", side_effect=ValueError("bad actual proof")):
            self.assertFails("bad actual proof", "certify")

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
        self.assertEqual(self.fx.run("write")[0], 0)
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
