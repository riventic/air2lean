"""scripts/lean-deps.py --files / --elaborate: which Lean files the full build elaborates.

A tiny repository (one library `Lib` with `Lib/A.lean`) stands in for the real one: a file outside
the library that imports only Lean and `Lib` modules is standalone and elaborated; a file with a
fixture's own import is left to its check; an import of a `Lib` module that does not exist (a
renamed or split module, the break of the strength logs after #342) is an error for every file;
a stale cache entry is never hit (the key covers the transitive library sources).
"""
import importlib.util
import copy
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import types
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

    def test_raw_strings_match_original_source_at_absolute_offsets(self):
        source = ('def value := r\n'
                  'def quoted := r##"raw -- /- text with a quote " inside"##\n'
                  'def after := 0\n')
        with mock.patch.object(ld, 'RAW_STRING', wraps=ld.RAW_STRING) as raw:
            clean = ld.strip_comments(source)
        self.assertEqual([call.args[1] for call in raw.match.call_args_list],
                         [source.index('r\n'), source.index('r##"')])
        self.assertTrue(all(call.args[0] is source for call in raw.match.call_args_list))
        self.assertEqual(len(clean), len(source))
        self.assertNotIn('raw --', clean)
        self.assertIn('def after := 0', clean)

    def test_header_tokens_stop_at_the_first_body_token(self):
        source = 'import Lib.A\ndef body := many body tokens after the header\n'
        tokens_impl, consumed = ld.header_tokens, []

        def observed(text):
            for token in tokens_impl(text):
                consumed.append(token)
                yield token

        with mock.patch.object(ld, 'header_tokens', side_effect=observed):
            self.assertEqual(ld.import_names(source), ['Lib.A'])
        self.assertEqual(consumed, ['import', 'Lib.A', 'def'])

    def test_import_names_validates_only_the_header_not_the_body(self):
        bodies = ('def body := "unterminated',
                  'def msg : String := s!"{r#"a " b"#}"',
                  'def msg : String := s!"{(show Nat from by sorry)}"')
        with mock.patch.object(ld, 'strip_comments', side_effect=AssertionError('body mask used for imports')):
            for body in bodies:
                with self.subTest(body=body):
                    self.assertEqual(ld.import_names('import Lib.A\n' + body), ['Lib.A'])
        # Discovery is not a Lean-validity or placeholder qualification result.
        for header in ('/- unterminated', 'import Lib.A /- nested /- comment -/',
                       'import /- missing module -/', 'public meta import'):
            with self.subTest(header=header), self.assertRaises(ValueError):
                ld.import_names(header)

    def test_unsupported_import_spelling_is_a_clear_error(self):
        for name in ('Lib.«A.B»', '«Lib A»', 'Lib/A', 'Lib.\\A', 'Lib.Α', 'Lib.'):
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


class Controls(unittest.TestCase):
    """Registry and selected-profile checks only; no Lean, resolver or fixture subprocess."""

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        for file in ("scripts/check.sh", "Proofs/Toy/Gen.lean", "controls/A.lean", "controls/B.lean"):
            path = self.root / file
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("import ZigLean\n")
        for file in ("controls/A.lean", "controls/B.lean"):
            (self.root / file).write_text("import ZigLean\n-- expect-error: control mismatch\n"
                                          "theorem probe : False := by trivial\n")
        (self.root / "lakefile.toml").write_text('[[lean_lib]]\nname = "ZigLean"\n')
        (self.root / "lean-toolchain").write_text("fixture-only\n")
        (self.root / "ZigLean.lean").write_text("def toy := 0\n")
        self.normalizer = ld.generated_normalizer()
        self.doc = json.loads((ROOT / "tests/roadmap/profiles/current.json").read_text())
        self.generated = self.root / "fresh.lean"
        metadata = dict(profile=self.normalizer.profile_for_air(self.doc),
                        float_semantics="ieee", correspondence="model")
        self.generated.write_bytes(self.normalizer.PREFIX + json.dumps(metadata).encode() +
                                   b"\nimport ZigLean\n")
        air = self.root / "air"
        air.mkdir()
        (air / "toy.json").write_text(json.dumps(self.doc))
        report = self.root / "fresh.json"
        self.normalizer.write_report(self.generated, air, report)
        self.report = self.root / "selected.json"
        self.normalizer.bind_selection(self.root / "Proofs/Toy/Gen.lean", self.generated, report, self.report)
        self.control = dict(reason="reciprocal ABI control", owner="toy",
                            generated="Proofs/Toy/Gen.lean", outcomes=[
                                {"profile": {"target_triple": "*-linux*-*"}, "expect": "reject"},
                                {"profile": {"target_triple": "*-macos*-*"}, "expect": "check"}])

    def write_registry(self, *, reject=None, contextual=None):
        path = self.root / "assurance/lean-files.json"
        path.parent.mkdir(exist_ok=True)
        owners = {"toy": dict(script="scripts/check.sh", part="test/0.15.2/golden", step="Translate",
                              env={"AIR2LEAN_EXAMPLES": "toy"})} if contextual else {}
        path.write_text(json.dumps(dict(schema_version=2, description="test controls",
                                        owners=owners, reject=reject or {}, contextual=contextual or {})))

    def reciprocal_registry(self):
        reciprocal = copy.deepcopy(self.control)
        for rule in reciprocal["outcomes"]:
            rule["expect"] = "check" if rule["expect"] == "reject" else "reject"
        self.write_registry(contextual={"controls/A.lean": self.control, "controls/B.lean": reciprocal})
        return ld.control_registry(self.root)

    def universe_helper(self):
        with mock.patch("sys.path", [str(ROOT / "scripts"), *sys.path]):
            import theorem_universe
        return theorem_universe

    def fake_lake(self, command, **kwargs):
        if command[:2] == ["lake", "build"]:
            self.assertTrue(kwargs.get("check"))
            return types.SimpleNamespace(returncode=0, stdout="")
        self.assertEqual(command[:3], ["lake", "env", "lean"])
        return types.SimpleNamespace(returncode=1,
            stdout=f"{Path(command[3]).name}:3:1: error: control mismatch\n")

    def fake_audit(self, modules, paths, output, **kwargs):
        output.write_text(json.dumps(dict(status="pass", theorem_count=1, modules=modules,
            theorems=[{"module": modules[0]}], kernel_replay={"status": "pass"})))
        return dict(status="pass", exit_code=0, theorem_count=1, kernel_replay="pass")

    def completion(self):
        registry = self.reciprocal_registry()
        controls = {}
        for file, control in registry["controls"].items():
            outcome, binding = ld.control_outcome(control, report=self.report, selected_root=self.root)
            result = dict(expect=outcome, selection=binding, report=str(self.report), status="pass",
                          source_sha256=ld.hashlib.sha256((self.root / file).read_bytes()).hexdigest())
            if outcome == "check":
                audit = self.root / "audit.json"
                audit.write_text(json.dumps(dict(status="pass", theorem_count=1, modules=["Fixture.Control"],
                    theorems=[{"module": "Fixture.Control"}], kernel_replay={"status": "pass"})))
                result.update(audit=str(audit), audit_sha256=ld.hashlib.sha256(audit.read_bytes()).hexdigest())
            controls[file] = result
        return dict(owner="toy", root=str(self.root.resolve()), registry_sha256=registry["sha256"],
                    status="pass", errors=[], controls=controls)

    def test_contextual_controls_defer_without_reading_or_guessing_a_profile(self):
        self.write_registry(contextual={"controls/A.lean": self.control})
        control = ld.control_registry(self.root)["controls"]["controls/A.lean"]
        with mock.patch.object(self.normalizer, "checked_selection", side_effect=AssertionError("no context read")):
            self.assertEqual(ld.control_outcome(control), ("defer", None))

    def test_reciprocal_outcomes_share_one_actual_selected_context(self):
        controls = self.reciprocal_registry()["controls"]
        first, binding = ld.control_outcome(controls["controls/A.lean"], report=self.report, selected_root=self.root)
        second, other = ld.control_outcome(controls["controls/B.lean"], report=self.report, selected_root=self.root)
        self.assertEqual((first, second), ("reject", "check"))
        self.assertEqual(binding, other)

    def test_context_must_match_the_selected_tree_and_full_source(self):
        with self.assertRaisesRegex(ValueError, "selected-source binding"):
            ld.control_outcome(self.control, report=self.report, selected_root=self.root / "other")
        (self.root / "Proofs/Toy/Gen.lean").write_bytes(self.generated.read_bytes())
        with self.assertRaisesRegex(ValueError, "differs from its check report"):
            ld.control_outcome(self.control, report=self.report, selected_root=self.root)

    def test_unmatched_or_ambiguous_profile_cannot_resolve_an_owner(self):
        for outcomes in ([{"profile": {"target_triple": "*-macos*-*"}, "expect": "check"}],
                         [self.control["outcomes"][0], self.control["outcomes"][0]]):
            control = {**self.control, "outcomes": outcomes}
            with self.assertRaisesRegex(ValueError, "no unique outcome"):
                ld.control_outcome(control, report=self.report, selected_root=self.root)

    def test_registry_missing_owner_control_or_generated_source_is_an_error(self):
        for field, missing in (("owner", "missing"), ("generated", "Proofs/Missing/Gen.lean")):
            self.write_registry(contextual={"controls/A.lean": {**self.control, field: missing}})
            with self.assertRaisesRegex(ValueError, f"missing contextual {field}"):
                ld.control_registry(self.root)
        self.write_registry(reject={"controls/Missing.lean": "stale control"})
        with self.assertRaisesRegex(ValueError, "registered control is missing"):
            ld.control_registry(self.root)

    def test_registry_has_one_identity_and_rejects_unsupported_rules_and_paths(self):
        for change in ({"owner": "../check.sh"}, {"owner": "/tmp/check.sh"},
                       {"outcomes": [{"profile": {"host_guess": "linux"}, "expect": "reject"}]}):
            self.write_registry(contextual={"controls/A.lean": {**self.control, **change}})
            with self.assertRaises(ValueError):
                ld.control_registry(self.root)
        self.write_registry(reject={"controls/A.lean": "unconditional"},
                            contextual={"controls/A.lean": self.control})
        with self.assertRaisesRegex(ValueError, "invalid contextual control"):
            ld.control_registry(self.root)

    def test_completion_requires_all_controls_and_no_deferred_or_foreign_context(self):
        record = self.completion()
        fake = types.SimpleNamespace(staged_module=lambda file: "Fixture.Control")
        with mock.patch.dict(sys.modules, theorem_universe=fake):
            self.assertEqual(ld.control_completion(record, "toy", root=self.root), record)
            for change in (lambda r: r["controls"].pop("controls/B.lean"),
                           lambda r: r.update(owner="other"), lambda r: r.update(root="/another/tree"),
                           lambda r: r.update(registry_sha256="old"),
                           lambda r: r["controls"]["controls/A.lean"].update(expect="defer", report=None, selection=None)):
                stale = copy.deepcopy(record)
                change(stale)
                with self.subTest(record=stale), self.assertRaises(ValueError):
                    ld.control_completion(stale, "toy", root=self.root)

    def test_positive_completion_requires_its_own_retained_kernel_audit(self):
        record = self.completion()
        fake = types.SimpleNamespace(staged_module=lambda file: "Fixture.Control")
        audit = Path(record["controls"]["controls/B.lean"]["audit"])
        original = audit.read_text()
        for change in ({"status": "fail"}, {"theorem_count": 0}, {"modules": ["Borrowed.Control"]},
                       {"theorems": [{"module": "Borrowed.Control"}]}, {"kernel_replay": {"status": "fail"}}):
            raw = {**json.loads(original), **change}
            audit.write_text(json.dumps(raw))
            record["controls"]["controls/B.lean"]["audit_sha256"] = ld.hashlib.sha256(audit.read_bytes()).hexdigest()
            with mock.patch.dict(sys.modules, theorem_universe=fake), self.assertRaisesRegex(ValueError, "compiled kernel audit"):
                ld.control_completion(record, "toy", root=self.root)

    def test_completion_invalidates_when_control_or_selected_source_changes(self):
        record = self.completion()
        (self.root / "controls/A.lean").write_text("changed control\n")
        with self.assertRaisesRegex(ValueError, "changed contextual control"):
            ld.control_completion(record, "toy", root=self.root)

    def test_owner_refuses_missing_context_before_any_build_dispatch(self):
        self.reciprocal_registry()
        fake = types.SimpleNamespace(staged_module=lambda file: "Fixture.Control")
        with mock.patch.object(ld, "ROOT", self.root), mock.patch.dict(sys.modules, theorem_universe=fake), \
                mock.patch.object(ld.subprocess, "run", side_effect=AssertionError("no build without context")):
            with self.assertRaisesRegex(ValueError, "missing selected producer reports"):
                ld.check_owned_controls("toy", {}, self.root / "result.json")

    def test_standalone_defers_both_controls_without_pass_markers_or_execution(self):
        self.reciprocal_registry()
        fake = types.SimpleNamespace(run=mock.Mock(side_effect=AssertionError("deferred controls must not run")))
        stdout = io.StringIO()
        with mock.patch.object(ld, "ROOT", self.root), \
                mock.patch.object(ld, "classify", return_value=(["controls/A.lean", "controls/B.lean"], [])), \
                mock.patch.dict(sys.modules, par=fake), mock.patch("sys.stdout", stdout):
            self.assertEqual(ld.elaborate(None, 3000), 0)
        self.assertIn("DEFER controls/A.lean", stdout.getvalue())
        self.assertIn("DEFER controls/B.lean", stdout.getvalue())
        self.assertIn("NOT QUALIFIED", stdout.getvalue())
        self.assertFalse((self.root / ".lake/lean-files").exists())
        fake.run.assert_not_called()

    def test_owner_builds_imports_and_routes_positive_and_negative_controls(self):
        self.reciprocal_registry()
        universe = self.universe_helper()
        with mock.patch.object(ld, "ROOT", self.root), mock.patch.object(universe, "ROOT", self.root), \
                mock.patch.object(universe, "compile_unit", return_value=None) as compile_unit, \
                mock.patch.object(universe, "audit_modules", side_effect=self.fake_audit) as audit_modules, \
                mock.patch.object(ld.subprocess, "run", side_effect=self.fake_lake) as execute:
            result = self.root / "result.json"
            self.assertEqual(ld.check_owned_controls("toy", {"Proofs/Toy/Gen.lean": self.report}, result), [])
            self.assertEqual(execute.call_args_list[0].args[0], ["lake", "build", "ZigLean"])
            self.assertEqual(execute.call_args_list[1].args[0], ["lake", "env", "lean", "controls/A.lean"])
            compile_unit.assert_called_once()
            audit_modules.assert_called_once()
            self.assertEqual(Path(compile_unit.call_args.args[0]).read_bytes(),
                             (self.root / "controls/B.lean").read_bytes())
            self.assertEqual(json.loads(audit_modules.call_args.kwargs["sources"].read_text()),
                             {universe.staged_module("controls/B.lean"): "controls/B.lean"})
            self.assertEqual(ld.control_completion(json.loads(result.read_text()), "toy", root=self.root)["status"], "pass")

    def test_positive_control_reuses_shared_shadow_refusal_before_compile_or_audit(self):
        self.reciprocal_registry()
        universe = self.universe_helper()
        shadow = self.root / ".lake/build/lib/lean/Universe.olean"
        shadow.parent.mkdir(parents=True)
        shadow.write_bytes(b"old shadow artifact; not a real olean")
        with mock.patch.object(ld, "ROOT", self.root), mock.patch.object(universe, "ROOT", self.root), \
                mock.patch.object(universe, "compile_unit", side_effect=AssertionError("shadow must block compile")) as compile_unit, \
                mock.patch.object(universe, "audit_modules", side_effect=AssertionError("shadow must block audit")) as audit, \
                mock.patch.object(ld.subprocess, "run", side_effect=self.fake_lake):
            with self.assertRaisesRegex(ValueError, "would shadow theorem-universe modules"):
                ld.check_owned_controls("toy", {"Proofs/Toy/Gen.lean": self.report}, self.root / "result.json")
            compile_unit.assert_not_called()
            audit.assert_not_called()

    def test_exact_rejection_anchor_refuses_a_later_unrelated_error(self):
        source = "-- expect-error: Application type mismatch\ntheorem valid : True := True.intro\n#check Nat.succ True.intro\n"
        self.assertIsNotNone(ld.rejection_error("Control.lean", source, 1,
            "Control.lean:3:1: error: Application type mismatch\n"))
        self.assertIsNone(ld.rejection_error("Control.lean", source, 1,
            "Control.lean:2:1: error: Application type mismatch\n"))
        self.assertIsNotNone(ld.rejection_error("Control.lean", source, 0,
            "Control.lean:2:1: error: Application type mismatch\n"))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            ld.expected_error(source + "-- expect-error: later\n#check 1\n")
        with self.assertRaisesRegex(ValueError, "immediately precede"):
            ld.expected_error("-- expect-error: missing\n\ntheorem valid : True := True.intro\n")

    def test_rejection_control_keeps_the_existing_theorem_presence_guard(self):
        source = "-- expect-error: Application type mismatch\n#check Nat.succ True.intro\n"
        self.assertIn("no theorem to reject", ld.rejection_error("Control.lean", source, 1,
            "Control.lean:2:1: error: Application type mismatch\n"))

    def test_rejection_anchor_cannot_credit_a_helper_before_the_final_theorem(self):
        source = ("-- expect-error: Type mismatch\ndef broken : Nat := True.intro\n"
                  "theorem valid : True := True.intro\n")
        self.assertIn("precedes its final theorem", ld.rejection_error("Control.lean", source, 1,
            "Control.lean:2:1: error: Type mismatch\n"))

    def test_positive_control_reports_preserve_long_encoded_module_components(self):
        registry = self.reciprocal_registry()
        control = registry["controls"]["controls/B.lean"]
        file = "tutorials/" + "a" * 101 + "/A.lean"
        path = self.root / file
        path.parent.mkdir(parents=True)
        path.write_bytes((self.root / "controls/B.lean").read_bytes())
        self.write_registry(contextual={"controls/A.lean": self.control, file: control})
        universe = self.universe_helper()
        with mock.patch.object(ld, "ROOT", self.root), mock.patch.object(universe, "ROOT", self.root), \
                mock.patch.object(universe, "compile_unit", return_value=None), \
                mock.patch.object(universe, "audit_modules", side_effect=self.fake_audit), \
                mock.patch.object(ld.subprocess, "run", side_effect=self.fake_lake):
            result = self.root / "long-result.json"
            self.assertEqual(ld.check_owned_controls("toy", {"Proofs/Toy/Gen.lean": self.report}, result), [])
        report = Path(json.loads(result.read_text())["controls"][file]["audit"])
        self.assertTrue(report.is_file())
        self.assertTrue(all(len(part.encode()) <= 255 for part in report.parts))


class OwnerDiscovery(unittest.TestCase):
    """CI descriptor/key/cache units; all tool resolution and execution is absent or mocked."""

    def setUp(self):
        spec = importlib.util.spec_from_file_location("fixture_checks_unit", ROOT / "scripts/fixture-checks.py")
        self.fc = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.fc)
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.owner = dict(script="scripts/check.sh", part="test/0.15.2/golden", step="Translate",
                          env={"AIR2LEAN_EXAMPLES": "toy", "AIR2LEAN_DIFF": "0"})
        self.row = dict(zig="0.15.2", part="golden", mutate=False)
        self.step = dict(name="Translate", run="scripts/check.sh", env={
            "AIR2LEAN_ZIG_VERSION": "${{ matrix.zig }}",
            "AIR2LEAN_ZIG_AIR": "${{ github.workspace }}/zig-air-${{ matrix.zig }}/bin/zig"})
        self.workflow = dict(jobs={"test": {"runs-on": "ubuntu-24.04", "strategy": {"matrix": {"include": [self.row]}},
                                           "steps": [self.step]}})
        self.tree = types.SimpleNamespace(files=[], under=lambda path: [])

    def discover(self):
        with mock.patch.object(self.fc, "ROOT", self.root), \
                mock.patch.object(self.fc.CR, "load_workflow", return_value=self.workflow), \
                mock.patch.object(self.fc.DEPS, "control_registry", return_value={"owners": {"toy": self.owner}}):
            return self.fc.discover(self.tree)

    def test_owner_reuses_one_exact_recipe_with_fingerprinted_selection(self):
        units = self.discover()
        self.assertEqual(len(units), 1)
        unit = units[0]
        self.assertEqual(unit["owner"], "toy")
        self.assertEqual(unit["rows"], ["test/0.15.2/golden"])
        self.assertEqual(unit["run"], "scripts/check.sh")
        self.assertEqual(unit["env"]["AIR2LEAN_EXAMPLES"], "toy")
        self.assertEqual(unit["env"]["AIR2LEAN_ZIG_VERSION"], "0.15.2")
        self.assertEqual(unit["toolchains"], {"patched": ["0.15.2"], "stock": []})

    def test_owner_reference_missing_ambiguous_or_nonproducer_fails(self):
        original = copy.deepcopy(self.workflow)
        for steps in ([], [self.step, copy.deepcopy(self.step)], [{**self.step, "run": "echo scripts/check.sh"}]):
            self.workflow = copy.deepcopy(original)
            self.workflow["jobs"]["test"]["steps"] = steps
            with self.assertRaisesRegex(ValueError, "owner toy"):
                self.discover()

    def test_shared_step_metadata_keeps_owner_and_ordinary_rows_separate(self):
        self.owner["script"] = self.step["run"] = "tests/toy/check.sh"
        with mock.patch.object(self.fc, "is_proof_fixture", return_value=True):
            units = self.discover()
        self.assertEqual(len(units), 2)
        self.assertEqual(units[0]["rows"], units[1]["rows"])
        self.assertIsNot(units[0]["rows"], units[1]["rows"])
        for key in ("job", "zig", "run", "runner", "skipped", "error"):
            self.assertEqual(units[0][key], units[1][key])

    def test_empty_owner_pass_marker_and_incomplete_result_are_not_cache_hits(self):
        marker = self.root / "pass"
        marker.touch()
        unit = {"owner": "toy"}
        with mock.patch.object(self.fc, "ROOT", self.root), \
                mock.patch.object(self.fc.DEPS, "control_completion", side_effect=ValueError("incomplete")) as check:
            self.assertFalse(self.fc.cached_pass(marker, unit))
            check.assert_not_called()
            marker.write_text("{}")
            self.assertFalse(self.fc.cached_pass(marker, unit))
            check.assert_called_once_with({}, "toy", root=self.root)
            self.assertTrue(self.fc.cached_pass(marker, {}))  # Existing noncontextual cache behavior.

    def test_owner_key_reuses_declared_ci_inputs_for_dynamic_zig_reads(self):
        unit = self.discover()[0]
        files = {"scripts/check.sh": "true\n", "examples/toy/toy.zig": "const x = 1;\n",
                 "assurance/lean-files.json": "registry bytes\n", ".github/ci-inputs.json": json.dumps(dict(
                     schema="air2lean-ci-inputs/2", parts={"test/0.15.2/golden": {"inputs": ["examples/**", "scripts/check.sh"]}}))}
        for file, text in files.items():
            path = self.root / file
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        tree = types.SimpleNamespace(files=sorted(files), file_set=set(files),
            dirs={str(Path(f).parent) for f in files}, under=lambda d: [f for f in files if f.startswith(d + "/")],
            digest=lambda f: ld.hashlib.sha256((self.root / f).read_bytes()).hexdigest())
        with mock.patch.object(self.fc, "ROOT", self.root), \
                mock.patch.object(self.fc.CR, "load_workflow", return_value=self.workflow) as workflow, \
                mock.patch.object(self.fc.CR, "load_declarations", wraps=self.fc.CR.load_declarations) as declarations, \
                mock.patch.object(self.fc.DEPS, "lib_roots", return_value={"Lib"}), \
                mock.patch.object(self.fc.Keyer, "tool", return_value="mock tool; never resolved"):
            keyer = self.fc.Keyer(tree)
            self.assertIn("examples/toy/toy.zig", keyer.files(unit))
            first = keyer.key(unit)
            (self.root / "examples/toy/toy.zig").write_text("const x = 2;\n")
            self.assertNotEqual(first, keyer.key(unit))
            workflow.assert_called_once_with(self.root, None)
            declarations.assert_called_once_with(self.root)

    def test_staging_reserves_existing_tool_names_for_the_selected_tools(self):
        unit = self.discover()[0]
        for name in ("zig-air-0.15.2", "host-zig"):
            (self.root / name).mkdir()
        selected = {}
        for kind in ("patched", "stock"):
            selected[kind] = self.root / ("selected-" + kind) / "bin/zig"
            selected[kind].parent.mkdir(parents=True)
            selected[kind].write_text("fixture path only; never executed\n")
        scratch = self.root / "scratch"
        with mock.patch.object(self.fc, "ROOT", self.root), \
                mock.patch.object(self.fc, "resolve", side_effect=lambda kind, version: selected[kind]) as resolve, \
                mock.patch.object(self.fc.platform, "system", return_value="Linux"):
            self.fc._stage(unit, scratch)
        self.assertEqual((scratch / "workspace/zig-air-0.15.2").resolve(), selected["patched"].parent.parent.resolve())
        self.assertEqual((scratch / "workspace/host-zig").resolve(), selected["stock"].parent.resolve())
        self.assertTrue((self.root / "zig-air-0.15.2").is_dir())
        self.assertTrue((self.root / "host-zig").is_dir())
        self.assertEqual(resolve.call_args_list, [mock.call("patched", "0.15.2"), mock.call("stock", "0.15.2")])

    def test_shell_wrapper_forwards_the_final_omitted_owner_status(self):
        scripts, binary = self.root / "scripts", self.root / "bin"
        scripts.mkdir()
        binary.mkdir()
        wrapper = scripts / "fixture-checks.sh"
        wrapper.write_bytes((ROOT / "scripts/fixture-checks.sh").read_bytes())
        python = binary / "python3"
        python.write_text(f"#!{sys.executable}\n" +
            "import pathlib, sys\n"
            "if 'scripts/cas.py' in sys.argv:\n"
            "    log = pathlib.Path(sys.argv[sys.argv.index('--log') + 1])\n"
            "    log.write_text(\"fixture-checks: 0 units passed\\nfixture-checks: NOT QUALIFIED: contextual owners omitted: ['toy']\\n\")\n"
            "else:\n"
            "    print('fixture-checks: NOT QUALIFIED: tool preparation does not check contextual owners')\n")
        python.chmod(0o755)
        env = dict(self.fc.os.environ, PATH=str(binary) + self.fc.os.pathsep + self.fc.os.environ["PATH"])
        result = subprocess.run(["bash", str(wrapper), "--only", "unrelated", "--logs", str(self.root / "logs")],
                                env=env, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("NOT QUALIFIED: contextual owners omitted: ['toy']", result.stdout)

    def test_success_without_owner_completion_does_not_cache_or_qualify(self):
        unit = self.discover()[0]
        stdout, stderr = io.StringIO(), io.StringIO()
        keyer = types.SimpleNamespace(key=lambda unit: "owner-key")
        store = self.root / "store"
        with mock.patch.object(self.fc, "ROOT", self.root), mock.patch.object(self.fc, "Tree", return_value=self.tree), \
                mock.patch.object(self.fc, "discover", return_value=[unit]), \
                mock.patch.object(self.fc, "Keyer", return_value=keyer), \
                mock.patch.object(self.fc, "store_dir", return_value=store), \
                mock.patch.object(self.fc, "stage", return_value=(["mock producer; never executed"], {})), \
                mock.patch.object(self.fc.par, "workers", return_value=1), \
                mock.patch.object(self.fc.par, "run", return_value=[0]) as execute, \
                mock.patch("sys.stdout", stdout), mock.patch("sys.stderr", stderr):
            self.assertEqual(self.fc.main(["--logs", str(self.root / "logs")]), 1)
        self.assertFalse((store / "owner-key").exists())
        self.assertIn("contextual completion", stderr.getvalue())
        jobs = execute.call_args.args[0]
        self.assertEqual(jobs[0].env["AIR2LEAN_CONTROL_OWNER"], "toy")
        self.assertEqual(jobs[0].env["AIR2LEAN_CONTROL_RESULT"], str(store / "owner-key.owner.json"))

    def test_omitted_owner_is_explicitly_not_qualified_without_running_it(self):
        unit = self.discover()[0]
        stdout = io.StringIO()
        with mock.patch.object(self.fc, "ROOT", self.root), mock.patch.object(self.fc, "Tree", return_value=self.tree), \
                mock.patch.object(self.fc, "discover", return_value=[unit]), \
                mock.patch.object(self.fc, "Keyer", return_value=types.SimpleNamespace()), \
                mock.patch.object(self.fc, "store_dir", return_value=self.root / "store"), \
                mock.patch.object(self.fc.par, "run", side_effect=AssertionError("omitted owner must not run")), \
                mock.patch("sys.stdout", stdout):
            self.assertEqual(self.fc.main(["--only", "unrelated-selection"]), 0)
        self.assertIn("NOT QUALIFIED: contextual owners omitted: ['toy']", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
