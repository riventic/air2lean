"""Fail-closed scope checks for the actual per-run certificate orchestration."""
import copy
import importlib.util
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location("canon_certification", ROOT / "scripts/canon_certification.py")
cc = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cc)


def record(module="RoundTripBatch0", namespace="Case", count=1, index=0):
    namespace = f"CanonCase{index}.{namespace}"
    return dict(index=index, module=module, namespace=namespace, count=count, changed=True, bytes=0,
                olean=f"/private/tmp/{module}.olean", olean_sha256="fresh-compiled-bytes",
                helpers=[f"{namespace}.shared_layout_0", f"{namespace}.metadata_0"])


def audit(records):
    theorems = [dict(module=r["module"], name=f"{r['namespace']}.{kind}_{index}", allowed=True)
                for r in records for index in range(r["count"])
                for kind in ("erased", "preserves")]
    nodes = [dict(module=r["module"], name=f"{r['namespace']}.{kind}_{index}",
                  dependencies=[r["helpers"][-1]])
             for r in records for index in range(r["count"])
             for kind in ("erased", "preserves")]
    nodes += [dict(module=r["module"], name=name, dependencies=r["helpers"][:index])
              for r in records for index, name in enumerate(r["helpers"])]
    return dict(status="pass", violations=[],
                modules=sorted({"Air2Lean.CanonSem", "Air2Lean.CanonCertificate",
                                *(r["module"] for r in records)}),
                kernel_replay=dict(status="pass", rejected=[], reused=[]),
                freshness=dict(artifacts=list({r["module"]: dict(module=r["module"], olean=r["olean"],
                                               olean_sha256=r["olean_sha256"]) for r in records}.values())),
                theorems=theorems, nodes=nodes)


class SourceTests(unittest.TestCase):
    source = cc.CERTIFICATE_HEADER + "namespace Case\n\nopen Air2Lean\n\ndef snapshots : Array Nat := #[]\n\nend Case\n"

    def test_lean_escapes_preserve_controls_and_literal_backslashes(self):
        self.assertEqual(cc.lean_string("\b\f\0\x1f"), '"\\u0008\\u000c\\u0000\\u001f"')
        self.assertEqual(cc.lean_string('\\b\\f"😀\n\r\t'), '"\\\\b\\\\f\\"😀\\n\\r\\t"')

    def test_roundtrip_uses_lean_escaping_for_directory_and_original_arguments(self):
        directory = '/private/tmp/work\b\f/air0'
        translator = SimpleNamespace(arguments={0: [directory, "--namespace", "Case"]})
        namespace, source = cc.roundtrip_source(self.source, translator, 0)
        quoted = '"/private/tmp/work\\u0008\\u000c/air0"'
        self.assertEqual(namespace, "CanonCase0.Case")
        self.assertIn(f'Air2Lean.parseArgs [{quoted}, "--namespace", "Case"]', source)
        self.assertIn(f"checkDirectory {quoted} args.allocatorModel Case.snapshots", source)

    def test_only_known_emitter_header_and_one_closed_namespace_are_accepted(self):
        translator = SimpleNamespace(arguments={0: ["directory"]})
        for source in (self.source.replace("import Air2Lean.CanonCertificate", "import Other"),
                       self.source.replace("namespace Case", "namespace Case\nnamespace Extra"),
                       self.source.replace("end Case", "end Wrong"),
                       self.source.replace("open Air2Lean", "import Other\nopen Air2Lean")):
            with self.assertRaisesRegex(ValueError, "unexpected emitter header or namespace"):
                cc.roundtrip_source(source, translator, 0)

    def test_native_markers_are_indexed_complete_and_unique(self):
        output = ("canon-snapshot-count:4:2\ncanon-debug-changes:4:false\n"
                  "canon-snapshot-count:9:3\ncanon-debug-changes:9:true\n")
        self.assertEqual(cc.native_results(output, [4, 9]), [{4: "2", 9: "3"}, {4: "false", 9: "true"}])
        for invalid in (output.replace("canon-snapshot-count:9:3\n", ""),
                        output + "canon-debug-changes:4:false\n",
                        output.replace("canon-debug-changes:9:true", "canon-debug-changes:10:true"),
                        output.replace("canon-debug-changes:9:true", "canon-debug-changes:9:maybe")):
            with self.assertRaisesRegex(ValueError, "missing or duplicate indexed"):
                cc.native_results(invalid, [4, 9])

    def test_batch_compiles_once_with_scoped_cases_and_one_import_header(self):
        with tempfile.TemporaryDirectory() as directory:
            translator = SimpleNamespace(work=Path(directory), arguments={4: ["one"], 9: ["two"]})
            batch = [(index, SimpleNamespace(label=str(index)), self.source) for index in (4, 9)]

            def compile(path, compile_module):
                self.assertTrue(compile_module)
                text = path.read_text()
                self.assertEqual(text.count("import Air2Lean.Main\n"), 1)
                self.assertEqual(text.count("import Air2Lean.CanonCertificate\n"), 1)
                for index in (4, 9):
                    self.assertIn(f"namespace CanonCase{index}\n", text)
                    self.assertIn(f"end CanonCase{index}\n", text)
                path.with_suffix(".olean").write_bytes(b"batch artifact")
                return SimpleNamespace(returncode=0, stderr="", stdout=
                    "canon-snapshot-count:4:2\ncanon-debug-changes:4:false\n"
                    "canon-snapshot-count:9:3\ncanon-debug-changes:9:true\n")

            with mock.patch.object(cc, "lean", side_effect=compile) as lean:
                records = cc.compile_batch(batch, translator, 0)
            lean.assert_called_once()
            self.assertEqual([r["namespace"] for r in records], ["CanonCase4.Case", "CanonCase9.Case"])
            self.assertEqual([r["count"] for r in records], [2, 3])
            self.assertEqual([r["changed"] for r in records], [False, True])
            self.assertEqual(len({(r["module"], r["olean"], r["olean_sha256"]) for r in records}), 1)
            self.assertTrue(Path(records[0]["olean"]).is_absolute())
            self.assertTrue(all("seconds" not in r for r in records))

    def test_empty_oversized_and_duplicate_case_batches_do_not_compile(self):
        translator = SimpleNamespace()
        case = SimpleNamespace(label="case")
        for batch in ([], [(index, case, self.source) for index in range(9)],
                      [(0, case, self.source), (0, case, self.source)]):
            with mock.patch.object(cc, "lean") as lean:
                with self.assertRaisesRegex(ValueError, "at most eight distinct cases"):
                    cc.compile_batch(batch, translator, 0)
            lean.assert_not_called()


class ScopeTests(unittest.TestCase):
    def test_missing_second_function_proof_fails(self):
        records = [record(count=2)]
        report = audit(records)
        cc.check_audit(report, records)
        report["theorems"] = [t for t in report["theorems"] if t["name"] != "CanonCase0.Case.preserves_1"]
        with self.assertRaisesRegex(ValueError, "missing per-function"):
            cc.check_audit(report, records)

    def test_matching_suffix_in_another_namespace_is_not_a_proof(self):
        records = [record()]
        report = audit(records)
        report["theorems"][-1]["name"] = "Unrelated.preserves_0"
        with self.assertRaisesRegex(ValueError, "missing per-function"):
            cc.check_audit(report, records)

    def test_missing_shared_generated_case_fails(self):
        # These two translations can share a Gen path, but have separate actual snapshots.
        records = [record(), record("RoundTripBatch1", "SecondCase", index=1)]
        report = audit(records)
        cc.check_audit(report, records)
        report["theorems"] = [t for t in report["theorems"] if t["module"] != "RoundTripBatch1"]
        with self.assertRaisesRegex(ValueError, "RoundTripBatch1: missing per-function"):
            cc.check_audit(report, records)

    def test_replay_cache_and_rejected_policy_are_not_accepted(self):
        records = [record()]
        for change in (lambda r: r["kernel_replay"].update(reused=["RoundTripBatch0"]),
                       lambda r: r["kernel_replay"].update(rejected=["RoundTripBatch0"]),
                       lambda r: r.update(violations=["unreviewed axiom"]),
                       lambda r: r["theorems"][0].update(allowed=False)):
            report = copy.deepcopy(audit(records))
            change(report)
            with self.assertRaises(ValueError):
                cc.check_audit(report, records)

    def test_same_named_shadow_or_changed_artifact_is_not_accepted(self):
        records = [record()]
        for change in (lambda r: r["freshness"]["artifacts"][0].update(olean="/private/tmp/shadow.olean"),
                       lambda r: r["freshness"]["artifacts"][0].update(olean_sha256="other-bytes"),
                       lambda r: r["freshness"].update(artifacts=[])):
            report = audit(records)
            change(report)
            with self.assertRaisesRegex(ValueError, "freshly compiled certificate artifact"):
                cc.check_audit(report, records)

    def test_every_helper_must_be_reached_in_its_actual_defining_module(self):
        records = [record()]
        for change in (lambda r: r["nodes"].pop(),
                       lambda r: r["nodes"][-1].update(dependencies=[]),
                       lambda r: r["nodes"][-2].update(module="AnotherModule"),
                       lambda r: r["nodes"][0].update(module="AnotherModule")):
            report = audit(records)
            change(report)
            with self.assertRaisesRegex(ValueError, "uncovered canonicalization declarations"):
                cc.check_audit(report, records)

    def test_each_case_in_same_module_requires_its_own_roots_and_helper_closure(self):
        records = [record(), record(namespace="SecondCase", index=1)]
        report = audit(records)
        cc.check_audit(report, records)
        report["theorems"] = [t for t in report["theorems"] if t["name"] != "CanonCase0.Case.preserves_0"]
        with self.assertRaisesRegex(ValueError, "missing per-function"):
            cc.check_audit(report, records)
        report = audit(records)
        # The second case still reaches the first case's helper. That must not fill
        # the first case's own now-broken closure merely because both share a module.
        for node in report["nodes"]:
            if node["name"].startswith("CanonCase0.Case.") and node["name"].endswith("_0"):
                node["dependencies"] = []
            if node["name"] == "CanonCase1.SecondCase.metadata_0":
                node["dependencies"].extend(records[0]["helpers"])
        with self.assertRaisesRegex(ValueError, "uncovered canonicalization declarations"):
            cc.check_audit(report, records)

    def test_swapped_case_namespace_and_foreign_artifact_in_same_batch_are_rejected(self):
        records = [record(), record(namespace="SecondCase", index=1)]
        report = audit(records)
        swapped = copy.deepcopy(records)
        swapped[0]["namespace"], swapped[1]["namespace"] = swapped[1]["namespace"], swapped[0]["namespace"]
        with self.assertRaisesRegex(ValueError, "swapped canonicalization case namespace"):
            cc.check_audit(report, swapped)
        records[1]["olean"] = "/private/tmp/foreign.olean"
        with self.assertRaisesRegex(ValueError, "freshly compiled certificate artifact"):
            cc.check_audit(report, records)

    def test_one_invalid_case_rejects_entire_batch_without_audit(self):
        cases = [(0, SimpleNamespace(path="Gen.lean", label="first")),
                 (1, SimpleNamespace(path="Gen.lean", label="second"))]
        with tempfile.TemporaryDirectory() as directory:
            translator = SimpleNamespace(certificate=lambda i, c: SourceTests.source.encode(),
                                         matches=lambda i, c, p: None, work=Path(directory),
                                         arguments={0: ["one"], 1: ["two"]})

            def compile(path, compile_module):
                self.assertIn("namespace CanonCase0", path.read_text())
                self.assertIn("namespace CanonCase1", path.read_text())
                return SimpleNamespace(returncode=1, stdout="second case proof invalid", stderr="")

            with mock.patch.object(cc, "lean", side_effect=compile) as check, \
                    mock.patch.object(cc, "reject_mutant") as mutant, \
                    mock.patch.object(cc, "audit_certificates") as replay:
                with self.assertRaisesRegex(ValueError, "second case proof invalid"):
                    cc.certify(translator, cases)
        check.assert_called_once()
        mutant.assert_not_called()
        replay.assert_not_called()

    def test_repeated_invocations_check_and_replay_again(self):
        translator = SimpleNamespace(certificate=lambda i, c: b"source",
                                     matches=lambda i, c, p: None, work=Path("unused"))
        cases = [(0, SimpleNamespace(path="Gen.lean", label="case"))]
        with mock.patch.object(cc, "compile_batch", return_value=[record()]) as check, \
                mock.patch.object(cc, "reject_mutant", return_value=True), \
                mock.patch.object(cc, "audit_certificates") as replay:
            cc.certify(translator, cases)
            cc.certify(translator, cases)
        self.assertEqual(check.call_count, 2)
        self.assertEqual(replay.call_count, 2)

    def test_eight_plus_one_streams_every_shared_gen_case_in_bounded_batches(self):
        translator = SimpleNamespace(certificate=mock.Mock(side_effect=lambda i, c: f"source{i}".encode()),
                                     matches=mock.Mock(return_value=None), work=Path("unused"))
        cases = [(index, SimpleNamespace(path="Gen.lean", label=f"case{index}")) for index in range(9)]

        def compile(batch, translator, batch_index):
            self.assertEqual(len(batch), 8 if batch_index == 0 else 1)
            # The next batch's source has not been requested while compiling this one.
            self.assertEqual(translator.certificate.call_count, 8 if batch_index == 0 else 9)
            return [record(f"RoundTripBatch{batch_index}", index=index) for index, _, _ in batch]

        with mock.patch.object(cc, "compile_batch", side_effect=compile) as check, \
                mock.patch.object(cc, "reject_mutant", return_value=True), \
                mock.patch.object(cc, "audit_certificates") as replay:
            cc.certify(translator, iter(cases))
        self.assertEqual(check.call_count, 2)
        self.assertEqual([args.args[0] for args in translator.matches.call_args_list], list(range(9)))
        self.assertEqual([args.args[0] for args in translator.certificate.call_args_list], list(range(9)))
        self.assertEqual(len(replay.call_args.args[1]), 9)


class MutantTests(unittest.TestCase):
    source = cc.CERTIFICATE_HEADER + """namespace Case

open Air2Lean

def before_body_0 : Array Inst :=
#[{ id := 0, ty := 1, op := Air2Lean.Op.arg 0 }]

def after_body_0 : Array Inst :=
  DebugIds.mapDebugArray (fun id => id - offset_0) before_body_0

def after_0 : Func := { metadata_0 with body := after_body_0 }

theorem erased_0 : DebugIds.eraseBody before_body_0.toList =
    DebugIds.eraseBody after_body_0.toList :=
  DebugIds.erase_mapDebugArray (fun id => id - offset_0) before_body_0

theorem preserves_0 (call : Sem.Oracle) (args : List Sem.Value) :
    Sem.execFunc call before_0 args = Sem.execFunc call after_0 args :=
  DebugIds.execFunc_of_body_erase_eq call metadata_0 _ _ args erased_0

def snapshots : Array (Nat × Func × Func) := #[(offset_0, before_0, after_0)]

end Case
"""

    def batch(self, directory, source=None):
        return ([(4, SimpleNamespace(label="case"), self.source if source is None else source)],
                SimpleNamespace(work=Path(directory), arguments={4: ["directory"]}))

    def test_mutation_changes_actual_mapped_target_and_requires_proof_error(self):
        with tempfile.TemporaryDirectory() as directory:
            def reject(path):
                source = path.read_text()
                self.assertIn("body.findIdx? (fun i : Inst => match i.op", source)
                self.assertIn("body.modify index (fun i => { i with id := i.id + 1000000 })", source)
                self.assertIn("#[{ id := 0, ty := 1, op := Air2Lean.Op.arg 0 }]", source)
                line = next(i + 1 for i, text in enumerate(source.splitlines())
                            if text.startswith("theorem erased_0"))
                return SimpleNamespace(returncode=1, stdout="canon-mutant-live:4:true\n"
                                       f"{path}:{line}:1: error: false equality", stderr="")
            with mock.patch.object(cc, "lean", side_effect=reject):
                self.assertTrue(cc.reject_mutant(*self.batch(directory)))
            with mock.patch.object(cc, "lean", return_value=SimpleNamespace(
                    returncode=1, stdout=f"{Path(directory) / 'WrongCanonicalization.lean'}:1:1: error: parse", stderr="")):
                with self.assertRaisesRegex(ValueError, "outside its actual equality"):
                    cc.reject_mutant(*self.batch(directory))

    def test_debug_only_first_instruction_is_not_a_live_id_control(self):
        source = self.source.replace("Air2Lean.Op.arg 0", "Air2Lean.Op.line 0")
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(cc, "lean", return_value=
                SimpleNamespace(returncode=0, stdout="canon-mutant-live:4:false\n", stderr="")) as lean:
            self.assertFalse(cc.reject_mutant(*self.batch(directory, source)))
        lean.assert_called_once()

    def test_live_instruction_after_debug_is_selected_without_an_argument(self):
        source = self.source.replace("Air2Lean.Op.arg 0",
                                    "Air2Lean.Op.line 0 }, { id := 1, ty := 1, op := Air2Lean.Op.ret .void")
        with tempfile.TemporaryDirectory() as directory:
            def reject(path):
                mutant = path.read_text()
                self.assertIn("Air2Lean.Op.line 0 }, { id := 1", mutant)
                self.assertIn("| .line _ | .dbg .. => false | _ => true", mutant)
                line = next(i + 1 for i, text in enumerate(mutant.splitlines())
                            if text.startswith("theorem erased_0"))
                return SimpleNamespace(returncode=1, stdout="canon-mutant-live:4:true\n"
                                       f"{path}:{line}:1: error: false equality", stderr="")
            with mock.patch.object(cc, "lean", side_effect=reject):
                self.assertTrue(cc.reject_mutant(*self.batch(directory, source)))

    def test_applicable_mutant_that_still_checks_fails_the_control(self):
        with tempfile.TemporaryDirectory() as directory, mock.patch.object(cc, "lean", return_value=
                SimpleNamespace(returncode=0, stdout="canon-mutant-live:4:true\n", stderr="")):
            with self.assertRaisesRegex(ValueError, "wrong canonicalization still checks"):
                cc.reject_mutant(*self.batch(directory))

    def test_negative_control_preserves_other_cases_and_selects_second_case_proof(self):
        with tempfile.TemporaryDirectory() as directory:
            first = self.source.replace("Air2Lean.Op.arg 0", "Air2Lean.Op.line 0")
            batch = [(4, SimpleNamespace(label="debug-only"), first),
                     (9, SimpleNamespace(label="live-second"), self.source)]
            translator = SimpleNamespace(work=Path(directory), arguments={4: ["one"], 9: ["two"]})

            def reject(path):
                text = path.read_text()
                self.assertEqual(text.count("body.modify index"), 1)
                if "canon-mutant-live:4:" in text:
                    self.assertIn(cc.roundtrip_source(self.source, translator, 9)[1], text)
                    return SimpleNamespace(returncode=0, stdout="canon-mutant-live:4:false\n", stderr="")
                self.assertIn(cc.roundtrip_source(first, translator, 4)[1], text)
                selected = next(i for i, line in enumerate(text.splitlines())
                                if "canon-mutant-live:9:" in line)
                line = next(i + 1 for i, line in enumerate(text.splitlines())
                            if i > selected and line.startswith("theorem erased_0"))
                return SimpleNamespace(returncode=1, stdout="canon-mutant-live:9:true\n"
                                       f"{path}:{line}:1: error: false second equality", stderr="")

            with mock.patch.object(cc, "lean", side_effect=reject) as lean:
                self.assertTrue(cc.reject_mutant(batch, translator))
            self.assertEqual(lean.call_count, 2)

            def wrong_case_error(path):
                result = reject(path)
                if result.returncode:
                    first_proof = next(i + 1 for i, line in enumerate(path.read_text().splitlines())
                                       if line.startswith("theorem erased_0"))
                    result.stdout = ("canon-mutant-live:9:true\n"
                                     f"{path}:{first_proof}:1: error: wrong case equality")
                return result

            with mock.patch.object(cc, "lean", side_effect=wrong_case_error):
                with self.assertRaisesRegex(ValueError, "outside its actual equality obligation"):
                    cc.reject_mutant(batch, translator)


if __name__ == "__main__":
    unittest.main()
