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


def record(module="RoundTrip0", namespace="Case", count=1):
    return dict(module=module, namespace=namespace, count=count, changed=True, seconds=0, bytes=0,
                olean=f"/private/tmp/{module}.olean", olean_sha256="fresh-compiled-bytes")


def audit(records):
    return dict(status="pass", violations=[],
                modules=sorted({"Air2Lean.CanonSem", "Air2Lean.CanonCertificate",
                                *(r["module"] for r in records)}),
                kernel_replay=dict(status="pass", rejected=[], reused=[]),
                freshness=dict(artifacts=[dict(module=r["module"], olean=r["olean"],
                                               olean_sha256=r["olean_sha256"]) for r in records]),
                theorems=[dict(module=r["module"], name=f"{r['namespace']}.{kind}_{index}", allowed=True)
                          for r in records for index in range(r["count"])
                          for kind in ("erased", "preserves")])


class ScopeTests(unittest.TestCase):
    def test_missing_second_function_proof_fails(self):
        records = [record(count=2)]
        report = audit(records)
        cc.check_audit(report, records)
        report["theorems"] = [t for t in report["theorems"] if t["name"] != "Case.preserves_1"]
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
        records = [record(), record("RoundTrip1", "SecondCase")]
        report = audit(records)
        cc.check_audit(report, records)
        report["theorems"] = [t for t in report["theorems"] if t["module"] != "RoundTrip1"]
        with self.assertRaisesRegex(ValueError, "RoundTrip1: missing per-function"):
            cc.check_audit(report, records)

    def test_replay_cache_and_rejected_policy_are_not_accepted(self):
        records = [record()]
        for change in (lambda r: r["kernel_replay"].update(reused=["RoundTrip0"]),
                       lambda r: r["kernel_replay"].update(rejected=["RoundTrip0"]),
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

    def test_shared_generated_path_does_not_shortcut_case_checking(self):
        translator = SimpleNamespace(certificate=lambda i, c: b"source",
                                     matches=lambda i, c, p: None, work=Path("unused"))
        cases = [(0, SimpleNamespace(path="Gen.lean", label="first")),
                 (1, SimpleNamespace(path="Gen.lean", label="second"))]
        with mock.patch.object(cc, "compile_certificate", side_effect=[record(), ValueError("second invalid")]) as check, \
                mock.patch.object(cc, "reject_mutant", return_value=True), \
                mock.patch.object(cc, "audit_certificates") as replay:
            with self.assertRaisesRegex(ValueError, "second invalid"):
                cc.certify(translator, cases)
        self.assertEqual(check.call_count, 2)
        replay.assert_not_called()

    def test_repeated_invocations_check_and_replay_again(self):
        translator = SimpleNamespace(certificate=lambda i, c: b"source",
                                     matches=lambda i, c, p: None, work=Path("unused"))
        cases = [(0, SimpleNamespace(path="Gen.lean", label="case"))]
        with mock.patch.object(cc, "compile_certificate", return_value=record()) as check, \
                mock.patch.object(cc, "reject_mutant", return_value=True), \
                mock.patch.object(cc, "audit_certificates") as replay:
            cc.certify(translator, cases)
            cc.certify(translator, cases)
        self.assertEqual(check.call_count, 2)
        self.assertEqual(replay.call_count, 2)


class MutantTests(unittest.TestCase):
    source = """def before_body_0 : Array Inst :=
#[{ id := 0, ty := 1, op := Air2Lean.Op.arg 0 }]

def after_body_0 : Array Inst :=
  DebugIds.mapDebugArray (fun id => id - offset_0) before_body_0

def after_0 : Func := { metadata_0 with body := after_body_0 }

theorem erased_0 : DebugIds.eraseBody before_body_0.toList =
    DebugIds.eraseBody after_body_0.toList :=
  DebugIds.erase_mapDebugArray (fun id => id - offset_0) before_body_0

theorem preserves_0 (call : Sem.Oracle) (args : List Sem.Value) :
"""

    def test_mutation_changes_actual_mapped_target_and_requires_proof_error(self):
        with tempfile.TemporaryDirectory() as directory:
            def reject(path):
                source = path.read_text()
                self.assertIn(".modify 0 (fun i => { i with id := i.id + 1000000 })", source)
                self.assertIn("#[{ id := 0, ty := 1, op := Air2Lean.Op.arg 0 }]", source)
                line = next(i + 1 for i, text in enumerate(source.splitlines())
                            if text.startswith("theorem erased_0"))
                return SimpleNamespace(returncode=1, stdout=f"{path}:{line}:1: error: false equality", stderr="")
            with mock.patch.object(cc, "lean", side_effect=reject):
                self.assertTrue(cc.reject_mutant(self.source, Path(directory)))
            with mock.patch.object(cc, "lean", return_value=SimpleNamespace(
                    returncode=1, stdout=f"{Path(directory) / 'WrongCanonicalization.lean'}:1:1: error: parse", stderr="")):
                with self.assertRaisesRegex(ValueError, "outside its actual equality"):
                    cc.reject_mutant(self.source, Path(directory))

    def test_debug_only_first_instruction_is_not_a_live_id_control(self):
        source = self.source.replace("Air2Lean.Op.arg 0", "Air2Lean.Op.line 0")
        with mock.patch.object(cc, "lean") as lean:
            self.assertFalse(cc.reject_mutant(source, Path("unused")))
        lean.assert_not_called()


if __name__ == "__main__":
    unittest.main()
