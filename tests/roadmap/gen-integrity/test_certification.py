"""Fail-closed native protocol and separate generic kernel-audit checks."""
import contextlib
import copy
import hashlib
import importlib.util
import io
import json
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location("canon_certification", ROOT / "scripts/canon_certification.py")
cc = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cc)


def binding(functions=1, changed=True):
    return dict(kind="canon-debug-native-binding", version=1, functions=functions, changed=changed)


CANON_SEM = "Air2Lean.CanonSem"
ROOTS = [(module, name) for module, names in cc.GENERIC_ROOTS.items() for name in sorted(names)]


def artifact():
    return {module: dict(olean=f"/private/tmp/{module}.olean", olean_sha256=f"actual-{module}-sha256")
            for module in cc.MODULES}


def audit():
    return dict(status="pass", violations=[], modules=list(cc.MODULES),
                kernel_replay=dict(status="pass", rejected=[], reused=[]),
                freshness=dict(lake_trace_check=dict(status="up-to-date"),
                               artifacts=[dict(module=module, **row) for module, row in artifact().items()]),
                theorems=[dict(module=module, name=name, allowed=True) for module, name in ROOTS],
                nodes=[dict(module=module, name=name, kind="theorem") for module, name in ROOTS])


class ProtocolTests(unittest.TestCase):
    def test_exact_native_reports_accept_zero_or_nonzero_counts(self):
        for report in (binding(), binding(0, False), binding(123456, False)):
            self.assertEqual(cc.native_binding(json.dumps(report).encode()), report)

    def test_missing_or_extra_fields_cannot_claim_kernel_evidence(self):
        for key in binding():
            report = binding()
            del report[key]
            with self.assertRaisesRegex(ValueError, "schema"):
                cc.native_binding(json.dumps(report).encode())
        for extra in (dict(kernel_checked=True), dict(theorems=["preserves_0"]), dict(extra=None)):
            with self.assertRaisesRegex(ValueError, "schema"):
                cc.native_binding(json.dumps(binding() | extra).encode())

    def test_type_confused_or_unsupported_fields_fail(self):
        changes = (dict(kind="kernel-certificate"), dict(kind=None),
                   dict(version=True), dict(version=1.0), dict(version=2), dict(version="1"),
                   dict(functions=True), dict(functions=-1), dict(functions=1.0),
                   dict(functions="1"), dict(functions=None), dict(changed=1), dict(changed="true"))
        for change in changes:
            with self.subTest(change=change), self.assertRaisesRegex(ValueError, "schema"):
                cc.native_binding(json.dumps(binding() | change).encode())

    def test_invalid_utf8_json_duplicate_keys_and_nonobjects_fail(self):
        encoded = json.dumps(binding()).encode()
        invalid = (b"\xff", b"{", encoded + encoded, b"null", b"[]", b"true", b"0",
                   encoded.decode().encode("utf-16"),
                   encoded.replace(b'"version": 1', b'"version": 1, "version": 1'),
                   encoded.replace(b'"changed": true', b'"changed": false, "changed": true'))
        for data in invalid:
            with self.subTest(data=data), self.assertRaises(ValueError):
                cc.native_binding(data)
        with self.assertRaisesRegex(ValueError, "UTF-8 JSON bytes"):
            cc.native_binding(encoded.decode())


class AuditTests(unittest.TestCase):
    def test_generic_roots_in_their_actual_module_are_accepted(self):
        self.assertIn("Air2Lean.DebugIds.execFunc_mapDebugArray", cc.GENERIC_ROOTS[CANON_SEM])
        self.assertIn("Air2Lean.Renumber.execFunc_rename", cc.GENERIC_ROOTS["Air2Lean.Renumber"])
        cc.check_audit(audit(), artifact())

    def test_module_scope_in_any_order_is_accepted(self):
        # scripts/assumptions.sh reports its modules sorted, GENERIC_ROOTS keeps its own order.
        for order in (sorted(cc.MODULES), list(reversed(cc.MODULES))):
            report = audit()
            report["modules"] = order
            with self.subTest(order=order):
                cc.check_audit(report, artifact())

    def test_each_generic_root_requires_its_actual_theorem_and_node(self):
        for _, name in ROOTS:
            for field in ("theorems", "nodes"):
                report = audit()
                report[field] = [row for row in report[field] if row["name"] != name]
                with self.subTest(name=name, field=field), self.assertRaisesRegex(ValueError, "actual generic"):
                    cc.check_audit(report, artifact())
        for field, change in (("theorems", dict(module="Foreign")),
                              ("nodes", dict(module="Foreign")), ("nodes", dict(kind="definition"))):
            report = audit()
            report[field][0].update(change)
            with self.assertRaisesRegex(ValueError, "actual generic|out-of-scope"):
                cc.check_audit(report, artifact())
        for field in ("theorems", "nodes"):
            report = audit()
            report[field].append(copy.deepcopy(report[field][0]))
            with self.assertRaisesRegex(ValueError, "actual generic"):
                cc.check_audit(report, artifact())

    def test_replay_reuse_rejection_staleness_and_wrong_scope_fail(self):
        changes = (lambda r: r.update(status="fail"), lambda r: r.update(violations=["axiom"]),
                   lambda r: r.update(modules=[*cc.MODULES, "RoundTrip0"]),
                   lambda r: r.update(modules=["RoundTrip0"]),
                   lambda r: r.update(modules=[CANON_SEM]),
                   lambda r: r.update(modules=[*cc.MODULES[1:], cc.MODULES[1]]),
                   lambda r: r.update(modules=dict.fromkeys(cc.MODULES)),
                   lambda r: r.update(modules=None),
                   lambda r: r["kernel_replay"].update(status="fail"),
                   lambda r: r["kernel_replay"].update(reused=[CANON_SEM]),
                   lambda r: r["kernel_replay"].update(rejected=[CANON_SEM]),
                   lambda r: r["freshness"]["lake_trace_check"].update(status="stale"),
                   lambda r: r["theorems"][0].update(allowed=False),
                   lambda r: r["theorems"].append(dict(module="RoundTrip0", name="preserves_0", allowed=True)))
        for change in changes:
            report = audit()
            change(report)
            with self.assertRaises(ValueError):
                cc.check_audit(report, artifact())

    def test_missing_duplicate_foreign_or_changed_artifact_fails(self):
        changes = (lambda r: r["freshness"].update(artifacts=[]),
                   lambda r: r["freshness"]["artifacts"].append(r["freshness"]["artifacts"][0]),
                   lambda r: r["freshness"]["artifacts"][0].update(module="Other"),
                   lambda r: r["freshness"]["artifacts"][0].update(olean="/private/tmp/foreign.olean"),
                   lambda r: r["freshness"]["artifacts"][0].update(olean_sha256="changed"))
        for change in changes:
            report = audit()
            change(report)
            with self.assertRaisesRegex(ValueError, "actual artifact"):
                cc.check_audit(report, artifact())

    def test_generic_artifact_hashes_the_actual_built_module(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / ".lake/build/lib/lean/Air2Lean/CanonSem.olean"
            path.parent.mkdir(parents=True)
            path.write_bytes(b"unit fixture bytes")
            with mock.patch.object(cc, "ROOT", root):
                actual = cc.generic_artifact(CANON_SEM)
                self.assertEqual(actual, dict(olean=str(path.resolve()),
                    olean_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
                report = audit()
                report["freshness"]["artifacts"][0] = dict(module=CANON_SEM,
                    olean=str(path.relative_to(root)), olean_sha256=actual["olean_sha256"])
                cc.check_audit(report, artifact() | {CANON_SEM: actual})

    def test_one_existing_assurance_call_with_no_build_cache_or_private_lean_path(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)

            def run(arguments, **kwargs):
                self.assertEqual([arguments[i + 1] for i, a in enumerate(arguments) if a == "--module"],
                                 list(cc.MODULES))
                self.assertIn("--no-build", arguments)
                self.assertNotIn("--replay-cache", arguments)
                self.assertEqual(kwargs["env"]["LEAN_PATH"], "existing-path")
                self.assertEqual(kwargs["env"]["AIR2LEAN_REPLAY_JOBS"], "2")
                (work / "audit.json").write_text(json.dumps(audit()))
                return SimpleNamespace(returncode=0, stdout="", stderr="")

            with mock.patch.dict(cc.os.environ, LEAN_PATH="existing-path", AIR2LEAN_JOBS="2"), \
                    mock.patch.object(cc, "generic_artifacts", return_value=artifact()) as hashed, \
                    mock.patch.object(cc.subprocess, "run", side_effect=run) as executed, \
                    contextlib.redirect_stdout(io.StringIO()):
                cc.audit_certificates(work)
            executed.assert_called_once()
            self.assertEqual(hashed.call_count, 2)
            self.assertEqual([p.name for p in work.iterdir()], ["audit.json"])

    def test_artifact_change_during_audit_and_audit_process_failure_propagate(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            (work / "audit.json").write_text(json.dumps(audit()))
            changed = artifact() | {CANON_SEM: artifact()[CANON_SEM] | dict(olean_sha256="new")}
            with mock.patch.object(cc, "generic_artifacts", side_effect=[artifact(), changed]), \
                    mock.patch.object(cc.subprocess, "run", return_value=SimpleNamespace(returncode=0)):
                with self.assertRaisesRegex(ValueError, "changed during its audit"):
                    cc.audit_certificates(work)
            with mock.patch.object(cc, "generic_artifacts", return_value=artifact()), \
                    mock.patch.object(cc.subprocess, "run", return_value=SimpleNamespace(
                        returncode=1, stdout="", stderr="actual replay failure")):
                with self.assertRaisesRegex(ValueError, "actual replay failure"):
                    cc.audit_certificates(work)


class CohortTests(unittest.TestCase):
    cases = [(index, SimpleNamespace(path="Gen.lean", label=f"case{index}")) for index in (1, 4, 7)]

    def translator(self, work, reports=None):
        return SimpleNamespace(work=work, matches=mock.Mock(return_value=None),
            certificate=mock.Mock(side_effect=[json.dumps(r).encode() for r in
                                               (reports or [binding(), binding(), binding()])]))

    def test_every_shared_gen_case_is_checked_and_receipts_are_native_only(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            reports = [binding(0, False), binding(3), binding(4, False)]
            translator = self.translator(work, reports)
            output = io.StringIO()
            with mock.patch.object(cc, "audit_certificates") as replay, contextlib.redirect_stdout(output):
                cc.certify(translator, iter(self.cases))
            self.assertEqual([call.args[0] for call in translator.matches.call_args_list], [1, 4, 7])
            self.assertEqual([call.args[0] for call in translator.certificate.call_args_list], [1, 4, 7])
            replay.assert_called_once_with(work)
            self.assertEqual(sorted(p.name for p in work.iterdir()),
                             ["NativeBinding1.json", "NativeBinding4.json", "NativeBinding7.json"])
            for (index, _), report in zip(self.cases, reports):
                self.assertEqual(json.loads((work / f"NativeBinding{index}.json").read_text()), report)
            self.assertIn("3 TRU-02 native bindings, 7 functions", output.getvalue())
            self.assertIn("generic CanonSem/Renumber kernel replay checked separately", output.getvalue())

    def test_mismatch_producer_failure_and_invalid_protocol_never_reach_audit(self):
        for failure in ("mismatch", "producer", "protocol"):
            with tempfile.TemporaryDirectory() as directory:
                translator = self.translator(Path(directory))
                if failure == "mismatch":
                    translator.matches.side_effect = [None, "changed Gen"]
                else:
                    translator.certificate.side_effect = [json.dumps(binding()).encode(),
                        ValueError("producer failed") if failure == "producer" else b"not JSON"]
                with mock.patch.object(cc, "audit_certificates") as replay, \
                        contextlib.redirect_stdout(io.StringIO()), self.assertRaises(ValueError):
                    cc.certify(translator, self.cases)
                replay.assert_not_called()
                self.assertEqual(translator.matches.call_count, 2)

    def test_empty_zero_function_and_no_real_debug_change_cohorts_fail(self):
        scopes = ([], [binding(0, False)], [binding(2, False)],
                  [binding(0, True), binding(1, False)])
        for reports in scopes:
            with tempfile.TemporaryDirectory() as directory:
                translator = self.translator(Path(directory), reports)
                cases = self.cases[:len(reports)]
                with mock.patch.object(cc, "audit_certificates") as replay, \
                        contextlib.redirect_stdout(io.StringIO()), self.assertRaises(ValueError):
                    cc.certify(translator, cases)
                replay.assert_not_called()

    def test_repeated_runs_check_every_case_and_replay_again(self):
        with tempfile.TemporaryDirectory() as directory:
            translator = self.translator(Path(directory), [binding(), binding()])
            with mock.patch.object(cc, "audit_certificates") as replay, contextlib.redirect_stdout(io.StringIO()):
                cc.certify(translator, self.cases[:1])
                cc.certify(translator, self.cases[:1])
            self.assertEqual(translator.certificate.call_count, 2)
            self.assertEqual(replay.call_count, 2)

    def test_generic_audit_failure_cannot_print_an_acceptance_summary(self):
        with tempfile.TemporaryDirectory() as directory:
            translator = self.translator(Path(directory))
            output = io.StringIO()
            with mock.patch.object(cc, "audit_certificates", side_effect=ValueError("generic replay failed")), \
                    contextlib.redirect_stdout(output), self.assertRaisesRegex(ValueError, "generic replay failed"):
                cc.certify(translator, self.cases)
            self.assertNotIn("generic CanonSem kernel replay checked separately", output.getvalue())


if __name__ == "__main__":
    unittest.main()
