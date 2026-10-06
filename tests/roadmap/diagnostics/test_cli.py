#!/usr/bin/env python3
"""Actual-CLI regressions; --self-test checks bounded harness oracles without tools."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile
import unittest


VOID = dict(k="void", abi_size=0, abi_align=1)
NORETURN = dict(k="noreturn")
INT = dict(k="int", signed=False, bits=32, abi_size=4, abi_align=4)
PTR = dict(k="ptr", size="one", const=False, child=0, abi_size=8, abi_align=8, ptr_align=4)


def inst(i, tag, ty, args=(), **extra):
    return dict(id=i, tag=tag, ty=ty, args=list(args), **extra)


def function(name, body=None):
    return dict(schema=11, zig_version="0.16.0", name=name, types=[VOID, NORETURN],
                params=[], ret=0, body=body if body is not None else [
                    inst(0, "ret", 1, [dict(ty=0, val="{}")])], globals=[])



def runtime_tag_cases():
    """Actual enum membership; synthetic rejection cases, not compiler fixtures."""
    common = {"inferred_alloc": "unresolved inferred allocation",
              "inferred_alloc_comptime": "unresolved inferred allocation",
              "err_return_trace": "mutable error-return-trace",
              "set_err_return_trace": "mutable error-return-trace",
              "save_err_return_trace_index": "mutable error-return-trace"}
    cases = []
    for version in ("0.14.1", "0.15.2", "0.16.0"):
        reasons = dict(common)
        if version != "0.14.1":
            reasons["runtime_nav_ptr"] = "identity and lifetime"
        if version == "0.16.0":
            reasons.update({tag: "compiler legalization" for tag in (
                "legalize_vec_store_elem", "legalize_vec_elem_val", "legalize_compiler_rt_call")})
            reasons["cmp_lte_errors_len"] = "finalized compiler error universe"
        else:
            reasons["vector_store_elem"] = "vector-element memory writes"
            reasons["cmp_lt_errors_len"] = "finalized compiler error universe"
        cases.extend((version, tag, reason) for tag, reason in reasons.items())
    return cases


def calls(name, *targets):
    return function(name, [inst(i, "call", 0, callee=dict(func=target, noreturn=False))
                           for i, target in enumerate(targets)] + [
                               inst(len(targets), "ret", 1, [dict(ty=0, val="{}")])])


def decode(result, expected_status=None):
    assert result.stderr == "", result.stderr
    report = json.loads(result.stdout)
    assert report["schema"] == 1 and report["kind"] == "air2lean-check-diagnostics"
    assert report["proof_status"] == "not_run" and report["runtime_outcomes"] == "not_observed"
    assert report["source_correspondence"] == "not_attested"
    assert result.returncode == (1 if report["status"] == "rejected" else 0)
    assert report["status"] in ("checked", "rejected")
    if expected_status is not None:
        assert report["status"] == expected_status
    if report["status"] == "checked":
        assert report["complete"] is True and report["truncated"] is False
        assert not report["diagnostics"]
        assert all(f["local_check"] == "passed" for f in report["files"])
    assert len(report["diagnostics"]) <= report["diagnostic_limit"]
    assert report["diagnostic_payload_bytes"] <= 1024 * 1024
    if report["truncated"] or any(d["first_error_in_unit"] for d in report["diagnostics"]):
        assert report["complete"] is False
    for d in report["diagnostics"]:
        assert d["source_span"] is None and d["source_span_status"] == "unavailable_in_AIR"
        assert d["anchor"]["id_space"] in ("canonical", "exported", "unavailable")
        assert isinstance(d["prerequisites"], list) and isinstance(d["dependency_chain"], list)
    return report


def invoke(binary, air, *flags):
    return subprocess.run([str(binary), "--diagnostics-json", str(air), *flags],
                          capture_output=True, text=True, timeout=15, check=False)


def write(air, documents):
    for old in air.glob("*.json"):
        old.unlink()
    for name, document in documents.items():
        text = document if isinstance(document, str) else json.dumps(document)
        (air / name).write_text(text)


def run(binary, baseline=None):
    checks = 0
    with tempfile.TemporaryDirectory(prefix="air2lean-diagnostics-") as directory:
        directory = Path(directory)
        air = directory / "air"
        air.mkdir()
        output = directory / "Gen.lean"
        output.write_text("sentinel\n")
        marked = function("marked", [inst(42, "unknown_a", 0, unsupported=True),
                                      inst(43, "unknown_b", 0, unsupported=True)])
        write(air, {"a.json": "{", "b.json": "{", "marked.json": marked, "ok.json": function("ok")})
        first = invoke(binary, air)
        report = decode(first, "rejected")
        assert [d["file"].split("/")[-1] for d in report["diagnostics"] if d["code"] == "JSON_SYNTAX"] == ["a.json", "b.json"]
        markers = [d for d in report["diagnostics"] if d["code"] == "EXPORTER_UNSUPPORTED"]
        assert [d["anchor"]["instruction"] for d in markers] == [42, 43]
        assert all(d["anchor"]["id_space"] == "exported" for d in markers)
        assert any(f["function"] == "ok" and f["local_check"] == "passed" for f in report["files"])
        second = invoke(binary, air)
        decode(second, "rejected")
        assert second.stdout == first.stdout, "deterministic report bytes"
        assert output.read_text() == "sentinel\n"
        cap = decode(invoke(binary, air, "--diagnostic-limit", "1"), "rejected")
        assert len(cap["diagnostics"]) == 1 and cap["truncated"] and not cap["complete"]
        checks += 3

        # Each known compiler/runtime family remains rejected, including nested
        # exported markers whose inferred allocations deliberately omit ty.
        for version, tag, reason in runtime_tag_cases():
            child = inst(42, tag, 0, unsupported=True)
            if tag.startswith("inferred_alloc"):
                child.pop("ty")
            document = function("runtime_tag", [inst(7, "block", 0, body=[child])])
            document["zig_version"] = version
            write(air, {"runtime-tag.json": document})
            report = decode(invoke(binary, air), "rejected")
            found = [d for d in report["diagnostics"] if d["code"] == "EXPORTER_UNSUPPORTED"]
            assert len(found) == 1 and found[0]["anchor"]["instruction"] == 42
            assert found[0]["anchor"]["id_space"] == "exported"
            assert found[0]["category"] == "unsupported_semantics"
            assert tag in found[0]["message"] and reason in found[0]["message"]
            assert "runtime_tag: inst 42:" in found[0]["message"]
            assert output.read_text() == "sentinel\n"
            checks += 1

        write(air, {"ok.json": function("ok")})
        (air / "a-invalid.json").write_bytes(b"\xff")
        (air / "b-unreadable.json").symlink_to(air / "absent-input")
        (air / "c-directory.json").mkdir()
        report = decode(invoke(binary, air), "rejected")
        reads = [d for d in report["diagnostics"] if d["code"] == "INPUT_READ"]
        assert [Path(d["file"]).name for d in reads] == ["a-invalid.json", "b-unreadable.json", "c-directory.json"]
        assert all(d["category"] == "io_failure" and d["first_error_in_unit"] for d in reads)
        assert any("non UTF-8 AIR input" in d["message"] for d in reads)
        assert any("AIR input must be a regular file" in d["message"] for d in reads)
        assert any(f["function"] == "ok" and f["local_check"] == "passed" for f in report["files"])
        assert all(f["local_check"] == "blocked_or_rejected" and not f["normalized"]
                   for f in report["files"] if Path(f["file"]).name != "ok.json")
        assert output.read_text() == "sentinel\n"
        (air / "c-directory.json").rmdir()
        checks += 1

        write(air, {"ok.json": function("ok")})
        # A sparse logical oversize tests pre-open classification without allocating 64 MiB.
        with (air / "a-oversize.json").open("wb") as oversized:
            oversized.truncate(64 * 1024 * 1024 + 1)
        report = decode(invoke(binary, air), "rejected")
        limits = [d for d in report["diagnostics"] if d["code"] == "INPUT_LIMIT"]
        assert len(limits) == 1 and Path(limits[0]["file"]).name == "a-oversize.json"
        assert limits[0]["category"] == "resource_limit" and limits[0]["first_error_in_unit"]
        assert any(d["code"] == "PREREQUISITE_SKIPPED" and
                   d["prerequisites"] == ["readable_input_within_aggregate_budget"] for d in report["diagnostics"])
        assert any(f["function"] == "ok" and f["local_check"] == "passed" for f in report["files"])
        assert output.read_text() == "sentinel\n"
        checks += 1

        write(air, {"repeated.json": calls("repeated", "missing", "missing")})
        report = decode(invoke(binary, air), "rejected")
        missing = [d for d in report["diagnostics"] if d["code"] == "CALLEE_MISSING"]
        assert [d["anchor"]["instruction"] for d in missing] == [0, 1]
        assert all(d["dependency_chain"] == ["repeated", "missing"] for d in missing)
        assert output.read_text() == "sentinel\n"
        checks += 1

        branch = function("branches", [inst(0, "arg", 3, param=0), inst(7, "dbg_stmt", 1, line=42),
            inst(1, "cond_br", 2, [dict(ty=4, val="true")], **{"then": [
                inst(10, "atomic_load", 0, [dict(inst=0)], order="unordered")], "else": [
                inst(20, "assembly", 1, source="", volatile=False, clobbers=["memory"], outputs=[], inputs=[])]}),
            inst(30, "ret", 2, [dict(ty=1, val="{}")])])
        branch.update(types=[INT, VOID, NORETURN, PTR, dict(k="bool", abi_size=1, abi_align=1)], params=[3], ret=1)
        write(air, {"branches.json": branch})
        report = decode(invoke(binary, air), "rejected")
        failures = [d for d in report["diagnostics"] if d["code"] == "INSTRUCTION_FAILURE"]
        assert len(failures) == 2, report
        assert all(d["anchor"]["id_space"] == "canonical" and d["anchor"]["nearest_dbg_line"] == 42 for d in failures)
        assert not report["complete"] and not report["truncated"]
        default = subprocess.run([str(binary), str(air), "-o", str(output), "--namespace", "Diagnostics"],
                                 text=True, capture_output=True, timeout=15)
        assert default.returncode == 1 and output.read_text() == "sentinel\n"
        checks += 2

        prerequisite = function("prerequisite", [inst(0, "arg", 3, param=0),
            inst(1, "ptr_elem_ptr", 4, [dict(inst=0), dict(ty=0, val="0")]),
            inst(2, "ptr_elem_ptr", 4, [dict(inst=0), dict(ty=0, val="0")]),
            inst(3, "assembly", 1, source="", volatile=False, clobbers=["memory"], outputs=[], inputs=[]),
            inst(4, "ret", 2, [dict(ty=1, val="{}")])])
        prerequisite.update(types=[INT, VOID, NORETURN, PTR, dict(k="other", name="x" * (100 * 1024))],
                            params=[3], ret=1)
        write(air, {"prerequisite.json": prerequisite})
        report = decode(invoke(binary, air), "rejected")
        assert all(len(d["message"]) <= 2048 for d in report["diagnostics"])
        assert len([d for d in report["diagnostics"] if d["message_truncated"]]) >= 2
        assert len([d for d in report["diagnostics"] if d["code"] == "PREREQUISITE_SKIPPED" and
                    d["prerequisites"] == ["instruction_result_type"]]) == 2
        assert len([d for d in report["diagnostics"] if d["code"] == "INSTRUCTION_FAILURE"]) == 1
        checks += 1

        write(air, {"root.json": calls("root", "mid", "missing_a", "missing_b"),
                    "mid.json": calls("mid", "root", "marked"), "marked.json": marked})
        report = decode(invoke(binary, air), "rejected")
        assert any(d["code"] == "CALLEE_BLOCKED" and d["dependency_chain"] == ["root", "mid", "marked"] for d in report["diagnostics"])
        assert {d["dependency_chain"][-1] for d in report["diagnostics"] if d["code"] == "CALLEE_MISSING"} == {"missing_a", "missing_b"}
        assert report["runtime_outcomes"] == "not_observed", "cycles cannot be labeled divergence"
        checks += 1
        write(air, {"a.json": function("duplicate"), "b.json": function("duplicate"), "caller.json": calls("caller", "duplicate")})
        report = decode(invoke(binary, air), "rejected")
        assert any(d["code"] == "DUPLICATE_FUNCTION" for d in report["diagnostics"])
        assert any(d["code"] == "CALLEE_AMBIGUOUS" for d in report["diagnostics"])
        checks += 1
        write(air, {"ok.json": function("ok")})
        report = decode(invoke(binary, air), "checked")
        assert report["status"] == "checked" and report["complete"] and not report["diagnostics"]
        assert output.read_text() == "sentinel\n"
        for flags in (("-o", str(output)), ("--namespace", "N"), ("--prefix", "p"),
                      ("--float-semantics", "ieee"), ("--diagnostic-limit", "0")):
            rejected = decode(invoke(binary, air, *flags), "rejected")
            assert rejected["diagnostics"][0]["code"] == "CLI_ARGUMENTS"
            assert output.read_text() == "sentinel\n"
        checks += 6
        if baseline is not None:
            reference = directory / "Reference.lean"
            for executable, destination in ((baseline, reference), (binary, output)):
                emitted = subprocess.run([str(executable), str(air), "-o", str(destination), "--namespace", "Diagnostics"],
                                         text=True, capture_output=True, timeout=15)
                assert emitted.returncode == 0, emitted.stderr
            assert output.read_bytes() == reference.read_bytes(), "default successful emission changed"
            checks += 1
        else:
            print("baseline emission-byte comparison not run (supply --baseline)")
    print(f"diagnostic CLI regressions passed: {checks}")


class HarnessTests(unittest.TestCase):
    def valid(self):
        return dict(schema=1, kind="air2lean-check-diagnostics", proof_status="not_run",
                    runtime_outcomes="not_observed", source_correspondence="not_attested",
                    status="checked", diagnostics=[], diagnostic_limit=256, files=[],
                    diagnostic_payload_bytes=0, complete=True, truncated=False)

    def result(self, report, status=0):
        return subprocess.CompletedProcess([], status, json.dumps(report), "")

    def test_oracle_refuses_inflated_evidence(self):
        for key, value in (("proof_status", "proved"), ("runtime_outcomes", "no_failures"),
                           ("source_correspondence", "verified")):
            report = self.valid()
            report[key] = value
            with self.assertRaises(AssertionError):
                decode(self.result(report))

    def test_oracle_refuses_hidden_truncation_and_failed_verdict(self):
        report = self.valid()
        report["truncated"] = True
        with self.assertRaises(AssertionError):
            decode(self.result(report))
        with self.assertRaises(AssertionError):
            decode(self.result(self.valid(), 1))

    def test_oracle_refuses_checked_blockers_and_wrong_expected_status(self):
        blocker = dict(code="EXPORTER_UNSUPPORTED", first_error_in_unit=False,
                       source_span=None, source_span_status="unavailable_in_AIR",
                       anchor=dict(id_space="exported"), prerequisites=[], dependency_chain=[])
        report = self.valid()
        report.update(diagnostics=[blocker], complete=False, truncated=True)
        with self.assertRaises(AssertionError):
            decode(self.result(report))
        report = self.valid()
        report["files"] = [dict(local_check="blocked_or_rejected")]
        with self.assertRaises(AssertionError):
            decode(self.result(report))
        with self.assertRaises(AssertionError):
            decode(self.result(self.valid()), "rejected")

    def test_synthetic_dependency_and_branch_inputs(self):
        document = calls("root", "mid", "missing")
        self.assertEqual([i["callee"]["func"] for i in document["body"][:-1]], ["mid", "missing"])
        self.assertEqual(document["body"][-1]["tag"], "ret")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path, nargs="?")
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        unittest.main(argv=[__file__])
    elif args.binary:
        run(args.binary.resolve(strict=True), args.baseline.resolve(strict=True) if args.baseline else None)
    else:
        parser.error("provide a root-built translator, or --self-test for offline harness checks")
