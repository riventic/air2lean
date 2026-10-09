#!/usr/bin/env python3
"""I05 independent-blocker collection through the actual check-only CLI.

One run must report every independent blocker of a unit and of a multi-file project;
malformed input stays one fatal unit error. Never runs Zig, Lake or a proof checker.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("diagnostics_cli", ROOT / "tests/roadmap/diagnostics/test_cli.py")
cli = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cli)
inst, function, calls, decode, invoke, write = (cli.inst, cli.function, cli.calls, cli.decode,
                                                cli.invoke, cli.write)
RET = inst(99, "ret", 1, [dict(ty=0, val="{}")])


def blockers(report, code=None, file=None):
    """Non-skipped diagnostics, optionally filtered by code and by input file name."""
    return [d for d in report["diagnostics"] if d["category"] != "skipped_prerequisite"
            and (code is None or d["code"] == code)
            and (file is None or (d["file"] and Path(d["file"]).name == file))]


def several():
    """Four independent unsupported constructs, nested and top-level, plus a missing callee."""
    return function("several", [
        inst(1, "err_return_trace", 0),
        inst(2, "block", 0, body=[inst(3, "unknown_plain", 0), inst(4, "vendor_marked", 0, unsupported=True)]),
        inst(5, "call", 0, callee=dict(func="absent", noreturn=False)),
        inst(6, "runtime_nav_ptr", 0),
        RET])


def project_coverage(binary, base, air_files, expected):
    """The project coverage command retains every producer blocker from one invocation."""
    for name in ("source.zig", "patch", "runtime", "toolchain", "contract"):
        (base / name).write_text("evidence")
    (base / "profile.json").write_text(json.dumps(dict(name="legacy-abi64-le", zig_version="0.16.0")))
    manifest = dict(schema=1, profile="profile.json", float_semantics="ieee", source_closure=["source.zig"],
        components=dict(compiler_patch=["patch"], runtime=["runtime"], toolchain=["toolchain"]),
        allowed_assumptions=[], roots=[dict(id="main", function="main", air=[f"air/{n}" for n in air_files],
        namespace="Main", prefix="", contracts=["contract"], goals=[], assumptions=[], exclusions=[])])
    (base / "project.json").write_text(json.dumps(manifest))
    out = base / "coverage.json"
    result = subprocess.run([sys.executable, str(ROOT / "scripts/project-diagnostics.py"), "check",
                             str(base / "project.json"), "--translator", str(binary), "--out", str(out)],
                            capture_output=True, text=True, timeout=120, check=False)
    assert result.returncode == 1, result.stderr
    report = json.loads(out.read_text())
    assert report["status"] == "rejected" and len(report["root_checks"]) == 1
    producer = report["root_checks"][0]["producer"]
    assert len(blockers(producer)) == expected, producer


def run(binary):
    checks = 0
    with tempfile.TemporaryDirectory(prefix="air2lean-blockers-") as directory:
        air = Path(directory) / "air"
        air.mkdir()

        write(air, {"several.json": several()})
        report = decode(invoke(binary, air), "rejected")
        marker = blockers(report, "EXPORTER_UNSUPPORTED")
        assert [d["anchor"]["instruction"] for d in marker] == [4], report
        assert marker[0]["anchor"]["id_space"] == "exported"
        normal = blockers(report, "NORMALIZATION_FAILURE")
        assert len(normal) == 3, report
        assert all(d["anchor"]["id_space"] == "canonical" and d["phase"] == "normalize" for d in normal)
        assert len({d["anchor"]["instruction"] for d in normal}) == 3
        by_tag = {tag: d for d in normal for tag in ("err_return_trace", "unknown_plain", "runtime_nav_ptr")
                  if f"'{tag}'" in d["message"]}
        assert by_tag["err_return_trace"]["category"] == "unsupported_semantics"
        assert by_tag["runtime_nav_ptr"]["category"] == "unsupported_semantics"
        assert by_tag["unknown_plain"]["category"] == "validation_failure"
        missing = blockers(report, "CALLEE_MISSING")
        assert len(missing) == 1 and missing[0]["dependency_chain"] == ["several", "absent"], report
        assert any(d["code"] == "PREREQUISITE_SKIPPED" and d["prerequisites"] == ["fully_normalized_function"]
                   for d in report["diagnostics"])
        assert not report["complete"] and not report["truncated"]
        assert all(d["category"] != "malformed_input" for d in report["diagnostics"])
        checks += 1

        # A project: independent blocked units, check-stage failures, a missing leaf and a
        # supported sibling are all reported by a single invocation, with call-graph chains.
        branch = function("branchy", [inst(0, "arg", 3, param=0),
            inst(1, "cond_br", 2, [dict(ty=4, val="true")], **{"then": [
                inst(10, "atomic_load", 0, [dict(inst=0)], order="unordered")], "else": [
                inst(20, "assembly", 1, source="mfence", volatile=False, clobbers=[], outputs=[], inputs=[])]}),
            inst(30, "ret", 2, [dict(ty=1, val="{}")])])
        branch.update(types=[cli.INT, cli.VOID, cli.NORETURN, cli.PTR, dict(k="bool", abi_size=1, abi_align=1)],
                      params=[3], ret=1)
        traced = function("traced", [inst(0, "err_return_trace", 0),
                                     inst(1, "call", 0, callee=dict(func="leaf_missing", noreturn=False)), RET])
        unknown = function("unknown", [inst(0, "unknown_a", 0), inst(1, "unknown_b", 0), RET])
        write(air, {"main.json": calls("main", "traced", "unknown", "ok"), "traced.json": traced,
                    "unknown.json": unknown, "branchy.json": branch, "ok.json": function("ok")})
        first = invoke(binary, air)
        report = decode(first, "rejected")
        files = {Path(f["file"]).name: f for f in report["files"]}
        assert files["ok.json"]["local_check"] == "passed" and files["main.json"]["local_check"] == "passed"
        assert len(blockers(report, "NORMALIZATION_FAILURE", "traced.json")) == 1
        assert len(blockers(report, "NORMALIZATION_FAILURE", "unknown.json")) == 2
        # The output-less `mfence` is off the reviewed allowlist (L13): its own stable code.
        assert len(blockers(report, "INSTRUCTION_FAILURE")) == 1
        assert len(blockers(report, "ASM_VOLATILE_EFFECT")) == 1
        chains = sorted(d["dependency_chain"] for d in blockers(report, "CALLEE_BLOCKED"))
        assert ["main", "traced"] in chains and ["main", "unknown"] in chains, chains
        assert ["main", "ok"] not in chains
        leaf = [d["dependency_chain"] for d in blockers(report, "CALLEE_MISSING")]
        assert ["main", "traced", "leaf_missing"] in leaf and ["traced", "leaf_missing"] in leaf, leaf
        assert invoke(binary, air).stdout == first.stdout, "deterministic report bytes"
        checks += 1
        project_coverage(binary, Path(directory), sorted(p.name for p in air.glob("*.json")),
                         len(blockers(report)))
        checks += 1

        # Malformed input stays one fatal error per unit, separate from unsupported features,
        # and does not stop independent siblings.
        duplicate = function("duplicate_ids", [inst(0, "unknown_a", 0), inst(0, "unknown_b", 0), RET])
        write(air, {"broken.json": "{", "duplicate.json": duplicate, "several.json": several()})
        report = decode(invoke(binary, air), "rejected")
        broken = blockers(report, file="broken.json")
        assert [d["code"] for d in broken] == ["JSON_SYNTAX"], broken
        assert broken[0]["category"] == "malformed_input" and broken[0]["first_error_in_unit"]
        dup = blockers(report, file="duplicate.json")
        assert [d["code"] for d in dup] == ["CANONICAL_FAILURE"], dup
        assert len(blockers(report, "NORMALIZATION_FAILURE")) == 3, "sibling unit still fully collected"
        checks += 1

        # A structurally malformed normalized unit stays one fatal error.
        bad = function("bad_type", [inst(0, "ret", 7, [dict(ty=0, val="{}")])])
        write(air, {"bad.json": bad})
        report = decode(invoke(binary, air), "rejected")
        assert len(blockers(report)) == 1 and blockers(report)[0]["category"] == "malformed_input", report
        checks += 1

        # Supported input: unchanged acceptance.
        write(air, {"ok.json": function("ok"), "caller.json": calls("caller", "ok")})
        decode(invoke(binary, air), "checked")
        checks += 1
    print(f"blocker-collection CLI regressions passed: {checks}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    run(parser.parse_args().binary.resolve(strict=True))
