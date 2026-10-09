#!/usr/bin/env python3
"""I05 acceptance: one check-only run reports every independent blocker of a project.

Synthetic AIR covers each formerly first-error boundary (profile fields, cross-file profile
comparison, canonical references, the whole-program validator), source spans from the
exporter's additive provenance, and explicit per-unit/total caps. `--export-air DIR` also
checks real exports of fixture.zig made by a patched compiler (spans must point at the
marked source lines). Never runs Zig, Lake or a proof checker itself.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
spec = importlib.util.spec_from_file_location("diagnostics_cli", ROOT / "tests/roadmap/diagnostics/test_cli.py")
cli = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cli)
inst, function, calls, decode, invoke, write = (cli.inst, cli.function, cli.calls, cli.decode,
                                                cli.invoke, cli.write)
INT, VOID, NORETURN = cli.INT, cli.VOID, cli.NORETURN
RET = inst(99, "ret", 1, [dict(ty=0, val="{}")])
PROFILE = dict(name="abi64-le-v1", target_triple="x86_64-linux.4.19...6.1-gnu.2.28", pointer_bits=64,
               endian="little", abi="gnu", zig_version="0.16.0", backend="stage2_x86_64", cpu="x86_64",
               features=["sse", "sse2"], build_mode="ReleaseSafe", float_mode="per-instruction",
               error_set_bits=16, error_layout="type-table", error_tracing=False,
               export_stage="analyzed-air")


def blockers(report):
    """(code, file name, instruction) of every non-skipped diagnostic, in report order."""
    return [(d["code"], Path(d["file"]).name if d["file"] else None, d["anchor"]["instruction"])
            for d in report["diagnostics"] if d["category"] != "skipped_prerequisite"]


def shared_types(name, bits):
    """Two named structs used by a parameter each; their field widths differ across files."""
    def struct(label):
        return dict(k="struct", name=label, layout="extern", fields=[dict(name="a", ty=2, offset=0)],
                    abi_size=bits // 8, abi_align=bits // 8)
    document = function(name, [inst(0, "arg", 3, param=0), inst(1, "arg", 4, param=1), RET])
    document.update(types=[VOID, NORETURN, dict(k="int", signed=False, bits=bits, abi_size=bits // 8,
                                                abi_align=bits // 8), struct("S"), struct("T")],
                    params=[3, 4], ret=0)
    return document


def project():
    """Every class of formerly first-error boundary, plus already-collected blockers."""
    bad_profile = function("bad_profile", [inst(0, "unknown_profiled", 0), RET])
    bad_profile.update(schema=12, profile=dict(PROFILE, pointer_bits=32, build_mode="Fast"))
    mixed = function("zz_mixed")
    mixed.update(schema=10, zig_version="0.15.2")
    refs = function("refs", [inst(0, "bitcast", 0, [dict(inst=77)]),
                             inst(1, "bitcast", 0, [dict(inst=88)]), RET])
    return {
        "a-broken.json": "{",
        "bad-profile.json": bad_profile,
        "refs.json": refs,
        "unknown.json": function("unknown", [inst(0, "unknown_a", 0), inst(1, "unknown_b", 0), RET]),
        "shared-a.json": shared_types("shared_a", 32),
        "shared-b.json": shared_types("shared_b", 64),
        "main.json": calls("main", "missing_a", "missing_b", "unknown"),
        "zz-mixed.json": mixed,
    }


EXPECTED = sorted([
    ("JSON_SYNTAX", "a-broken.json", None),
    ("PROFILE_FAILURE", "bad-profile.json", None),
    ("PROFILE_FAILURE", "bad-profile.json", None),
    ("NORMALIZATION_FAILURE", "bad-profile.json", 0),
    ("CANONICAL_FAILURE", "refs.json", 0),
    ("CANONICAL_FAILURE", "refs.json", 1),
    ("NORMALIZATION_FAILURE", "unknown.json", 0),
    ("NORMALIZATION_FAILURE", "unknown.json", 1),
    ("PROGRAM_FAILURE", "shared-b.json", None),
    ("PROGRAM_FAILURE", "shared-b.json", None),
    ("CALLEE_MISSING", "main.json", 0),
    ("CALLEE_MISSING", "main.json", 1),
    ("CALLEE_BLOCKED", "main.json", 2),
    ("PROFILE_FAILURE", "zz-mixed.json", None),
    ("PROFILE_FAILURE", "zz-mixed.json", None),
], key=repr)


def check_project(report):
    found = blockers(report)
    assert sorted(found, key=repr) == EXPECTED, found
    by = {}
    for d in report["diagnostics"]:
        by.setdefault((d["code"], Path(d["file"]).name if d["file"] else None), []).append(d)
    profile = by[("PROFILE_FAILURE", "bad-profile.json")]
    assert all(not d["fatal"] and not d["first_error_in_unit"] for d in profile)
    assert any("pointer_bits 32" in d["message"] for d in profile)
    assert any("build_mode 'Fast'" in d["message"] for d in profile)
    mixed = by[("PROFILE_FAILURE", "zz-mixed.json")]
    assert sorted(d["message"].split("'")[1] for d in mixed) == ["schema", "zig_version"], mixed
    refs = by[("CANONICAL_FAILURE", "refs.json")]
    assert all(d["fatal"] and d["category"] == "malformed_input" and d["anchor"]["id_space"] == "exported"
               for d in refs)
    assert sorted("unknown instruction ref " + r in d["message"] for d in refs for r in ("77", "88")).count(True) == 2
    assert by[("JSON_SYNTAX", "a-broken.json")][0]["fatal"]
    shared = by[("PROGRAM_FAILURE", "shared-b.json")]
    assert sorted(d["message"].split("'")[1] for d in shared) == ["S", "T"], shared
    assert all(d["function"] == "shared_b" and not d["fatal"] for d in shared)
    unknown = by[("NORMALIZATION_FAILURE", "unknown.json")]
    assert all(not d["fatal"] for d in unknown)
    files = {Path(f["file"]).name: f for f in report["files"]}
    assert files["bad-profile.json"]["local_check"] == "blocked_or_rejected"
    assert files["shared-a.json"]["local_check"] == "passed"
    assert all(d["source_span"] is None for d in report["diagnostics"]), "legacy AIR has no provenance"
    assert report["capped_units"] == [] and not report["truncated"]


def coverage_command(binary, base, names):
    """The project coverage command retains the same producer blockers from one invocation."""
    for name in ("source.zig", "patch", "runtime", "toolchain", "contract"):
        (base / name).write_text("evidence")
    (base / "profile.json").write_text(json.dumps(dict(name="legacy-abi64-le", zig_version="0.16.0")))
    manifest = dict(schema=1, profile="profile.json", float_semantics="ieee", source_closure=["source.zig"],
        components=dict(compiler_patch=["patch"], runtime=["runtime"], toolchain=["toolchain"]),
        allowed_assumptions=[], roots=[dict(id="main", function="main", air=[f"air/{n}" for n in names],
        namespace="Main", prefix="", contracts=["contract"], goals=[], assumptions=[], exclusions=[])])
    (base / "project.json").write_text(json.dumps(manifest))
    out = base / "coverage.json"
    result = subprocess.run([sys.executable, str(ROOT / "scripts/project-diagnostics.py"), "check",
                             str(base / "project.json"), "--translator", str(binary), "--out", str(out)],
                            capture_output=True, text=True, timeout=120, check=False)
    assert result.returncode == 1, result.stderr
    report = json.loads(out.read_text())
    producer = report["root_checks"][0]["producer"]
    assert producer is not None, report["root_checks"][0]
    found = [(code, (Path(file).name if file else None), instruction) for code, file, instruction in blockers(producer)]
    assert sorted(found, key=repr) == EXPECTED, found


def spans(binary, air):
    """Exporter provenance becomes statement/declaration spans, including inlined scopes."""
    src = dict(file="src/spans.zig", module="root", decl_line=10)
    inner = dict(file="src/helper.zig", module="root", decl_line=40)
    body = [inst(0, "dbg_stmt", 0, line=2, column=5),
            inst(1, "unknown_a", 0),
            inst(2, "dbg_inline_block", 0, src=inner, body=[
                inst(3, "dbg_stmt", 0, line=3, column=9),
                inst(4, "unknown_b", 0),
                inst(5, "br", 0, [dict(ty=0, val="{}")], target=2)]),
            inst(6, "dbg_stmt", 0, line=4, column=3),
            inst(7, "block", 0, body=[inst(8, "unknown_c", 0),
                                      inst(9, "br", 0, [dict(ty=0, val="{}")], target=7)]),
            inst(10, "unknown_d", 0, unsupported=True),
            RET]
    located = function("located", body)
    located["src"] = src
    # A legacy-shaped unit next to it: no provenance, no span.
    write(air, {"located.json": located, "plain.json": function("plain", [inst(0, "unknown_e", 0), RET])})
    report = decode(invoke(binary, air), "rejected")
    located_d = [d for d in report["diagnostics"] if d["function"] == "located"]
    def span_of(fragment):
        hits = [d for d in located_d if fragment in d["message"]]
        assert len(hits) == 1, (fragment, located_d)
        return hits[0]["source_span_status"], hits[0]["source_span"]
    assert span_of("unknown_a") == ("statement", dict(file="src/spans.zig", module="root", line=11, column=5))
    assert span_of("unknown_b") == ("statement", dict(file="src/helper.zig", module="root", line=42, column=9))
    assert span_of("unknown_c") == ("statement", dict(file="src/spans.zig", module="root", line=13, column=3))
    # The exported-ID marker resolves through the exported map.
    assert span_of("unknown_d") == ("statement", dict(file="src/spans.zig", module="root", line=13, column=3))
    skipped = [d for d in located_d if d["code"] == "PREREQUISITE_SKIPPED"]
    assert skipped and all(d["source_span_status"] == "declaration" and
                           d["source_span"] == dict(file="src/spans.zig", module="root", line=10, column=None)
                           for d in skipped), skipped
    plain = [d for d in report["diagnostics"] if d["function"] == "plain"]
    assert plain and all(d["source_span"] is None and d["source_span_status"] == "unavailable_in_AIR" for d in plain)
    # An inlined body without its callee's provenance stays unresolved; it is never guessed.
    body[2] = dict(body[2]); body[2].pop("src")
    write(air, {"located.json": located})
    report = decode(invoke(binary, air), "rejected")
    inner_d = [d for d in report["diagnostics"] if "unknown_b" in d["message"]]
    assert len(inner_d) == 1 and inner_d[0]["source_span"] is None, inner_d


def caps(binary, air):
    """A noisy unit cannot starve a sibling: per-unit caps are explicit and accounted."""
    noisy = function("noisy", [inst(i, f"unknown_{i}", 0) for i in range(10)] + [RET])
    write(air, {"a-noisy.json": noisy, "b-quiet.json": function("quiet", [inst(0, "unknown_q", 0), RET]),
                "c-caller.json": calls("caller", "absent_c")})
    report = decode(invoke(binary, air, "--unit-diagnostic-limit", "3", "--diagnostic-limit", "8"), "rejected")
    assert report["caps"] == dict(diagnostics=8, diagnostics_per_unit=3, payload_bytes=1024 * 1024,
                                  message_chars=2048, files=256, input_bytes=64 * 1024 * 1024,
                                  function_name_chars=1024, dependency_chain_names=257), report["caps"]
    names = [Path(d["file"]).name for d in report["diagnostics"]]
    assert names.count("a-noisy.json") == 3 and "b-quiet.json" in names, names
    # A per-unit cap truncates only that unit: later program-phase blockers still report.
    assert any(d["code"] == "CALLEE_MISSING" and d["dependency_chain"] == ["caller", "absent_c"]
               for d in report["diagnostics"]), report["diagnostics"]
    assert [Path(u["file"]).name for u in report["capped_units"]] == ["a-noisy.json"]
    assert report["capped_units"][0]["dropped"] == 8, report["capped_units"]
    assert report["truncated"] and not report["complete"]
    default = decode(invoke(binary, air), "rejected")
    assert default["caps"]["diagnostics_per_unit"] == 64 and default["capped_units"] == []
    for flags in (("--unit-diagnostic-limit", "0"), ("--unit-diagnostic-limit", "4097"),
                  ("--unit-diagnostic-limit", "x"), ("--unit-diagnostic-limit",)):
        rejected = decode(invoke(binary, air, *flags), "rejected")
        assert rejected["diagnostics"][0]["code"] == "CLI_ARGUMENTS" and rejected["diagnostics"][0]["fatal"]


def provenance_invariance(binary, base):
    """Source provenance never changes generated Lean or semantic fingerprints."""
    def document(decl_line, column):
        inner = dict(file="src/helper.zig", module="root", decl_line=decl_line + 30)
        doc = function("moved", [inst(0, "dbg_stmt", 0, line=2, column=column),
                                 inst(1, "dbg_inline_block", 0, src=inner, body=[
                                     inst(2, "br", 0, [dict(ty=0, val="{}")], target=1)]), RET])
        doc["src"] = dict(file="src/moved.zig", module="root", decl_line=decl_line)
        return doc
    outputs = []
    for label, doc in (("near", document(10, 5)), ("far", document(200, 9)), ("none", function("moved", [
            inst(0, "dbg_stmt", 0, line=2), inst(1, "dbg_inline_block", 0, body=[
                inst(2, "br", 0, [dict(ty=0, val="{}")], target=1)]), RET]))):
        air = base / f"provenance-{label}"
        air.mkdir()
        write(air, {"moved.json": doc})
        out, sidecar = base / f"{label}.lean", base / f"{label}.json"
        result = subprocess.run([str(binary), str(air), "-o", str(out), "--namespace", "Moved",
                                 "--source-map-json", str(sidecar)], capture_output=True, text=True, timeout=60)
        assert result.returncode == 0, result.stderr
        canonical = [f["canonical"] for f in json.loads(sidecar.read_text())["functions"]]
        outputs.append((out.read_bytes(), canonical))
    assert outputs[0] == outputs[1] == outputs[2], "source provenance changed generation or fingerprints"


def exported(binary, air_root):
    """Real patched-compiler exports: every span points at the line marked `SPAN:`."""
    source = (HERE / "fixture.zig").read_text().splitlines()
    for air in sorted(p for p in Path(air_root).iterdir() if p.is_dir()):
        report = decode(invoke(binary, air), "rejected")
        located = [d for d in report["diagnostics"] if d["category"] != "skipped_prerequisite"]
        assert located, report
        lines = set()
        for d in located:
            span = d["source_span"]
            if d["phase"] == "profile":
                # A host outside the model ABI scope (e.g. aarch64-linux) is a profile blocker;
                # it is located at its function's declaration line.
                assert d["source_span_status"] == "declaration" and span["column"] is None, d
                assert source[span["line"] - 1].lstrip().startswith(("export fn", "fn", "inline fn")), d
                continue
            assert span is not None and d["source_span_status"] == "statement", d
            assert span["file"] == "fixture.zig" and span["module"], span
            text = source[span["line"] - 1]
            assert "SPAN:" in text, (d["code"], span, text)
            assert span["column"] is not None and 1 <= span["column"] <= len(text), span
            lines.add(span["line"])
        marked = {n + 1 for n, text in enumerate(source) if "SPAN:" in text}
        assert lines == marked, (air.name, sorted(lines), sorted(marked))
        print(f"{air.name}: {len(located)} located blockers on lines {sorted(lines)}")


def run(binary, export_air=None):
    with tempfile.TemporaryDirectory(prefix="air2lean-i05-") as directory:
        base = Path(directory)
        air = base / "air"
        air.mkdir()
        documents = project()
        write(air, documents)
        first = invoke(binary, air)
        report = decode(first, "rejected")
        check_project(report)
        assert invoke(binary, air).stdout == first.stdout, "deterministic report bytes"
        coverage_command(binary, base, sorted(documents))
        spans(binary, air)
        caps(binary, air)
        provenance_invariance(binary, base)
        checks = 5
        if export_air is not None:
            exported(binary, export_air)
            checks += 1
        else:
            print("real-export span check not run (supply --export-air)")
    print(f"I05 diagnostic acceptance passed: {checks}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("air2lean", type=Path)
    parser.add_argument("--export-air", type=Path,
                        help="directory of per-version AIR dirs exported from fixture.zig")
    args = parser.parse_args()
    run(args.air2lean.resolve(), args.export_air)


if __name__ == "__main__":
    main()
