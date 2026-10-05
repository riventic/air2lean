#!/usr/bin/env python3
"""Keep profile provenance while comparing generated semantics against legacy goldens.

The check pipeline calls `report` only after the real translator succeeds. Consumers
verify the report's full generated hash before permitting metadata-only normalization.
This receipt records checked inputs; it is not a semantic preservation theorem.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

PREFIX = b"-- air2lean-profile: "
VERSIONS = {"0.14.1", "0.15.2", "0.16.0"}
RAW_FIELDS = {"name", "target_triple", "pointer_bits", "endian", "abi", "zig_version",
              "backend", "cpu", "features", "build_mode", "float_mode", "error_set_bits",
              "error_layout", "error_tracing", "export_stage"}


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def parse_json(text):
    return json.loads(text, object_pairs_hook=unique_object)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def profile_for_air(doc):
    """Check metadata again when binding a real translation receipt to its AIR files."""
    if not isinstance(doc, dict):
        raise ValueError("AIR file must be an object")
    schema, version = doc.get("schema"), doc.get("zig_version")
    if (type(schema) is not int or not 1 <= schema <= 12 or
            not isinstance(version, str) or version not in VERSIONS):
        raise ValueError("unsupported AIR schema or zig_version")
    if "target_endian" in doc and doc["target_endian"] != "little":
        raise ValueError("target_endian is outside the little-endian memory model")
    if schema < 12:
        if "profile" in doc:
            raise ValueError("profile metadata requires AIR schema 12")
        return dict(name="legacy-abi64-le", schema=schema, zig_version=version,
                    target_triple="unverified", pointer_bits=64, endian="little", abi="unverified",
                    backend="unverified", cpu="unverified", features=[], build_mode="unverified",
                    float_mode="unverified", error_set_bits=16, error_layout="reference-model",
                    error_tracing=None, export_stage="unverified")
    p = doc.get("profile")
    if not isinstance(p, dict) or set(p) != RAW_FIELDS:
        raise ValueError("schema 12 requires exactly the supported profile fields")
    string_fields = RAW_FIELDS - {"pointer_bits", "error_set_bits", "error_tracing", "features"}
    if any(not isinstance(p[k], str) or not p[k] for k in string_fields):
        raise ValueError("profile string fields must not be empty or malformed")
    if (p["name"] != "abi64-le-v1" or p["zig_version"] != version or
            type(p["pointer_bits"]) is not int or p["pointer_bits"] != 64 or
            p["endian"] != "little" or type(p["error_set_bits"]) is not int or p["error_set_bits"] != 16):
        raise ValueError("incompatible target profile")
    triple = p["target_triple"].split("-")
    if (len(triple) != 3 or triple[2].split(".")[0] != p["abi"] or
            (triple[0], triple[1].split(".")[0]) not in {("x86_64", "linux"), ("aarch64", "macos")}):
        raise ValueError("target triple is outside the supported model ABI scope")
    fs = p["features"]
    if (not isinstance(fs, list) or any(not isinstance(f, str) or not f for f in fs) or
            len(fs) != len(set(fs)) or type(p["error_tracing"]) is not bool):
        raise ValueError("invalid profile features or error_tracing")
    if (p["build_mode"] not in {"Debug", "ReleaseSafe", "ReleaseFast", "ReleaseSmall"} or
            p["float_mode"] != "per-instruction" or p["error_layout"] != "type-table" or
            p["export_stage"] != "analyzed-air"):
        raise ValueError("unsupported build/profile claim")
    return dict(p, schema=schema)


# Audited Zig 0.15.2/0.16.0 x86_64 baseline models, including sse2's sse dependency.
BASELINE_FEATURES = {"64bit", "cmov", "cx8", "fxsr", "idivq_to_divl", "macrofusion",
                     "mmx", "nopl", "slow_3ops_lea", "slow_incdec", "sse", "sse2",
                     "vzeroupper", "x87"}


def fresh_linux_profile(doc, expected_version):
    """Validate one fresh Linux/baseline ReleaseSafe export, with a caller-pinned version."""
    profile = profile_for_air(doc)
    if doc.get("schema") != 12 or doc.get("zig_version") != expected_version:
        raise ValueError("fresh AIR requires current schema 12 and matching version")
    arch, os_version, _ = profile["target_triple"].split("-")
    if (doc.get("target_endian") != "little" or arch != "x86_64" or
            os_version.split(".")[0] != "linux" or profile["abi"] not in {"gnu", "musl"} or
            profile["backend"] != "stage2_llvm" or profile["cpu"] != "x86_64" or
            set(profile["features"]) != BASELINE_FEATURES or
            profile["build_mode"] != "ReleaseSafe" or profile["error_tracing"] is not False):
        raise ValueError("fresh AIR profile differs from Linux/baseline ReleaseSafe flags")
    return profile


def split_generated(data, required=False):
    first, newline, body = data.partition(b"\n")
    if not first.startswith(PREFIX):
        if required:
            raise ValueError("generated output has no first-line profile record")
        return None, data
    if not newline:
        raise ValueError("profile record must end with a newline")
    metadata = parse_json(first[len(PREFIX):].decode("utf-8"))
    if (not isinstance(metadata, dict) or set(metadata) != {"profile", "float_semantics", "correspondence"} or
            not isinstance(metadata["float_semantics"], str) or
            metadata["float_semantics"] not in {"ieee", "compiler-rt"} or metadata["correspondence"] != "model"):
        raise ValueError("unsupported generated profile record")
    p = metadata["profile"]
    if not isinstance(p, dict) or set(p) != RAW_FIELDS | {"schema"}:
        raise ValueError("malformed normalized profile record")
    raw = {k: v for k, v in p.items() if k != "schema"}
    doc = dict(schema=p["schema"], zig_version=p["zig_version"])
    if p["schema"] == 12:
        doc["profile"] = raw
    if profile_for_air(doc) != p:
        raise ValueError("generated profile differs from the supported profile contract")
    return metadata, body


def load_report(path):
    report = parse_json(Path(path).read_text(encoding="utf-8"))
    if (not isinstance(report, dict) or report.get("format") != "air2lean-check-report-v1" or
            report.get("profile_validation") != "translator-and-input-match"):
        raise ValueError("unsupported check report")
    return report


def checked_generated(path, report_path):
    data = Path(path).read_bytes()
    report = load_report(report_path)
    metadata, body = split_generated(data, required=True)
    if digest(data) != report["generated_sha256"] or metadata != report["metadata"]:
        raise ValueError("generated artifact does not match validated check report")
    return data, body, metadata


def write_report(generated, air_dir, output):
    data = Path(generated).read_bytes()
    metadata, body = split_generated(data, required=True)
    inputs = []
    paths = sorted(Path(air_dir).glob("*.json"))
    if not paths:
        raise ValueError("no AIR files to bind to generated profile")
    for path in paths:
        raw = path.read_bytes()
        doc = parse_json(raw.decode("utf-8"))
        if profile_for_air(doc) != metadata["profile"]:
            raise ValueError(f"{path}: AIR profile differs from generated profile")
        inputs.append(dict(file=path.name, sha256=digest(raw)))
    report = dict(format="air2lean-check-report-v1", profile_validation="translator-and-input-match",
                  metadata=metadata, generated_sha256=digest(data), body_sha256=digest(body), air=inputs)
    Path(output).write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")


def compare(baseline, generated, report):
    _, current, _ = checked_generated(generated, report)
    _, expected = split_generated(Path(baseline).read_bytes())
    if current != expected:
        raise ValueError(f"{baseline} differs from the translator output (generated semantics changed)")


def check_tracked(path, generated, report):
    """Reject staged, working-tree and untracked body changes before replacement."""
    _, _, metadata = checked_generated(generated, report)
    def git(*args):
        return subprocess.run(["git", *args], check=True, capture_output=True).stdout
    committed = git("show", f"HEAD:{path}")
    _, committed_body = split_generated(committed)
    for label, content in [("index", git("show", f":{path}")), ("working tree", Path(path).read_bytes())]:
        if content == committed:
            continue
        header, body = split_generated(content, required=True)
        if header != metadata or body != committed_body:
            raise ValueError(f"{path}: {label} has changes beyond the validated profile header")


def check_proof_status(examples):
    allowed = {f"Proofs/{ex[0].upper() + ex[1:]}/Gen.lean" for ex in examples.split()}
    result = subprocess.run(["git", "status", "--porcelain", "-z", "--untracked-files=all", "--", "Proofs"],
                            check=True, capture_output=True)
    for entry in result.stdout.split(b"\0"):
        if not entry:
            continue
        status, path = entry[:2], entry[3:].decode("utf-8")
        if status == b"??" or b"R" in status or b"C" in status or path not in allowed:
            raise ValueError(f"{path}: unrelated or untracked proof change in CI")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    status = sub.add_parser("proof-status")
    status.add_argument("examples")
    report = sub.add_parser("report")
    report.add_argument("generated"); report.add_argument("air_dir"); report.add_argument("output")
    for command in ("compare", "tracked"):
        p = sub.add_parser(command)
        p.add_argument("baseline"); p.add_argument("generated"); p.add_argument("report")
    args = parser.parse_args()
    try:
        if args.command == "proof-status":
            check_proof_status(args.examples)
        elif args.command == "report":
            write_report(args.generated, args.air_dir, args.output)
        elif args.command == "compare":
            compare(args.baseline, args.generated, args.report)
        else:
            check_tracked(args.baseline, args.generated, args.report)
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"error: {error}\n")


if __name__ == "__main__":
    main()
