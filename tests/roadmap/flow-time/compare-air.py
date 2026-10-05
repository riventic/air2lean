#!/usr/bin/env python3
"""Compare Flow AIR, allowing only a receipt-bound schema 12 profile transition."""
import argparse
from functools import cache
import json
from pathlib import Path
import runpy

NAMES = {"flow_time.timestamp32.json", "flow_time.timestamp64.json"}
MAX_BYTES = 4 * 1024 * 1024
# Zig 0.16.0 Target.Cpu.Model.baseline(x86_64, linux), with feature dependencies.
PROFILE = {
    "name": "abi64-le-v1", "target_triple": "x86_64-linux.5.10...6.19-musl",
    "pointer_bits": 64, "endian": "little", "abi": "musl", "zig_version": "0.16.0",
    "backend": "stage2_llvm", "cpu": "x86_64",
    "features": ["64bit", "cmov", "cx8", "fxsr", "idivq_to_divl", "macrofusion", "mmx",
                 "nopl", "slow_3ops_lea", "slow_incdec", "sse", "sse2", "vzeroupper", "x87"],
    "build_mode": "ReleaseSafe", "float_mode": "per-instruction", "error_set_bits": 16,
    "error_layout": "type-table", "error_tracing": False, "export_stage": "analyzed-air",
}


@cache
def helpers():
    return runpy.run_path(str(Path(__file__).resolve().parents[3] / "scripts/normalize-generated.py"))


def read(path):
    with Path(path).open("rb") as stream:
        data = stream.read(MAX_BYTES + 1)
    if len(data) > MAX_BYTES:
        raise ValueError(f"Flow artifact exceeds byte bound: {path}")
    return data


def document(data):
    return helpers()["parse_json"](data.decode("utf-8"))


def canonical(value):
    # Keep JSON types observable (Python's True == 1 must not hide a mutation).
    return json.dumps(value, sort_keys=True, ensure_ascii=False, allow_nan=False)


def inventory(directory):
    directory = Path(directory)
    if {path.name for path in directory.glob("*.json")} != NAMES:
        raise ValueError(f"Flow AIR must contain exactly both timestamp entry points: {directory}")
    return {name: read(directory / name) for name in sorted(NAMES)}


def fresh_documents(raw):
    docs = {name: document(data) for name, data in raw.items()}
    expected = dict(PROFILE, schema=12)
    for name, doc in docs.items():
        profile = helpers()["profile_for_air"](doc)
        if canonical(profile) != canonical(expected) or doc.get("target_endian") != "little":
            raise ValueError(f"Flow fresh AIR has an unqualified profile: {name}")
    for name, doc in docs.items():
        if doc.get("name") != name.removesuffix(".json"):
            raise ValueError(f"Flow fresh AIR has a changed function name: {name}")
    return docs


def compare(expected, actual, generated=None, report=None, validate_fresh=False):
    baseline, raw = inventory(expected), inventory(actual)
    if validate_fresh:
        fresh_documents(raw)
        return
    if generated is None and report is None:
        for name in sorted(NAMES):
            if canonical(document(baseline[name])) != canonical(document(raw[name])):
                raise ValueError(f"Flow AIR changed: {name}; regenerate translation and recheck proofs")
        return
    if generated is None or report is None:
        raise ValueError("fresh comparison requires both --generated and --check-report")
    docs = fresh_documents(raw)
    # Bound files before calling the shared profile receipt checker.
    read(generated)
    receipt = document(read(report))
    _, body, metadata = helpers()["checked_generated"](generated, report)
    if (metadata["float_semantics"] != "ieee" or
            canonical(metadata["profile"]) != canonical(dict(PROFILE, schema=12)) or
            receipt.get("body_sha256") != helpers()["digest"](body)):
        raise ValueError("Flow generated profile/body differs from validated receipt")
    if set(receipt) != {"format", "profile_validation", "metadata", "generated_sha256", "body_sha256", "air"}:
        raise ValueError("Flow receipt has unsupported fields")
    entries = receipt.get("air")
    if not isinstance(entries, list) or len(entries) != len(NAMES):
        raise ValueError("Flow receipt must bind exactly both AIR files")
    bound = {}
    for entry in entries:
        if (not isinstance(entry, dict) or set(entry) != {"file", "sha256"} or
                not isinstance(entry["file"], str) or entry["file"] in bound):
            raise ValueError("Flow receipt has a malformed or duplicate AIR entry")
        bound[entry["file"]] = entry["sha256"]
    if bound != {name: helpers()["digest"](value) for name, value in raw.items()}:
        raise ValueError("Flow raw AIR does not match validated receipt")
    for name, doc in docs.items():
        historic = document(baseline[name])
        if (not isinstance(historic, dict) or type(historic.get("schema")) is not int or
                historic["schema"] != 11 or "profile" in historic or
                historic.get("zig_version") != "0.16.0" or historic.get("target_endian") != "little"):
            raise ValueError(f"Flow historical AIR envelope changed: {name}")
        # No name/version/endian/identity/body/type/layout normalization is permitted.
        semantic = {key: value for key, value in doc.items() if key != "profile"}
        semantic["schema"] = 11
        if canonical(semantic) != canonical(historic):
            raise ValueError(f"Flow AIR changed: {name}; regenerate translation and recheck proofs")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("expected"); parser.add_argument("actual")
    parser.add_argument("--validate-fresh", action="store_true")
    parser.add_argument("--generated"); parser.add_argument("--check-report")
    args = parser.parse_args()
    if args.validate_fresh and (args.generated or args.check_report):
        parser.error("--validate-fresh cannot take generated artifacts")
    try:
        compare(args.expected, args.actual, args.generated, args.check_report, args.validate_fresh)
    except (ValueError, KeyError, TypeError, OSError, UnicodeError, RecursionError) as error:
        parser.exit(1, f"error: {error}\n")
    print("Flow fresh profiles validated" if args.validate_fresh else
          "Flow AIR matches both checked production-source entry points")


if __name__ == "__main__":
    main()
