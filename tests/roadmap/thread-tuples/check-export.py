#!/usr/bin/env python3
"""Validate fresh tuple AIR inventory and profiles; no compiler invocation."""
import argparse
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parent
HELPERS = runpy.run_path(str(ROOT.parents[2] / "scripts/normalize-generated.py"))


def check_export(directory, adapter=False):
    paths = sorted(Path(directory).glob("*.json"))
    if not paths:
        raise ValueError("AIR export function inventory is empty")
    data = [HELPERS["parse_json"](p.read_text()) for p in paths]
    profiles = []
    for doc in data:
        profile = HELPERS["profile_for_air"](doc)
        if doc.get("schema") not in (11, 12):
            raise ValueError("AIR export has a wrong schema")
        if doc.get("target_endian") != "little":
            raise ValueError("AIR export has a wrong target endianness")
        if profile["schema"] == 12:
            # The shared validator checks triple shape and equality with profile.abi.
            # Zig's inferred Linux target includes an OS version range and may use musl.
            arch, os_version, _ = profile["target_triple"].split("-")
            if (arch != "x86_64" or os_version.split(".")[0] != "linux" or
                    profile["abi"] not in {"gnu", "musl"} or
                    profile["cpu"] != "x86_64" or profile["build_mode"] != "ReleaseSafe" or
                    profile["error_tracing"] is not False):
                raise ValueError("AIR export profile differs from the explicit Linux/baseline ReleaseSafe flags")
        profiles.append(profile)
    if any(profile != profiles[0] for profile in profiles):
        raise ValueError("AIR export has mixed profiles")
    version = profiles[0]["zig_version"]
    if adapter:
        if version != "0.16.0":
            raise ValueError("adapter AIR has a wrong version")
        expected = {"thread_adapter_contract." + name for name in
                    ("mutableCapture", "strongCapture", "weakCapture", "sliceWorker")}
    else:
        manifest = HELPERS["parse_json"]((ROOT / "provenance.json").read_text())
        expected = {"thread_tuples." + n for n in manifest["functions"]}
        expected.update(manifest["stdlib_functions"])
        if version != "0.16.0":
            expected.remove("thread_tuples.groupMixed")
    names = [doc["name"] for doc in data]
    if set(names) != expected or len(names) != len(expected):
        raise ValueError("AIR export function inventory differs from the required source and std callees")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--adapter", action="store_true")
    args = parser.parse_args()
    try:
        check_export(args.directory, args.adapter)
    except (ValueError, KeyError, OSError, TypeError) as error:
        parser.exit(1, f"error: {error}\n")
    print("thread tuple fresh AIR inventory and profiles passed")


if __name__ == "__main__":
    main()
