#!/usr/bin/env python3
"""Normalize compiler identities and writer metadata for AIR golden comparison."""

import argparse
import json
from pathlib import Path
import runpy
import re
import sys


IDENTITY_MARKER = re.compile(r"__(anon|enum|opaque|union|struct)_[0-9]+")


def normalize(value, root=True, type_entry=False, checked_profile=None, actual=False):
    if root and checked_profile is not None:
        helpers = runpy.run_path(str(Path(__file__).with_name("normalize-generated.py")))
        profile = helpers["profile_for_air"](value)
        if actual and profile != checked_profile:
            raise ValueError("AIR profile differs from validated translation report")
        # The only schema compatibility transition is 12 (mandatory metadata) to
        # 11 (the same AIR semantic payload). Older schemas remain observable.
        if value["schema"] == 12:
            value = {k: v for k, v in value.items() if k != "profile"}
            value["schema"] = 11

    # Match Air2Lean.Anon.renameIdentities: only the root/type-entry name and
    # function references are identities. Nested names and all other data remain
    # observable, even when they contain compiler-looking markers.
    if isinstance(value, list):
        return [normalize(item, False, type_entry) for item in value]
    if not isinstance(value, dict):
        return value
    result = {}
    for key, item in value.items():
        if root and (key == "zig_version" or (key == "target_endian" and item == "little")):
            continue
        identity = key in ("func", "comptime_fn") or (key == "name" and (root or type_entry))
        if identity:
            result[key] = IDENTITY_MARKER.sub(r"__\1_N", item) if isinstance(item, str) else item
        else:
            result[key] = normalize(item, False, root and key == "types")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source")
    parser.add_argument("--check-report")
    parser.add_argument("--actual", action="store_true")
    args = parser.parse_args()
    try:
        raw = Path(args.source).read_bytes()
        helpers = runpy.run_path(str(Path(__file__).with_name("normalize-generated.py")))
        document = helpers["parse_json"](raw.decode("utf-8"))
        checked_profile = None
        if args.check_report:
            report = helpers["load_report"](args.check_report)
            checked_profile = report["metadata"]["profile"]
            if args.actual:
                matches = [entry for entry in report["air"] if entry["file"] == Path(args.source).name]
                if len(matches) != 1 or matches[0]["sha256"] != helpers["digest"](raw):
                    raise ValueError("AIR artifact does not match validated translation report")
        elif args.actual:
            raise ValueError("--actual requires a validated --check-report")
        json.dump(normalize(document, checked_profile=checked_profile, actual=args.actual),
                  sys.stdout, ensure_ascii=False, sort_keys=True, indent=2)
        sys.stdout.write("\n")
    except (ValueError, KeyError, OSError) as error:
        parser.exit(1, f"error: {error}\n")
