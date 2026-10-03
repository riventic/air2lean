#!/usr/bin/env python3
"""Normalize compiler identities and writer metadata for AIR golden comparison."""

import json
import re
import sys


IDENTITY_MARKER = re.compile(r"__(anon|enum|opaque|union|struct)_[0-9]+")


def normalize(value, root=True, type_entry=False):
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
    with open(sys.argv[1], encoding="utf-8") as source:
        document = json.load(source)
    json.dump(normalize(document), sys.stdout, ensure_ascii=False, sort_keys=True, indent=2)
    sys.stdout.write("\n")
