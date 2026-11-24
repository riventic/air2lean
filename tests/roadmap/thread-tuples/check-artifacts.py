#!/usr/bin/env python3
"""Source freshness and exact checked AIR inventory of every exported version; no compiler
invocation."""
import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parent
manifest = json.loads((root / "provenance.json").read_text())
expected = manifest["source_sha256"]
if not isinstance(expected, str) or re.fullmatch(r"[0-9a-f]{64}", expected) is None:
    raise SystemExit("invalid source_sha256 in provenance.json")
if hashlib.sha256((root / "thread_tuples.zig").read_bytes()).hexdigest() != expected:
    raise SystemExit("stale thread tuple source; regenerate AIR and refresh provenance")
versions = manifest["versions"]
if not versions or set(manifest["air_sha256"]) != set(versions):
    raise SystemExit("provenance versions differ from the versions of its AIR hashes")
if {p.name for p in (root / "air").iterdir()} != set(versions):
    raise SystemExit("checked thread tuple AIR version directories differ from provenance")
expected_names = {"thread_tuples." + name for name in manifest["functions"]}
expected_names.update(manifest.get("stdlib_functions", []))
for version in versions:
    hashes = manifest["air_sha256"][version]
    paths = list((root / "air" / version).glob("*.json"))
    if set(hashes) != {path.name for path in paths}:
        raise SystemExit(f"{version}: checked thread tuple AIR filename inventory differs from provenance")
    actual = []
    for path in paths:
        expected_air_hash = hashes.get(path.name)
        if not isinstance(expected_air_hash, str) or re.fullmatch(r"[0-9a-f]{64}", expected_air_hash) is None:
            raise SystemExit(f"{version}/{path.name}: missing or invalid AIR hash")
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected_air_hash:
            raise SystemExit(f"{version}/{path.name}: stale checked AIR hash")
        data = json.loads(path.read_text())
        actual.append(data["name"])
        if data["schema"] != manifest["air"]["schema"]:
            raise SystemExit(f"{version}/{path.name}: wrong schema")
        if data["zig_version"] != version:
            raise SystemExit(f"{version}/{path.name}: wrong zig_version")
        if data.get("target_endian") != "little":
            raise SystemExit(f"{version}/{path.name}: wrong target_endian")
    if set(actual) != expected_names or len(actual) != len(expected_names):
        raise SystemExit(f"{version}: checked thread tuple AIR function inventory differs from provenance")
print(f"thread tuple source and checked AIR inventory passed ({', '.join(versions)})")
