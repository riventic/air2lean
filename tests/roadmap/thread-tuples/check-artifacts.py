#!/usr/bin/env python3
"""Source freshness and exact checked AIR inventory; no compiler invocation."""
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
air = root / "air" / manifest["air"]["zig_version"]
paths = list(air.glob("*.json"))
if set(manifest["air_sha256"]) != {path.name for path in paths}:
    raise SystemExit("checked thread tuple AIR filename inventory differs from provenance")
expected_names = {"thread_tuples." + name for name in manifest["functions"]}
expected_names.update(manifest.get("stdlib_functions", []))
actual = []
for path in paths:
    expected_air_hash = manifest["air_sha256"].get(path.name)
    if not isinstance(expected_air_hash, str) or re.fullmatch(r"[0-9a-f]{64}", expected_air_hash) is None:
        raise SystemExit(f"{path.name}: missing or invalid AIR hash")
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected_air_hash:
        raise SystemExit(f"{path.name}: stale checked AIR hash")
    data = json.loads(path.read_text())
    actual.append(data["name"])
    for key in ["schema", "zig_version"]:
        if data[key] != manifest["air"][key]:
            raise SystemExit(f"{path.name}: wrong {key}")
    if data.get("target_endian") != "little":
        raise SystemExit(f"{path.name}: wrong target_endian")
if set(actual) != expected_names or len(actual) != len(expected_names):
    raise SystemExit("checked thread tuple AIR function inventory differs from provenance")
print("thread tuple source and checked AIR inventory passed")
