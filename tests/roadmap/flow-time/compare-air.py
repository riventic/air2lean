#!/usr/bin/env python3
"""Compare the complete AIR export structurally; no semantic fields are erased."""
import json
import pathlib
import sys

if len(sys.argv) != 3:
    raise SystemExit("usage: compare-air.py EXPECTED_DIR ACTUAL_DIR")
expected, actual = map(pathlib.Path, sys.argv[1:])
names = {"flow_time.timestamp32.json", "flow_time.timestamp64.json"}
for directory in (expected, actual):
    if {path.name for path in directory.glob("*.json")} != names:
        raise SystemExit(f"Flow AIR must contain exactly both timestamp entry points: {directory}")
for name in sorted(names):
    if json.loads((expected / name).read_text()) != json.loads((actual / name).read_text()):
        raise SystemExit(f"Flow AIR changed: {name}; regenerate translation and recheck proofs")
print("Flow AIR matches both checked production-source entry points")
