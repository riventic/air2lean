#!/usr/bin/env python3
"""Fail before invoking tools when the external production source has changed."""
import hashlib
import json
import pathlib
import re
import sys

if len(sys.argv) != 2:
    raise SystemExit("usage: check-source.py FLOW_TIME_SOURCE")
try:
    manifest = json.loads((pathlib.Path(__file__).parent / "provenance.json").read_text())
    expected = manifest["production_sha256"]
except (OSError, ValueError, KeyError, TypeError) as error:
    raise SystemExit(f"Flow provenance invalid: {error}") from error
if not isinstance(expected, str) or re.fullmatch(r"[0-9a-f]{64}", expected) is None:
    raise SystemExit("Flow provenance invalid: production_sha256 must be a 64-digit lowercase hexadecimal SHA-256")
source = pathlib.Path(sys.argv[1])
try:
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
except OSError as error:
    raise SystemExit(f"Flow source unavailable: {error}") from error
if digest != expected:
    raise SystemExit(f"Flow source changed: expected {expected}, got {digest}; regenerate AIR and recheck proofs")
print(f"Flow source matches recorded SHA-256: {digest}")
