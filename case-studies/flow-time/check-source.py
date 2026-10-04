#!/usr/bin/env python3
"""Fail before invoking tools when the external production source has changed."""
import hashlib
import pathlib
import sys

if len(sys.argv) != 2:
    raise SystemExit("usage: check-source.py FLOW_TIME_SOURCE")
source = pathlib.Path(sys.argv[1])
try:
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
except OSError as error:
    raise SystemExit(f"Flow source unavailable: {error}") from error
expected = (pathlib.Path(__file__).parent / "source.sha256").read_text().strip()
if digest != expected:
    raise SystemExit(f"Flow source changed: expected {expected}, got {digest}; regenerate AIR and recheck proofs")
print(f"Flow source matches recorded SHA-256: {digest}")
