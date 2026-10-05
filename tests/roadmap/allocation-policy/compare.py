#!/usr/bin/env python3
"""Compare every qualified policy case; no exclusions or capped matches."""
import json
from pathlib import Path
import sys

def records(path):
    lines = [json.loads(line) for line in Path(path).read_text().splitlines()]
    if len(lines) != 10 or len({line['case'] for line in lines}) != 10:
        raise ValueError('expected ten distinct policy cases')
    return lines

if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit('usage: compare.py LEAN_JSONL ZIG_JSONL')
    if records(sys.argv[1]) != records(sys.argv[2]):
        raise SystemExit('allocator policy differential mismatch')
    print('10 exact policy comparisons; 0 exclusions; 0 capped searches')
