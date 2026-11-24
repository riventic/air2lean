#!/usr/bin/env python3
"""Compare every qualified policy case; no exclusions or capped matches."""
import json
from pathlib import Path
import sys

# Ten cases of the failure index, list and request cap; ten of the oracle and the budget.
CASES = 20
# Every oracle and budget case must be among them: a side that drops them all would still agree.
REQUIRED = ('oracle-even-attempts', 'oracle-by-size', 'oracle-attempt-and-size', 'oracle-two-rules',
            'oracle-all', 'oracle-with-list-and-cap', 'budget-held', 'budget-released', 'budget-zero',
            'budget-and-oracle')

def records(path):
    lines = [json.loads(line) for line in Path(path).read_text().splitlines()]
    names = {line['case'] for line in lines}
    if len(lines) != CASES or len(names) != CASES:
        raise ValueError(f'expected {CASES} distinct policy cases')
    if not names.issuperset(REQUIRED):
        raise ValueError('an oracle or budget case is missing')
    return lines

if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit('usage: compare.py LEAN_JSONL ZIG_JSONL')
    if records(sys.argv[1]) != records(sys.argv[2]):
        raise SystemExit('allocator policy differential mismatch')
    print(f'{CASES} exact policy comparisons; 0 exclusions; 0 capped searches')
