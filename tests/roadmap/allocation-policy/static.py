#!/usr/bin/env python3
"""Offline tests of mutation anchors and comparison accounting; never invokes compilers."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def module(name):
    spec = importlib.util.spec_from_file_location(name, HERE / f'{name}.py')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result

MUTATIONS = module('mutations')
COMPARE = module('compare')

class PolicyChecks(unittest.TestCase):
    def test_mutants_change_exactly_one_real_boundary(self):
        original = (ROOT / 'tests/diff/common.zig').read_text()
        for name in MUTATIONS.MUTANTS:
            mutant = MUTATIONS.mutated(original, name)
            self.assertNotEqual(original, mutant)
            before, after = MUTATIONS.MUTANTS[name]
            self.assertEqual(original.replace(before, after, 1), mutant)

    def test_missing_mutation_anchor_is_error(self):
        for name in MUTATIONS.MUTANTS:
            with self.assertRaises(ValueError):
                MUTATIONS.mutated('', name)

    def test_comparison_rejects_missing_or_duplicate_cases(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'lines.jsonl'
            for lines in ([], [{'case': 'duplicate'}] * 10):
                path.write_text('\n'.join(json.dumps(line) for line in lines))
                with self.assertRaises(ValueError):
                    COMPARE.records(path)

    def test_comparison_accepts_ten_distinct_cases(self):
        lines = [{'case': str(i), 'outcomes': [0, 1], 'attempts': 2, 'live': 0} for i in range(10)]
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'lines.jsonl'
            path.write_text('\n'.join(json.dumps(line) for line in lines))
            self.assertEqual(COMPARE.records(path), lines)

    def test_lean_fixture_uses_json_serializer(self):
        fixture = (HERE / 'Check.lean').read_text()
        self.assertIn('Lean.Json.mkObj', fixture)
        self.assertNotIn('s!"{{', fixture)
        self.assertNotIn('\\n', fixture)

    def test_gate_builds_imported_separation_library(self):
        gate = (HERE / 'check.sh').read_text()
        self.assertIn('lake build ZigLean ZigLean.Sep.Alloc', gate)
        self.assertLess(gate.index('lake build ZigLean ZigLean.Sep.Alloc'),
                        gate.index('lake env lean tests/roadmap/allocation-policy/Check.lean'))
        self.assertIn('AIR2LEAN_ALLOCATION_REPORT_DIR', gate)

    def test_legacy_mutation_still_targets_fail_at(self):
        source = (ROOT / 'scripts/mutate.sh').read_text()
        self.assertIn('if m.allocPolicy.maxBytes < n ∨ m.allocs ∈ m.allocPolicy.failures then return none', source)
        self.assertIn('if m.failAt = some m.allocs ∨ m.allocPolicy.maxBytes < n ∨ m.allocs ∈ m.allocPolicy.failures then return none', source)

if __name__ == '__main__':
    unittest.main()
