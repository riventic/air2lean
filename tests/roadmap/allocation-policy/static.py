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
            # No case, one case repeated, and the right number without the oracle/budget cases.
            for lines in ([], [{'case': 'duplicate'}] * COMPARE.CASES,
                          [{'case': str(i)} for i in range(COMPARE.CASES)]):
                path.write_text('\n'.join(json.dumps(line) for line in lines))
                with self.assertRaises(ValueError):
                    COMPARE.records(path)

    def test_comparison_accepts_the_distinct_cases(self):
        names = [*COMPARE.REQUIRED, *map(str, range(COMPARE.CASES - len(COMPARE.REQUIRED)))]
        lines = [{'case': name, 'outcomes': [0, 1], 'attempts': 2, 'live': 0} for name in names]
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'lines.jsonl'
            path.write_text('\n'.join(json.dumps(line) for line in lines))
            self.assertEqual(COMPARE.records(path), lines)

    def test_both_sides_run_every_oracle_and_budget_case(self):
        for fixture in ('Check.lean', 'fixture.zig'):
            source = (HERE / fixture).read_text()
            for case in COMPARE.REQUIRED:
                self.assertEqual(source.count(f'"{case}"'), 1, (fixture, case))

    def test_oracle_and_budget_have_mutants(self):
        for name in ('ignore-failure-oracle', 'ignore-budget', 'budget-ignores-live-bytes',
                     'oracle-ignores-bytes-upper-bound'):
            self.assertIn(name, MUTATIONS.MUTANTS)

    def test_differential_inputs_carry_oracle_and_budget_policies(self):
        """The lists differential (scripts/diff.sh) runs each function under generated policy
        objects; the committed inputs hold them, with the fields the harness decodes."""
        fields = {'fail_at', 'failures', 'max_bytes', 'oracle', 'budget'}
        rule_fields = {'attempt_min', 'attempt_max', 'attempt_mod', 'attempt_rem', 'bytes_min', 'bytes_max'}
        for name in ('sumRange', 'dupe', 'dupeZLen', 'evens', 'listSum'):
            rows = [json.loads(line)['args'][0]
                    for line in (ROOT / f'tests/diff/lists/inputs/{name}.jsonl').read_text().splitlines()]
            policies = [row for row in rows if isinstance(row, dict)]
            self.assertGreaterEqual(len(policies), 40, name)
            self.assertTrue(any(p.get('oracle') for p in policies), name)
            self.assertTrue(any('budget' in p for p in policies), name)
            for policy in policies:
                self.assertLessEqual(set(policy), fields, name)
                for rule in policy.get('oracle', []):
                    self.assertLessEqual(set(rule), rule_fields, name)

    def test_lean_fixture_uses_json_serializer(self):
        fixture = (HERE / 'Check.lean').read_text()
        self.assertIn('Lean.Json.mkObj', fixture)
        self.assertNotIn('s!"{{', fixture)

    def test_gate_builds_imports_first(self):
        gate = (HERE / 'check.sh').read_text()
        build = gate.index('scripts/lean-deps.py --build tests/roadmap/allocation-policy')
        for fixture in ('Check.lean', 'Oracle.lean'):
            self.assertLess(build, gate.index(f'lake env lean --run tests/roadmap/allocation-policy/{fixture}'))
        self.assertIn('AIR2LEAN_ALLOCATION_REPORT_DIR', gate)

    def test_fixtures_import_no_legacy_logic(self):
        for fixture in ('Check.lean', 'Oracle.lean'):
            self.assertNotIn('ZigLean.Sep', (HERE / fixture).read_text())

    def test_gate_runs_general_policy_checks(self):
        oracle = (HERE / 'Oracle.lean').read_text()
        for case in ('oracle-even-indices', 'list-as-oracle', 'budget', 'default-uncapped',
                     'harness-cap', 'large-dupe', 'append-loop-several-failures'):
            self.assertIn(case, oracle)

    def test_rawalloc_consults_general_oracle(self):
        source = (ROOT / 'ZigLean/Mem/Alloc.lean').read_text()
        self.assertIn('  if m.oracleDenies n then return none', source)
        basic = (ROOT / 'ZigLean/Mem/Basic.lean').read_text()
        self.assertIn('maxBytes : Nat := unboundedAllocBytes', basic)

    def test_legacy_mutation_still_targets_fail_at(self):
        source = (ROOT / 'scripts/mutate.sh').read_text()
        self.assertIn('if m.allocPolicy.maxBytes < n ∨ m.allocs ∈ m.allocPolicy.failures then return none', source)
        self.assertIn('if m.failAt = some m.allocs ∨ m.allocPolicy.maxBytes < n ∨ m.allocs ∈ m.allocPolicy.failures then return none', source)

if __name__ == '__main__':
    unittest.main()
