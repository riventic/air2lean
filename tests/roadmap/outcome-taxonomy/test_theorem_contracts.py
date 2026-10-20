#!/usr/bin/env python3
"""Explicit outcome declarations are bounded by audited conclusions, never by samples."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]


def load(name):
    spec = importlib.util.spec_from_file_location('outcome_contract_' + name, ROOT / 'scripts' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


outcomes = load('outcomes')
claims = load('claims')
FIXTURE = json.loads((ROOT / 'tests/roadmap/claims/fixture-report.json').read_text())


def extraction(returns=('valid',), *, total=True, concurrent=False):
    return {'schema_version': 1, 'status': 'computed', 'returns': list(returns),
            'unexcluded': [] if total else ['divergence', 'stack_overflow'],
            'scope': 'all_outcomes' if total else 'conditional_on_return',
            'concurrent': concurrent, 'precision': 'constructor upper bound', 'reason': None}


class TheoremContractTests(unittest.TestCase):
    def judge(self, declared, audit=None):
        return outcomes.theorem_contract('total_correctness', declared, extraction() if audit is None else audit)

    def test_narrower_than_theorem_fails_without_samples(self):
        result = self.judge(['valid'], extraction(('valid', 'error_return')))
        self.assertEqual(result['status'], 'rejected')
        self.assertEqual(result['missing'], ['error_return'])
        self.assertIn('narrower than the theorem', result['reason'])

    def test_equal_contract_verified(self):
        self.assertEqual(self.judge(['valid'])['status'], 'verified')

    def test_wider_contract_is_an_under_claim(self):
        result = self.judge(['valid', 'error_return'])
        self.assertEqual(result['status'], 'under_claim')
        self.assertEqual(result['extra'], ['error_return'])

    def test_error_return_does_not_become_panic(self):
        result = self.judge(['error_return'], extraction(('error_return',)))
        self.assertEqual(result['status'], 'verified')
        self.assertEqual(result['theorem_admits'], ['error_return'])

    def test_partial_postcondition_does_not_prove_termination(self):
        result = outcomes.theorem_contract('partial_correctness', ['valid'], extraction(total=False))
        self.assertEqual(result['status'], 'rejected')
        self.assertEqual(result['missing'], ['divergence', 'stack_overflow'])

    def test_concurrent_values_keep_the_schedule_class(self):
        result = self.judge(['valid'], extraction(concurrent=True))
        self.assertEqual(result['status'], 'rejected')
        self.assertEqual(result['missing'], ['nondeterministic_valid'])

    def test_unsupported_opaque_missing_or_malformed_extract_fails_closed(self):
        bad = [None, {}, {**extraction(), 'status': 'unsupported', 'reason': 'opaque return predicate'},
               {**extraction(), 'returns': ['valid', 'valid']}, {**extraction(), 'returns': ['unknown']},
               {**extraction(), 'unexcluded': ['unknown']}, {**extraction(), 'concurrent': None},
               {**extraction(), 'scope': 'conditional_on_return'}, {**extraction(), 'schema_version': 99}]
        for audit in bad:
            with self.subTest(audit=audit):
                result = outcomes.theorem_contract('total_correctness', ['valid'], audit)
                self.assertEqual(result['status'], 'rejected')

    def test_defaults_are_labelled_strength_relative(self):
        result = outcomes.theorem_contract('partial_correctness', None, extraction(total=False))
        self.assertEqual(result['status'], 'strength_default')
        self.assertEqual(result['scope'], 'conditional_on_return')
        self.assertEqual(result['unexcluded'], ['divergence', 'stack_overflow'])


class ClaimGateTests(unittest.TestCase):
    def check(self, declared, audit, counts=None):
        report = copy.deepcopy(FIXTURE)
        theorems = claims.audited_theorems(report)
        theorem = theorems['ClaimFixture.fret_total']
        theorem['statement']['outcomes'] = audit
        goal = {'theorem': theorem['name'], 'strength': 'total_correctness', 'domain': 'all',
                'outcomes': {'admits': declared}}
        return claims.check_goal(goal, theorems, counts, definition='ClaimFixture.ret')

    def test_claim_gate_rejects_narrower_even_with_clean_samples(self):
        result = self.check(['valid'], extraction(('valid', 'error_return')), {'valid': 10})
        self.assertEqual(result['status'], 'rejected')
        self.assertEqual(result['theorem_outcome_contract']['missing'], ['error_return'])

    def test_claim_gate_accepts_equal_and_reports_wider(self):
        self.assertEqual(self.check(['valid'], extraction())['status'], 'accepted')
        result = self.check(['valid', 'error_return'], extraction())
        self.assertEqual(result['status'], 'accepted')
        self.assertEqual(result['theorem_outcome_contract']['status'], 'under_claim')

    def test_claim_gate_refuses_unsupported(self):
        result = self.check(['valid'], {'status': 'unsupported', 'reason': 'opaque return predicate'})
        self.assertEqual(result['status'], 'rejected')
        self.assertIn('opaque', result['reason'])

    def test_samples_can_refute_a_theorem_bound_contract(self):
        result = self.check(['valid'], extraction(), {'error_return': 1})
        self.assertEqual(result['status'], 'rejected')
        self.assertIn('observed outcomes outside the contract', result['reason'])


if __name__ == '__main__':
    unittest.main()
