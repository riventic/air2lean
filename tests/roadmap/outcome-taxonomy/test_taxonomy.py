#!/usr/bin/env python3
"""V06 outcome-taxonomy regressions: shared taxonomy, absence refusal in claims and coverage.

Offline: synthetic diff summaries and the checked-in claim fixture report only."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


outcomes = load('outcomes', ROOT / 'scripts' / 'outcomes.py')
project = load('project', ROOT / 'scripts' / 'project.py')
report = load('diff_report', ROOT / 'scripts' / 'diff-report.py')
CLAIMS = ROOT / 'scripts' / 'claims.py'
FIXTURE = ROOT / 'tests' / 'roadmap' / 'claims' / 'fixture-report.json'
O = outcomes.Outcome


def case(status, kind=None, schedule=None, function='root'):
    row = {'schema': 1, 'example': 'example', 'function': function, 'status': status}
    if kind is not None:
        row['model_kind'] = kind
    if schedule is not None:
        row['schedule'] = schedule
    return row


def search(status='witness', no_result=False):
    return {'status': status, 'runs': 4, 'cap': 4, 'fuel': 100, 'saw_no_result': no_result}


class TaxonomyTests(unittest.TestCase):
    def test_every_diff_kind_and_model_status_is_mapped(self):
        # Drift guard: a new diff-report observation kind must be placed in the taxonomy.
        self.assertEqual(set(outcomes.DIFF_KINDS), {k.value for k in report.Kind})
        comparison_only = {report.Status.MISMATCH, report.Status.HOST, report.Status.INPUT_FAILURE,
                           report.Status.NATIVE_HARNESS_FAILURE, report.Status.SKIPPED}
        self.assertEqual(set(outcomes.DIFF_STATUSES), {s.value for s in report.Status if s not in comparison_only})

    def test_names_agree_with_project_preflight_outcomes(self):
        self.assertLessEqual({o.value for o in O} - {O.VALID.value}, set(project.OUTCOMES))

    def test_case_classification(self):
        expect = [
            (case('value_match', 'value'), {O.VALID}),
            (case('value_match', 'value', search()), {O.NONDETERMINISTIC_VALID}),
            (case('error_return_match', 'error_return'), {O.ERROR_RETURN}),
            (case('panic_match', 'model_panic'), {O.PANIC}),
            (case('illegal_exclusion', 'illegal'), {O.ILLEGAL}),
            (case('unspecified_exclusion', 'unspecified'), {O.UNSPECIFIED}),
            (case('mismatch', 'deadlock'), {O.DEADLOCK}),
            (case('stack_overflow_exclusion', 'stack_overflow'), {O.STACK_OVERFLOW}),
            (case('search_cap', 'value', search('capped')), {O.NONDETERMINISTIC_VALID, O.SEARCH_CAP}),
            (case('value_match', 'value', search('witness', True)), {O.NONDETERMINISTIC_VALID, O.DIVERGENCE}),
            (case('bounded_no_result', 'bounded_no_result', search('bounded', True)), {O.DIVERGENCE}),
            (case('value_match'), {O.VALID}),  # status-only rows
            (case('native_harness_failure', 'native_harness_failure'), set()),
            (case('value_match', 'future_kind'), {O.VALID, O.UNSUPPORTED}),  # unknown kinds fail closed
        ]
        for row, expected in expect:
            with self.subTest(row=row):
                self.assertEqual(outcomes.case_outcomes(row), expected)

    def verdict(self, claim, *rows):
        return outcomes.absence(claim, outcomes.count(rows))

    def test_error_returns_never_refuse_no_panic(self):
        for claim in outcomes.ABSENCE_CLAIMS:
            self.assertEqual(self.verdict(claim, case('error_return_match', 'error_return'),
                                          case('value_match', 'value', search()))['status'], 'not_refuted')

    def test_incomplete_and_failure_outcomes_refuse(self):
        refusing = {
            'search cap': case('search_cap', 'value', search('capped')),
            'fuel-bounded no result': case('bounded_no_result', 'bounded_no_result', search('bounded', True)),
            'witness beside no-result branch': case('value_match', 'value', search('witness', True)),
            'unspecified / timer': case('unspecified_exclusion', 'unspecified'),
            'panic': case('panic_match', 'model_panic'),
            'illegal': case('illegal_exclusion', 'illegal'),
            'deadlock': case('mismatch', 'deadlock'),
            'stack overflow': case('stack_overflow_exclusion', 'stack_overflow'),
        }
        for name, row in refusing.items():
            for claim in outcomes.ABSENCE_CLAIMS:
                with self.subTest(name=name, claim=claim):
                    verdict = self.verdict(claim, case('value_match', 'value'), row)
                    self.assertEqual(verdict['status'], 'refused')
                    self.assertIn('refused', verdict['reason'])
        self.assertEqual(outcomes.absence('no-panic', {O.UNSUPPORTED.value: 1})['status'], 'refused')


class ClaimsEvidenceTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.base = Path(temp.name)
        (self.base / 'profile.json').write_text(json.dumps({'name': 'legacy-abi64-le', 'zig_version': '0.16.0'}))
        self.diff = self.base / 'diff.json'

    def run_check(self, rows, strength='total_correctness', function='example.root', complete=True, diff=True):
        manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee', 'source_closure': ['a.zig'],
                    'components': {'compiler_patch': ['p'], 'runtime': ['r'], 'toolchain': ['t']},
                    'allowed_assumptions': [],
                    'roots': [{'id': 'root', 'function': function, 'air': ['f.json'], 'namespace': 'ClaimFixture',
                               'prefix': '', 'contracts': ['Fixture.lean'],
                               'goals': [{'theorem': 'ClaimFixture.ret_total', 'strength': strength, 'domain': 'all'}],
                               'assumptions': [], 'exclusions': []}]}
        path = self.base / 'project.json'
        path.write_text(json.dumps(manifest))
        self.diff.write_text(json.dumps({'schema': 1, 'complete': complete}))
        Path(str(self.diff) + '.jsonl').write_text(''.join(json.dumps(r) + '\n' for r in rows))
        extra = ['--diff', str(self.diff)] if diff else []
        result = subprocess.run([sys.executable, str(CLAIMS), 'check', str(path), '--assurance', str(FIXTURE), *extra],
                                capture_output=True, text=True, timeout=30)
        return result.returncode, json.loads(result.stdout) if result.stdout else None, result.stderr

    def test_clean_and_error_return_evidence_accepted(self):
        code, result, err = self.run_check([case('value_match', 'value'), case('error_return_match', 'error_return'),
                                            case('value_match', 'value', search())])
        self.assertEqual(code, 0, err)
        self.assertEqual(result['roots'][0]['outcomes'],
                         {'valid': 1, 'nondeterministic_valid': 1, 'error_return': 1})

    def test_capped_or_timer_evidence_rejects_goal(self):
        for row in (case('search_cap', 'value', search('capped')), case('unspecified_exclusion', 'unspecified'),
                    case('bounded_no_result', 'bounded_no_result', search('bounded', True))):
            for strength in ('safety', 'partial_correctness', 'total_correctness'):
                with self.subTest(row=row, strength=strength):
                    code, result, err = self.run_check([case('value_match', 'value'), row], strength)
                    self.assertEqual(code, 1, err)
                    goal = result['roots'][0]['goals'][0]
                    self.assertEqual(goal['status'], 'rejected')
                    self.assertTrue(goal['blocking'])

    def test_other_functions_and_unbound_roots_do_not_count(self):
        code, _, err = self.run_check([case('value_match', 'value'), case('search_cap', 'value', search('capped'), 'other')])
        self.assertEqual(code, 0, err)
        code, result, err = self.run_check([case('search_cap', 'value', search('capped'))], function='root')
        self.assertEqual(code, 0, err)
        self.assertIsNone(result['roots'][0]['outcomes'])

    def test_without_diff_type_evidence_alone_decides(self):
        code, result, err = self.run_check([case('search_cap', 'value', search('capped'))], diff=False)
        self.assertEqual(code, 0, err)
        self.assertIsNone(result['roots'][0]['outcomes'])

    def test_incomplete_summary_is_an_input_error(self):
        code, _, err = self.run_check([case('value_match', 'value')], complete=False)
        self.assertEqual(code, 2, err)


if __name__ == '__main__':
    unittest.main()
