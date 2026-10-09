#!/usr/bin/env python3
"""Claim-strength regressions. fixture-report.json holds conclusion shapes extracted by
tools/Assurance.lean from Fixture.lean; check.sh regenerates and compares them."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
SCRIPT = ROOT / 'scripts' / 'claims.py'
SPEC = importlib.util.spec_from_file_location('claims', SCRIPT)
claims = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(claims)
FIXTURE = json.loads((Path(__file__).parent / 'fixture-report.json').read_text())
AUDIT_SPEC = importlib.util.spec_from_file_location('assumptions', ROOT / 'scripts' / 'assumptions.py')
assumptions = importlib.util.module_from_spec(AUDIT_SPEC)
AUDIT_SPEC.loader.exec_module(assumptions)

EXPECTED = {
    'ClaimFixture.diverge_partial': ('correct-if-returned', 'partial_correctness'),
    'ClaimFixture.ret_partial': ('correct-if-returned', 'partial_correctness'),
    'ClaimFixture.ret_total': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.premise_total': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.ret_returns': ('guaranteed-return', 'safety'),
    'ClaimFixture.ret_run': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.ret_some': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.ret_pure_ok': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.panic_run': ('unclassified', None),
    'ClaimFixture.panic_some': ('unclassified', None),
    'ClaimFixture.panic_pure': ('unclassified', None),
    'ClaimFixture.diverge_not_total': ('unclassified', None),
    'ClaimFixture.wrapped_total': ('unclassified', None),
    'ClaimFixture.partial_and_returns': ('unclassified', None),
    'ClaimFixture.exit_within': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.exit_within_total': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.spin_no_run': ('unclassified', None),
    'ClaimFixture.spin_not_within': ('unclassified', None),
    'ClaimFixture.countdown_eventually': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.countdown_bounded': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.countdown_under': ('guaranteed-return-under-premise', None),
    'ClaimFixture.stuck_under_false': ('guaranteed-return-under-premise', None),
    'ClaimFixture.stuck_not_total': ('unclassified', None),
}
BOUNDS = {'ClaimFixture.exit_within': {'unit': 'loop_body_runs'},
          'ClaimFixture.countdown_bounded': {'unit': 'scheduler_turns'}}


def classified(report):
    return {t['name']: t for t in claims.classify(report)['theorems']}


def pure(monad, value):
    return {'head': 'Pure.pure', 'args': [{'head': monad}, value]}


class ClassifyTests(unittest.TestCase):
    def test_fixture_classification_from_types(self):
        theorems = classified(FIXTURE)
        self.assertEqual(set(theorems), set(EXPECTED))
        for name, (klass, strength) in EXPECTED.items():
            with self.subTest(name=name):
                self.assertEqual((theorems[name]['claim_class'], theorems[name]['derived_strength']),
                                 (klass, strength))

    def test_three_claims_are_distinct(self):
        theorems = classified(FIXTURE)
        self.assertEqual(theorems['ClaimFixture.diverge_partial']['claims'], ['no-panic', 'correct-if-returned'])
        self.assertEqual(theorems['ClaimFixture.ret_returns']['claims'], ['no-panic', 'guaranteed-return'])
        self.assertEqual(theorems['ClaimFixture.ret_total']['claims'],
                         ['no-panic', 'correct-if-returned', 'guaranteed-return'])

    def test_bounds_are_reported_only_for_bounded_heads(self):
        theorems = classified(FIXTURE)
        for name in EXPECTED:
            with self.subTest(name=name):
                self.assertEqual(theorems[name]['bound'], BOUNDS.get(name))
        # A bounded return is a guaranteed return; the bound is additional.
        self.assertEqual(theorems['ClaimFixture.exit_within']['claims'],
                         ['no-panic', 'correct-if-returned', 'guaranteed-return'])

    def test_premise_return_is_not_an_unconditional_claim(self):
        theorems = classified(FIXTURE)
        for name in ('ClaimFixture.countdown_under', 'ClaimFixture.stuck_under_false'):
            with self.subTest(name=name):
                self.assertEqual(theorems[name]['claims'], ['guaranteed-return-under-premise'])
                self.assertIsNone(theorems[name]['derived_strength'])

    def test_names_do_not_drive_classification(self):
        report = copy.deepcopy(FIXTURE)
        for theorem in report['theorems']:
            if theorem['name'] == 'ClaimFixture.diverge_partial':
                theorem['name'] = 'ClaimFixture.total_correctness_guaranteed_return'
        theorems = classified(report)
        self.assertEqual(theorems['ClaimFixture.total_correctness_guaranteed_return']['derived_strength'],
                         'partial_correctness')

    def test_only_exact_kernel_names(self):
        for head in ('TotalTriple', 'Foo.TotalTriple', 'Zig.TotalTriple.toPartial', 'EventuallyReturns',
                     'Zig.EventuallyReturns', 'Zig.Conc.EventuallyReturnsUnder', 'Zig.TotalTripleWithin.toTotal',
                     'Zig.Conc.Total.ReturnsWithin.eventually'):
            self.assertEqual(claims.claims_of({'head': head}), frozenset(), head)
        self.assertEqual(claims.claims_of({'head': 'Zig.TTriple'}), {'no-panic', 'correct-if-returned'})

    def test_malformed_shapes_support_nothing(self):
        for shape in (None, 3, {}, {'head': None}, {'head': 'Eq'}, {'head': 'Eq', 'args': 'x'},
                      {'head': 'Eq', 'args': [{'head': 'Option.some'}]},
                      {'head': 'Eq', 'args': [{'head': 'Option.some', 'args': [{'head': 'Except.error'}]}]},
                      {'head': 'Eq', 'args': [{'head': 'Pure.pure'}, {'head': 'Pure.pure'}]},
                      # `pure` without its monad, in `Option` around an error, or in an unknown monad.
                      {'head': 'Eq', 'args': [{'head': 'Pure.pure'}]},
                      {'head': 'Eq', 'args': [pure('Option', {'head': 'Except.error'})]},
                      {'head': 'Eq', 'args': [pure('Option', {'head': None})]},
                      {'head': 'Eq', 'args': [pure('Id', {'head': 'Prod.mk'})]}):
            self.assertEqual(claims.claims_of(shape), frozenset(), shape)

    def test_old_or_failed_reports_are_rejected(self):
        old = copy.deepcopy(FIXTURE)
        del old['theorems'][0]['conclusion']
        with self.assertRaisesRegex(ValueError, 'regenerate'):
            claims.classify(old)
        with self.assertRaisesRegex(ValueError, 'completed audit'):
            claims.classify({'schema_version': 1, 'status': 'error', 'error': 'build failed'})
        duplicate = copy.deepcopy(FIXTURE)
        duplicate['theorems'].append(duplicate['theorems'][0])
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            claims.classify(duplicate)


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        (self.base / 'profile.json').write_text(json.dumps({'name': 'legacy-abi64-le', 'zig_version': '0.16.0'}))
        self.report = self.base / 'assurance.json'
        # A report bound (H1) to this checkout's revision and to one artifact digest.
        self.olean = self.base / 'Fixture.olean'
        self.olean.write_bytes(b'compiled fixture')
        self.fixture = dict(FIXTURE, freshness={
            'revision': assumptions.git_revision(), 'lake_trace_check': {'modules': [], 'status': 'up-to-date'},
            'artifacts': [{'module': 'Fixture', 'olean': str(self.olean),
                           'olean_sha256': assumptions.file_sha256(self.olean), 'source': None, 'source_sha256': None}]})
        self.report.write_text(json.dumps(self.fixture))

    def manifest(self, goals):
        manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee', 'source_closure': ['a.zig'],
                    'components': {'compiler_patch': ['p'], 'runtime': ['r'], 'toolchain': ['t']},
                    'allowed_assumptions': [],
                    'roots': [{'id': 'root', 'function': 'f', 'air': ['f.json'], 'namespace': 'ClaimFixture',
                               'prefix': '', 'contracts': ['Fixture.lean'],
                               'goals': [{'theorem': t, 'strength': s, 'domain': 'fixture'} for t, s in goals],
                               'assumptions': [], 'exclusions': []}]}
        path = self.base / 'project.json'
        path.write_text(json.dumps(manifest))
        return path

    def cli(self, *args):
        return subprocess.run([sys.executable, str(SCRIPT), *map(str, args)],
                              capture_output=True, text=True, timeout=30)

    def check(self, goals, flags=('--allow-dirty',)):
        # The checkout under test may have uncommitted changes; refusal tests pass no flag.
        result = self.cli('check', self.manifest(goals), '--assurance', self.report, *flags)
        return result.returncode, json.loads(result.stdout) if result.stdout else None, result.stderr

    def test_matching_and_weaker_goals_accepted(self):
        code, result, err = self.check([('ClaimFixture.ret_total', 'total_correctness'),
                                        ('ClaimFixture.ret_total', 'partial_correctness'),
                                        ('ClaimFixture.ret_run', 'total_correctness'),
                                        ('ClaimFixture.diverge_partial', 'partial_correctness'),
                                        ('ClaimFixture.diverge_partial', 'safety'),
                                        ('ClaimFixture.ret_returns', 'safety')])
        self.assertEqual(code, 0, err)
        self.assertEqual(result['status'], 'pass')
        self.assertTrue(all(g['status'] == 'accepted' for g in result['roots'][0]['goals']))

    def test_bounded_and_concurrent_returns_accepted(self):
        code, result, err = self.check([('ClaimFixture.exit_within', 'total_correctness'),
                                        ('ClaimFixture.countdown_eventually', 'total_correctness'),
                                        ('ClaimFixture.countdown_bounded', 'total_correctness')])
        self.assertEqual(code, 0, err)
        goals = result['roots'][0]['goals']
        self.assertEqual([g['bound'] for g in goals],
                         [{'unit': 'loop_body_runs'}, None, {'unit': 'scheduler_turns'}])

    def test_premise_dependent_return_cannot_meet_unconditional_goals(self):
        for name in ('ClaimFixture.countdown_under', 'ClaimFixture.stuck_under_false'):
            for strength in ('total_correctness', 'partial_correctness', 'safety'):
                with self.subTest(name=name, strength=strength):
                    code, result, _ = self.check([(name, strength)])
                    self.assertEqual(code, 1)
                    goal = result['roots'][0]['goals'][0]
                    self.assertEqual((goal['status'], goal['claim_class']),
                                     ('rejected', 'guaranteed-return-under-premise'))
                    self.assertIn('premise', goal['reason'])

    def test_diverging_program_cannot_be_declared_bounded(self):
        # Only the refutation `spin_not_within` exists for the spinning loop; it states no claim.
        for name in ('ClaimFixture.spin_not_within', 'ClaimFixture.spin_no_run', 'ClaimFixture.stuck_not_total'):
            with self.subTest(name=name):
                code, result, _ = self.check([(name, 'total_correctness')])
                self.assertEqual(code, 1)
                self.assertEqual(result['roots'][0]['goals'][0]['derived_strength'], None)

    def test_diverging_program_cannot_be_declared_total(self):
        code, result, err = self.check([('ClaimFixture.diverge_partial', 'total_correctness')])
        self.assertEqual(code, 1)
        goal = result['roots'][0]['goals'][0]
        self.assertEqual((goal['status'], goal['derived_strength']), ('rejected', 'partial_correctness'))
        self.assertIn('exceeds', goal['reason'])
        self.assertIn('diverge_partial', err)

    def test_overstated_goals_rejected(self):
        for name, strength in [('ClaimFixture.ret_returns', 'total_correctness'),
                               ('ClaimFixture.ret_returns', 'partial_correctness'),
                               ('ClaimFixture.ret_partial', 'total_correctness'),
                               ('ClaimFixture.wrapped_total', 'total_correctness'),
                               ('ClaimFixture.partial_and_returns', 'total_correctness'),
                               ('ClaimFixture.panic_run', 'safety'),
                               ('ClaimFixture.panic_some', 'safety'),
                               ('ClaimFixture.panic_pure', 'safety'),
                               ('ClaimFixture.diverge_not_total', 'safety'),
                               ('ClaimFixture.ret_total', 'resource_bound'),
                               ('ClaimFixture.ret_total', 'correspondence')]:
            with self.subTest(name=name, strength=strength):
                code, result, _ = self.check([(name, strength)])
                self.assertEqual(code, 1)
                self.assertEqual(result['roots'][0]['goals'][0]['status'], 'rejected')

    def test_one_overstated_goal_fails_the_manifest(self):
        code, result, _ = self.check([('ClaimFixture.ret_total', 'total_correctness'),
                                      ('ClaimFixture.ret_partial', 'total_correctness')])
        self.assertEqual(code, 1)
        self.assertEqual([g['status'] for g in result['roots'][0]['goals']], ['accepted', 'rejected'])

    def test_missing_and_unaudited_theorems_rejected(self):
        code, result, _ = self.check([('ret_total', 'safety')])
        self.assertEqual(code, 1)
        self.assertIn('absent', result['roots'][0]['goals'][0]['reason'])
        report = copy.deepcopy(self.fixture)
        for theorem in report['theorems']:
            theorem['allowed'] = False
        self.report.write_text(json.dumps(report))
        code, result, _ = self.check([('ClaimFixture.ret_total', 'safety')])
        self.assertEqual(code, 1)
        self.assertIn('violations', result['roots'][0]['goals'][0]['reason'])

    def test_invalid_inputs_exit_2(self):
        self.report.write_text(json.dumps({'schema_version': 1, 'status': 'error', 'error': 'x'}))
        code, _, err = self.check([('ClaimFixture.ret_total', 'safety')])
        self.assertEqual(code, 2)
        self.assertIn('claims error', err)
        self.report.write_text(json.dumps(self.fixture))
        code, _, _ = self.check([('ClaimFixture.ret_total', 'proved')])
        self.assertEqual(code, 2)

    def test_report_must_be_fresh_for_this_tree(self):
        goal = [('ClaimFixture.ret_total', 'total_correctness')]
        code, result, err = self.check(goal)
        self.assertEqual(code, 0, err)
        self.assertEqual(result['freshness']['artifacts'], 1)
        cases = {'no freshness binding': {k: v for k, v in self.fixture.items() if k != 'freshness'},
                 'revision': dict(self.fixture, freshness=dict(self.fixture['freshness'],
                                                               revision={'head': '0' * 40, 'tracked_dirty': False})),
                 'trace check': dict(self.fixture, freshness=dict(self.fixture['freshness'], lake_trace_check={}))}
        for reason, report in cases.items():
            with self.subTest(reason=reason):
                self.report.write_text(json.dumps(report))
                code, _, err = self.check(goal)
                self.assertEqual(code, 2)
                self.assertIn(reason, err)
        self.report.write_text(json.dumps(self.fixture))
        self.olean.write_bytes(b'recompiled fixture')
        code, _, err = self.check(goal)
        self.assertEqual(code, 2)
        self.assertIn('stale', err)

    def test_dirty_report_needs_explicit_recorded_permission(self):
        goal = [('ClaimFixture.ret_total', 'total_correctness')]
        dirty = copy.deepcopy(self.fixture)
        dirty['freshness']['revision']['tracked_dirty'] = True
        self.report.write_text(json.dumps(dirty))
        code, _, err = self.check(goal, flags=())
        self.assertEqual(code, 2)
        self.assertIn('--allow-dirty', err)
        code, result, err = self.check(goal)
        self.assertEqual(code, 0, err)
        self.assertEqual((result['freshness']['tracked_dirty'], result['freshness']['dirty_allowed']), (True, True))

    def test_report_command(self):
        result = self.cli('report', '--assurance', self.report)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(json.loads(result.stdout)['theorems']), len(EXPECTED))


if __name__ == '__main__':
    unittest.main()
