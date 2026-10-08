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
}


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

    def test_names_do_not_drive_classification(self):
        report = copy.deepcopy(FIXTURE)
        for theorem in report['theorems']:
            if theorem['name'] == 'ClaimFixture.diverge_partial':
                theorem['name'] = 'ClaimFixture.total_correctness_guaranteed_return'
        theorems = classified(report)
        self.assertEqual(theorems['ClaimFixture.total_correctness_guaranteed_return']['derived_strength'],
                         'partial_correctness')

    def test_only_exact_kernel_names(self):
        for head in ('TotalTriple', 'Foo.TotalTriple', 'Zig.TotalTriple.toPartial', 'Zig.Conc.Total.EventuallyReturns'):
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

    def test_asm_closure_carries_fault_premise(self):
        """S7: a no-panic or guaranteed-return claim over an inline-asm opaque carries ASM-03
        (the allowlist entry's fault condition); a report without the closure is rejected."""
        report = copy.deepcopy(FIXTURE)
        for theorem in report['theorems']:
            if theorem['name'] in ('ClaimFixture.ret_total', 'ClaimFixture.panic_pure'):
                theorem['opaque_dependencies'] = ['Asm.airAsm_3653072158']
        theorems = classified(report)
        self.assertEqual(theorems['ClaimFixture.ret_total']['premises'], ['ASM-01', 'ASM-03'])
        self.assertEqual(theorems['ClaimFixture.panic_pure']['premises'], ['ASM-01'])
        self.assertEqual(theorems['ClaimFixture.ret_partial']['premises'], [])
        goal = claims.check_goal({'theorem': 'ClaimFixture.ret_total', 'strength': 'total_correctness',
                                  'domain': 'all'}, theorems)
        self.assertEqual((goal['status'], goal['premises']), ('accepted', ['ASM-01', 'ASM-03']))
        del report['theorems'][0]['opaque_dependencies']
        name = report['theorems'][0]['name']
        goal = claims.check_goal({'theorem': name, 'strength': 'safety', 'domain': 'all'}, classified(report))
        self.assertEqual(goal['status'], 'rejected')
        self.assertIn('opaque_dependencies', goal['reason'])

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
        self.report.write_text(json.dumps(FIXTURE))

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

    def check(self, goals):
        result = self.cli('check', self.manifest(goals), '--assurance', self.report)
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
        report = copy.deepcopy(FIXTURE)
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
        self.report.write_text(json.dumps(FIXTURE))
        code, _, _ = self.check([('ClaimFixture.ret_total', 'proved')])
        self.assertEqual(code, 2)

    def test_report_command(self):
        result = self.cli('report', '--assurance', self.report)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(json.loads(result.stdout)['theorems']), len(EXPECTED))


if __name__ == '__main__':
    unittest.main()
