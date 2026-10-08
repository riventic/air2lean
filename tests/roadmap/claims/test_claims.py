#!/usr/bin/env python3
"""Claim-strength regressions. fixture-report.json holds statement structures extracted by
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
HEADS = claims.load_heads()
EVENTUALLY = 'Zig.Conc.Total.EventuallyReturns'

# (claim class, strength after witness caps); classification ignores the root binding.
EXPECTED = {
    # Partial correctness of a program that never returns: no liveness witness, so safety only.
    'ClaimFixture.diverge_partial': ('correct-if-returned', 'safety'),
    'ClaimFixture.ret_partial': ('correct-if-returned', 'partial_correctness'),
    'ClaimFixture.ret_total': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.premise_total': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.ret_returns': ('guaranteed-return', 'safety'),
    'ClaimFixture.ret_run': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.ret_run_ground': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.ret_some': ('guaranteed-return', 'total_correctness'),
    'ClaimFixture.ret_pure_ok': ('guaranteed-return', 'total_correctness'),
    # A thread triple without a non-vacuity witness.
    'ClaimFixture.ret_thread': ('correct-if-returned', 'safety'),
    'ClaimFixture.panic_run': ('unclassified', None),
    'ClaimFixture.panic_some': ('unclassified', None),
    'ClaimFixture.panic_pure': ('unclassified', None),
    'ClaimFixture.diverge_not_total': ('unclassified', None),
    'ClaimFixture.wrapped_total': ('unclassified', None),
    'ClaimFixture.partial_and_returns': ('unclassified', None),
    # Not a registered head on this branch (codex/roadmap-batch8 registers concurrent heads).
    'ClaimFixture.countdown_total': ('unclassified', None),
    'ClaimFixture.diverge_partial.nonvacuous': ('unclassified', None),
    'ClaimFixture.ret_total.nonvacuous': ('unclassified', None),
    'ClaimFixture.ret_partial.nonvacuous': ('unclassified', None),
    'ClaimFixture.ret_partial.returns': ('unclassified', None),
    'ClaimFixture.premise_total.nonvacuous': ('unclassified', None),
    'ClaimFixture.ret_returns.nonvacuous': ('unclassified', None),
}


def classified(report, heads=None):
    return {t['name']: t for t in claims.classify(report, heads)['theorems']}


def theorems_of(report):
    return {t['name']: t for t in report['theorems']}


def pure(monad, value):
    return {'head': 'Pure.pure', 'args': [{'head': monad}, value]}


def registry_with_eventually():
    """The registry plus the fixture's own concurrent head, as a batch8-style head would plug in."""
    statement = theorems_of(FIXTURE)['ClaimFixture.countdown_total']['statement']
    return dict(HEADS, **{EVENTUALLY: {'module': statement['head']['module'], 'fingerprint': statement['head']['fingerprint'],
                                       'claims': list(claims.CLAIMS), 'program': 3, 'state': [4]}})


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
            if theorem['name'] == 'ClaimFixture.ret_returns':
                theorem['name'] = 'ClaimFixture.total_correctness_guaranteed_return'
        theorems = classified(report)
        self.assertEqual(theorems['ClaimFixture.total_correctness_guaranteed_return']['derived_strength'], 'safety')

    def test_heads_are_registered_declarations(self):
        theorem = theorems_of(FIXTURE)['ClaimFixture.ret_total']
        self.assertEqual(claims.claims_of(theorem, HEADS), claims.EXACT_SUCCESS)
        for change in ({'name': 'TotalTriple'}, {'name': 'Foo.TotalTriple'}, {'name': 'Zig.TotalTriple.toPartial'},
                       {'name': EVENTUALLY}, {'module': 'tests.roadmap.claims.Fixture'}, {'fingerprint': '0' * 32}):
            with self.subTest(change=change):
                spoof = copy.deepcopy(theorem)
                spoof['statement']['head'].update(change)
                self.assertEqual(claims.claims_of(spoof, HEADS), frozenset())
        # The audit's declaration graph must agree on the head's module as well.
        self.assertEqual(claims.claims_of(theorem, HEADS, {'Zig.TotalTriple': {'module': 'Elsewhere'}}), frozenset())
        thread = theorems_of(FIXTURE)['ClaimFixture.ret_thread']
        self.assertEqual(claims.claims_of(thread, HEADS), {'no-panic', 'correct-if-returned'})

    def test_registry_matches_extracted_heads(self):
        seen = claims.head_identities(FIXTURE)
        for name, entry in HEADS.items():
            with self.subTest(head=name):
                self.assertEqual((seen[name]['module'], seen[name]['fingerprint']), (entry['module'], entry['fingerprint']))

    def test_registry_modules_are_imported_by_the_extractor(self):
        source = (ROOT / 'tools/Assurance.lean').read_text()
        for entry in HEADS.values():
            self.assertIn(f'import {entry["module"]}\n', source)

    def test_invalid_registry_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / 'heads.json'
            for heads in ({'Eq': HEADS['Zig.Triple']}, {'X': dict(HEADS['Zig.Triple'], fingerprint='short')},
                          {'X': dict(HEADS['Zig.Triple'], claims=['everything'])}, {'X': dict(HEADS['Zig.Triple'], program=-1)}):
                path.write_text(json.dumps({'schema_version': 1, 'heads': heads}))
                with self.assertRaises(ValueError):
                    claims.load_heads(path)

    def test_malformed_shapes_support_nothing(self):
        eq = {'statement': {'head': {'name': 'Eq', 'module': 'Init.Prelude'}}}
        for shape in (None, 3, {}, {'head': None}, {'head': 'Eq'}, {'head': 'Eq', 'args': 'x'},
                      {'head': 'Eq', 'args': [{'head': 'Option.some'}]},
                      {'head': 'Eq', 'args': [{'head': 'Option.some', 'args': [{'head': 'Except.error'}]}]},
                      {'head': 'Eq', 'args': [{'head': 'Pure.pure'}, {'head': 'Pure.pure'}]},
                      # `pure` without its monad, in `Option` around an error, or in an unknown monad.
                      {'head': 'Eq', 'args': [{'head': 'Pure.pure'}]},
                      {'head': 'Eq', 'args': [pure('Option', {'head': 'Except.error'})]},
                      {'head': 'Eq', 'args': [pure('Option', {'head': None})]},
                      {'head': 'Eq', 'args': [pure('Id', {'head': 'Prod.mk'})]}):
            self.assertEqual(claims.claims_of(dict(eq, conclusion=shape), HEADS), frozenset(), shape)
        self.assertEqual(claims.claims_of({'conclusion': {'head': 'Eq'}}, HEADS), frozenset())

    def test_old_or_failed_reports_are_rejected(self):
        for field in ('conclusion', 'statement'):
            old = copy.deepcopy(FIXTURE)
            del old['theorems'][0][field]
            with self.assertRaisesRegex(ValueError, 'regenerate'):
                claims.classify(old)
        with self.assertRaisesRegex(ValueError, 'completed audit'):
            claims.classify({'schema_version': 1, 'status': 'error', 'error': 'build failed'})
        duplicate = copy.deepcopy(FIXTURE)
        duplicate['theorems'].append(duplicate['theorems'][0])
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            claims.classify(duplicate)


class AssessTests(unittest.TestCase):
    """Binding, domain, hypotheses and witnesses from the extracted kernel statements."""

    def goal(self, theorem, strength, definition, domain='all', report=FIXTURE, heads=None, **extra):
        return claims.check_goal({'theorem': theorem, 'strength': strength, 'domain': domain}, theorems_of(report),
                                 definition=definition, heads=heads, **extra)

    def test_subject_must_be_the_root(self):
        self.assertEqual(self.goal('ClaimFixture.ret_total', 'total_correctness', 'ClaimFixture.ret')['status'], 'accepted')
        for definition in ('ClaimFixture.boom', 'ClaimFixture.diverge'):
            goal = self.goal('ClaimFixture.ret_total', 'total_correctness', definition)
            self.assertEqual((goal['status'], goal['binding']), ('rejected', 'unrelated'))
            self.assertIn('ClaimFixture.ret', goal['reason'])
        # Runners (`StateT.run`, `ExceptT.run`) are peeled to the computation.
        for name in ('ClaimFixture.ret_run', 'ClaimFixture.ret_some', 'ClaimFixture.ret_pure_ok'):
            self.assertEqual(self.goal(name, 'total_correctness', 'ClaimFixture.ret')['binding'], 'direct', name)
        # An unregistered head (a wrapper definition) has no recognised computation.
        goal = self.goal('ClaimFixture.wrapped_total', 'safety', 'ClaimFixture.ret')
        self.assertEqual((goal['status'], goal['binding']), ('rejected', 'mentions'))

    def test_domain_is_derived(self):
        goal = self.goal('ClaimFixture.ret_run', 'total_correctness', 'ClaimFixture.ret')
        self.assertEqual(goal['derived_domain']['scope'], 'universal')
        self.assertEqual(goal['derived_domain']['arguments'], [{'position': 0, 'argument': 'v'}, {'state': 0, 'argument': 'm'}])
        for name, field, value in (('ClaimFixture.ret_run_ground', 'fixed', ['parameter 0']),
                                   ('ClaimFixture.premise_total', 'constrained_by', ['_h'])):
            with self.subTest(theorem=name):
                goal = self.goal(name, 'total_correctness', 'ClaimFixture.ret')
                self.assertEqual(goal['status'], 'rejected')
                self.assertIn('not marked scoped', goal['reason'])
                self.assertEqual(goal['derived_domain'][field], value)
                goal = self.goal(name, 'total_correctness', 'ClaimFixture.ret', domain='scoped: one input')
                self.assertEqual(goal['status'], 'accepted', goal['reason'])

    def test_hypotheses_about_generated_code_are_rejected(self):
        report = copy.deepcopy(FIXTURE)
        theorem = theorems_of(report)['ClaimFixture.premise_total']
        theorem['statement']['binders'][2]['defs'] = ['ClaimFixture.ret']
        goal = self.goal('ClaimFixture.premise_total', 'safety', 'ClaimFixture.ret', 'scoped: v > 0', report=report)
        self.assertEqual(goal['status'], 'rejected')
        self.assertIn('_h mentions ClaimFixture.ret', goal['reason'])
        # Allowed only as a declared root assumption; claim heads are never allowed.
        goal = self.goal('ClaimFixture.premise_total', 'total_correctness', 'ClaimFixture.ret', 'scoped: v > 0',
                         report=report, allowed=['ClaimFixture.ret'])
        self.assertEqual(goal['status'], 'accepted', goal['reason'])
        theorem['statement']['binders'][2]['defs'] = ['Zig.TotalTriple']
        goal = self.goal('ClaimFixture.premise_total', 'safety', 'ClaimFixture.ret', 'scoped: v > 0', report=report)
        self.assertIn('mentions Zig.TotalTriple', goal['reason'])
        # Any definition of the generated module counts, not only the root.
        theorem['statement']['binders'][2]['defs'] = ['ClaimFixture.boom']
        goal = self.goal('ClaimFixture.premise_total', 'safety', 'ClaimFixture.ret', 'scoped: v > 0', report=report,
                         generated={'ClaimFixture.boom'})
        self.assertEqual(goal['status'], 'rejected')

    def test_witnesses_cap_strength(self):
        goal = self.goal('ClaimFixture.diverge_partial', 'partial_correctness', 'ClaimFixture.diverge')
        self.assertEqual((goal['status'], goal['derived_strength']), ('rejected', 'safety'))
        self.assertIn('liveness witness absent', goal['reason'])
        self.assertEqual(self.goal('ClaimFixture.diverge_partial', 'safety', 'ClaimFixture.diverge')['status'], 'accepted')
        self.assertEqual(self.goal('ClaimFixture.ret_partial', 'partial_correctness', 'ClaimFixture.ret')['status'], 'accepted')
        goal = self.goal('ClaimFixture.ret_thread', 'partial_correctness', 'ClaimFixture.ret')
        self.assertIn('non-vacuity witness absent', goal['reason'])
        # A companion must itself be an allowed audited theorem, with the recomputed statement.
        report = copy.deepcopy(FIXTURE)
        theorems = theorems_of(report)
        theorems['ClaimFixture.ret_total.nonvacuous']['allowed'] = False
        goal = self.goal('ClaimFixture.ret_total', 'total_correctness', 'ClaimFixture.ret', report=report)
        self.assertEqual(goal['status'], 'rejected')
        self.assertIn('non-vacuity witness unaudited', goal['reason'])
        theorems['ClaimFixture.ret_partial']['statement']['witnesses']['liveness']['status'] = 'mismatch'
        goal = self.goal('ClaimFixture.ret_partial', 'partial_correctness', 'ClaimFixture.ret', report=report)
        self.assertIn('liveness witness mismatch', goal['reason'])

    def test_new_heads_plug_into_the_same_mechanism(self):
        heads = registry_with_eventually()
        theorems = classified(FIXTURE, heads)
        self.assertEqual(theorems['ClaimFixture.countdown_total']['derived_strength'], 'total_correctness')
        goal = self.goal('ClaimFixture.countdown_total', 'total_correctness', 'Zig.Conc.Total.countdown', heads=heads)
        # The initial memory `{}` is fixed: the claim is scoped to it.
        self.assertEqual((goal['binding'], goal['derived_domain']['fixed']), ('direct', ['initial state 0']))
        self.assertEqual(goal['status'], 'rejected')
        goal = self.goal('ClaimFixture.countdown_total', 'total_correctness', 'Zig.Conc.Total.countdown',
                         domain='scoped: initial memory {}', heads=heads)
        self.assertEqual(goal['status'], 'accepted', goal['reason'])
        heads[EVENTUALLY] = dict(heads[EVENTUALLY], fingerprint='1' * 32)
        goal = self.goal('ClaimFixture.countdown_total', 'total_correctness', 'Zig.Conc.Total.countdown', heads=heads)
        self.assertIn('not the registered one', goal['reason'])


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        (self.base / 'profile.json').write_text(json.dumps({'name': 'legacy-abi64-le', 'zig_version': '0.16.0'}))
        self.report = self.base / 'assurance.json'
        self.report.write_text(json.dumps(FIXTURE))

    def manifest(self, goals, function='ret'):
        manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee', 'source_closure': ['a.zig'],
                    'components': {'compiler_patch': ['p'], 'runtime': ['r'], 'toolchain': ['t']},
                    'allowed_assumptions': [],
                    'roots': [{'id': 'root', 'function': function, 'air': ['f.json'], 'namespace': 'ClaimFixture',
                               'prefix': '', 'contracts': ['Fixture.lean'],
                               'goals': [{'theorem': t, 'strength': s, 'domain': 'fixture'} for t, s in goals],
                               'assumptions': [], 'exclusions': []}]}
        path = self.base / 'project.json'
        path.write_text(json.dumps(manifest))
        return path

    def cli(self, *args):
        return subprocess.run([sys.executable, str(SCRIPT), *map(str, args)],
                              capture_output=True, text=True, timeout=30)

    def check(self, goals, function='ret'):
        result = self.cli('check', self.manifest(goals, function), '--assurance', self.report)
        return result.returncode, json.loads(result.stdout) if result.stdout else None, result.stderr

    def test_matching_and_weaker_goals_accepted(self):
        code, result, err = self.check([('ClaimFixture.ret_total', 'total_correctness'),
                                        ('ClaimFixture.ret_total', 'partial_correctness'),
                                        ('ClaimFixture.ret_run', 'total_correctness'),
                                        ('ClaimFixture.ret_partial', 'partial_correctness'),
                                        ('ClaimFixture.ret_partial', 'safety'),
                                        ('ClaimFixture.ret_returns', 'safety')])
        self.assertEqual(code, 0, err)
        self.assertEqual(result['status'], 'pass')
        self.assertTrue(all(g['status'] == 'accepted' for g in result['roots'][0]['goals']))
        code, result, err = self.check([('ClaimFixture.diverge_partial', 'safety')], function='diverge')
        self.assertEqual(code, 0, err)

    def test_diverging_program_cannot_be_declared_correct(self):
        for strength in ('total_correctness', 'partial_correctness'):
            code, result, err = self.check([('ClaimFixture.diverge_partial', strength)], function='diverge')
            self.assertEqual(code, 1)
            goal = result['roots'][0]['goals'][0]
            self.assertEqual((goal['status'], goal['derived_strength']), ('rejected', 'safety'))
            self.assertIn('exceeds', goal['reason'])
            self.assertIn('diverge_partial', err)

    def test_overstated_goals_rejected(self):
        for name, strength, function in [('ClaimFixture.ret_returns', 'total_correctness', 'ret'),
                                         ('ClaimFixture.ret_returns', 'partial_correctness', 'ret'),
                                         ('ClaimFixture.ret_partial', 'total_correctness', 'ret'),
                                         ('ClaimFixture.wrapped_total', 'total_correctness', 'ret'),
                                         ('ClaimFixture.partial_and_returns', 'total_correctness', 'ret'),
                                         ('ClaimFixture.panic_run', 'safety', 'boom'),
                                         ('ClaimFixture.panic_some', 'safety', 'boom'),
                                         ('ClaimFixture.panic_pure', 'safety', 'boom'),
                                         ('ClaimFixture.diverge_not_total', 'safety', 'diverge'),
                                         ('ClaimFixture.ret_total', 'resource_bound', 'ret'),
                                         ('ClaimFixture.ret_total', 'correspondence', 'ret'),
                                         ('ClaimFixture.ret_total', 'total_correctness', 'boom'),
                                         ('ClaimFixture.ret_run_ground', 'total_correctness', 'ret')]:
            with self.subTest(name=name, strength=strength):
                code, result, _ = self.check([(name, strength)], function)
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

    def test_report_and_heads_commands(self):
        result = self.cli('report', '--assurance', self.report)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(json.loads(result.stdout)['theorems']), len(EXPECTED))
        result = self.cli('heads', '--assurance', self.report)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(EVENTUALLY, json.loads(result.stdout))


if __name__ == '__main__':
    unittest.main()
