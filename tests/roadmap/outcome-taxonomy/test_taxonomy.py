#!/usr/bin/env python3
"""V06 outcome-taxonomy regressions: shared taxonomy, absence refusal in claims and coverage.

Offline: synthetic diff summaries and the checked-in claim fixture report only."""
import contextlib
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

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
sys.path.insert(0, str(ROOT / 'scripts'))
import theorem_universe as universe

assumptions = universe.assumptions


def case(status, kind=None, schedule=None, function='ret'):
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
            (case('unspecified_timer_exclusion', 'unspecified_timer'), {O.UNSPECIFIED_TIMER}),
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
            'unspecified': case('unspecified_exclusion', 'unspecified'),
            'unsupported timer': case('unspecified_timer_exclusion', 'unspecified_timer'),
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

    def test_timer_and_unspecified_stay_distinct(self):
        timer = case('unspecified_timer_exclusion', 'unspecified_timer')
        plain = case('unspecified_exclusion', 'unspecified')
        self.assertEqual(outcomes.count([timer]), {'unspecified_timer': 1})
        self.assertEqual(outcomes.count([plain]), {'unspecified_behavior': 1})
        for claim in outcomes.ABSENCE_CLAIMS:
            with self.subTest(claim=claim):
                verdict = self.verdict(claim, timer)
                self.assertEqual(verdict['blocking'], {'unspecified_timer': 1})
                self.assertIn('unsupported timer', verdict['reason'])
                verdict = self.verdict(claim, plain)
                self.assertEqual(verdict['blocking'], {'unspecified_behavior': 1})
                self.assertNotIn('unsupported timer', verdict['reason'])
                self.assertIn('unspecified result', verdict['reason'])
        # The status alone (rows without `model_kind`) keeps the distinction.
        self.assertEqual(outcomes.case_outcomes(case('unspecified_timer_exclusion')), {O.UNSPECIFIED_TIMER})

    def test_diff_report_types_the_timer_constructor(self):
        meta = lambda kind: json.dumps({'schema': 1, 'kind': kind, 'legacy_line': '{"fail":"Zig.Error.unsupportedTimer"}'})
        timer = {'fail': 'Zig.Error.unsupportedTimer'}
        kind, _ = report.observation(meta('unspecified_timer'), timer, 'model')
        self.assertEqual(kind, report.Kind.UNSPECIFIED_TIMER)
        for wrong in ('unspecified', 'model_panic'):
            with self.subTest(kind=wrong), self.assertRaises(report.Invalid):
                report.observation(meta(wrong), timer, 'model')
        native = {'ok': 1}
        self.assertEqual(report.classify(native, timer, report.Kind.VALUE, kind, None), report.Status.UNSPECIFIED_TIMER)
        unspecified = {'fail': 'Zig.Error.unspecified'}
        # An unspecified result is an exclusion only on an input pinned for it (F3); the timer
        # constructor is typed apart and never needs a pin.
        self.assertEqual(report.classify(native, unspecified, report.Kind.VALUE, report.Kind.UNSPECIFIED, None,
                                         pinned=True), report.Status.UNSPECIFIED)
        self.assertEqual(report.classify(native, unspecified, report.Kind.VALUE, report.Kind.UNSPECIFIED, None),
                         report.Status.MISMATCH)
        # The legacy compatibility projection still counts both in its `unspecified` bucket.
        self.assertEqual(report.legacy_bucket(native, timer, False), 'unspecified')


class ClaimsEvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.compilation = tempfile.TemporaryDirectory(prefix='taxonomy-synthetic-compiler-')
        cls.addClassCleanup(cls.compilation.cleanup)
        base = Path(cls.compilation.name)
        toolchain = base / 'toolchain'
        (toolchain / 'bin').mkdir(parents=True)
        (toolchain / 'lib/lean').mkdir(parents=True)
        for name in ('bin/lean', 'bin/leanchecker', 'lib/lean/Init.olean'):
            (toolchain / name).write_bytes(b'synthetic installed input')
        cls.runtime = {'lean_sysroot': str(toolchain.resolve()),
                       'toolchain_runtime_sha256': assumptions.toolchain_runtime_sha256(toolchain)}
        lake = base / 'stub-bin/lake'
        lake.parent.mkdir()
        lake.write_text('#!' + sys.executable + '\nimport os,pathlib,sys\n'
                        'if sys.argv[1:] == ["env", "printenv", "LEAN_SYSROOT"]:\n'
                        '    print(os.environ["STUB_LEAN_SYSROOT"])\n'
                        'elif sys.argv[1:] == ["env", "printenv", "LEAN_PATH"]:\n'
                        '    standard = pathlib.Path(os.environ["STUB_LEAN_SYSROOT"]) / "lib/lean"\n'
                        '    print(os.environ["LEAN_PATH"] + os.pathsep + str(standard))\n'
                        'else:\n'
                        '    raise AssertionError(sys.argv[1:])\n')
        lake.chmod(0o755)
        cls.env = dict(os.environ, PATH=str(lake.parent) + os.pathsep + os.environ['PATH'],
                       STUB_LEAN_SYSROOT=cls.runtime['lean_sysroot'])
        _, units = universe.universe()
        by_file = {unit.file: unit for unit in units}
        selected = [by_file['tests/roadmap/claims/Fixture.lean']]

        def compile_fixture(source, root, olean, lean_path, log, **kwargs):
            olean.parent.mkdir(parents=True, exist_ok=True)
            olean.write_bytes(b'compiled fixture')
            return None

        # The statements are synthetic test input, not a kernel replay. Keep the real
        # compiler-owned Unit/source plan and prepare it BEFORE the fake compiler runs.
        with mock.patch.dict(os.environ, cls.env):
            with mock.patch.object(assumptions, 'prepared_tool', contextlib.nullcontext):
                context = universe.prepare_compilation(selected, by_file, base / 'producer')
            with mock.patch.object(universe, 'compile_unit', side_effect=compile_fixture):
                errors = universe.compile_all(universe.closure(selected, by_file), by_file,
                                              base / 'producer', compiled_units=context)
            if errors:
                raise AssertionError(errors)
            universe.seal_compilation(context)
        cls.compiler_context = context
        cls.module = selected[0].module

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.base = Path(temp.name)
        (self.base / 'profile.json').write_text(json.dumps({'name': 'legacy-abi64-le', 'zig_version': '0.16.0'}))
        self.diff = self.base / 'diff.json'
        self.report = self.base / 'assurance.json'
        unit = self.compiler_context['units'][self.module]
        self.olean = Path(unit['output_path'])
        self.olean.write_bytes(b'compiled fixture')
        fixture = json.loads(FIXTURE.read_text())
        fixture.update(modules=[self.module], module_imports={self.module: []})
        fixture['extractor'] = dict(fixture.get('extractor', {}), **self.runtime)
        self.report.write_text(json.dumps(dict(fixture, freshness={**self.runtime,
            'revision': assumptions.git_revision(), 'lake_trace_check': {'modules': [], 'status': 'up-to-date'},
            'compiled_units': self.compiler_context,
            'artifacts': [{'module': self.module, 'olean': assumptions.display(self.olean),
                           'olean_sha256': unit['outputs'][0][1]['sha256'],
                           'source': unit['source']['path'], 'source_sha256': unit['source']['sha256']}]})))

    def run_check(self, rows, strength='total_correctness', function='example.ret', complete=True, diff=True,
                  tamper=None):
        manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee', 'source_closure': ['a.zig'],
                    'components': {'compiler_patch': ['p'], 'runtime': ['r'], 'toolchain': ['t']},
                    'allowed_assumptions': [],
                    'roots': [{'id': 'root', 'function': function, 'air': ['f.json'], 'namespace': 'ClaimFixture',
                               'prefix': 'example.', 'contracts': ['Fixture.lean'],
                               'goals': [{'theorem': 'ClaimFixture.fret_total', 'strength': strength, 'domain': 'all'}],
                               'assumptions': [], 'exclusions': []}]}
        path = self.base / 'project.json'
        path.write_text(json.dumps(manifest))
        cases = ''.join(json.dumps(r) + '\n' for r in rows).encode()
        Path(str(self.diff) + '.jsonl').write_bytes(cases)
        summary = {'schema': 1, 'complete': complete, 'runner_runtime_sources': report.source_hashes(ROOT),
                   'cases_sha256': hashlib.sha256(cases).hexdigest()}
        self.diff.write_text(json.dumps(tamper(summary) if tamper else summary))
        extra = ['--diff', str(self.diff)] if diff else []
        # The checkout under test may have uncommitted changes (the evidence binding is tested here).
        result = subprocess.run([sys.executable, str(CLAIMS), 'check', str(path), '--assurance', str(self.report),
                                 '--allow-dirty', *extra],
                                capture_output=True, text=True, timeout=30, env=self.env)
        return result.returncode, json.loads(result.stdout) if result.stdout else None, result.stderr

    def test_clean_and_error_return_evidence_accepted(self):
        code, result, err = self.run_check([case('value_match', 'value'), case('error_return_match', 'error_return'),
                                            case('value_match', 'value', search())])
        self.assertEqual(code, 0, err)
        self.assertEqual(result['roots'][0]['outcomes'],
                         {'valid': 1, 'nondeterministic_valid': 1, 'error_return': 1})

    def test_missing_or_mismatched_runtime_headers_are_refused(self):
        original = self.report.read_text()
        cases = [(section, key) for section in ('extractor', 'freshness')
                 for key in ('lean_sysroot', 'toolchain_runtime_sha256')]
        try:
            for section, key in cases:
                with self.subTest(section=section, key=key):
                    report = json.loads(original)
                    del report[section][key]
                    self.report.write_text(json.dumps(report))
                    code, result, err = self.run_check([case('value_match', 'value')])
                    self.assertEqual((code, result), (2, None))
                    self.assertIn('runtime binding', err)
            report = json.loads(original)
            report['extractor']['toolchain_runtime_sha256'] = '0' * 64
            self.report.write_text(json.dumps(report))
            code, result, err = self.run_check([case('value_match', 'value')])
            self.assertEqual((code, result), (2, None))
            self.assertIn('runtime binding', err)
        finally:
            self.report.write_text(original)

    def test_missing_or_mismatched_compiler_binding_is_refused(self):
        original = self.report.read_text()
        try:
            missing = json.loads(original)
            del missing['freshness']['compiled_units']
            mismatched = json.loads(original)
            mismatched['freshness']['artifacts'][0].update(source=None, source_sha256=None)
            for report, message in ((missing, 'no compiler-owned run binding'),
                                    (mismatched, 'source/output differs from its run binding')):
                with self.subTest(message=message):
                    self.report.write_text(json.dumps(report))
                    code, result, err = self.run_check([case('value_match', 'value')])
                    self.assertEqual((code, result), (2, None))
                    self.assertIn(message, err)
        finally:
            self.report.write_text(original)

    def test_changed_compiler_output_is_refused(self):
        try:
            self.olean.write_bytes(b'changed after the compiler run')
            code, result, err = self.run_check([case('value_match', 'value')])
            self.assertEqual((code, result), (2, None))
            self.assertIn('Fixture olean changed', err)
        finally:
            self.olean.write_bytes(b'compiled fixture')

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

    def test_timer_evidence_rejects_with_unsupported_timer_reason(self):
        code, result, err = self.run_check([case('value_match', 'value'),
                                            case('unspecified_timer_exclusion', 'unspecified_timer')], 'safety')
        self.assertEqual(code, 1, err)
        self.assertEqual(result['roots'][0]['outcomes'], {'valid': 1, 'unspecified_timer': 1})
        goal = result['roots'][0]['goals'][0]
        self.assertEqual(goal['blocking'], {'unspecified_timer': 1})
        self.assertIn('unsupported timer', goal['reason'])
        code, result, err = self.run_check([case('value_match', 'value'), case('unspecified_exclusion', 'unspecified')])
        self.assertEqual(code, 1, err)
        self.assertEqual(result['roots'][0]['outcomes'], {'valid': 1, 'unspecified_behavior': 1})
        self.assertNotIn('unsupported timer', result['roots'][0]['goals'][0]['reason'])

    def test_stale_or_unbound_evidence_is_refused(self):
        rows = [case('value_match', 'value')]
        name = 'scripts/diff-report.py'

        def changed(summary):
            sources = dict(summary['runner_runtime_sources'])
            sources[name] = '0' * 64
            return dict(summary, runner_runtime_sources=sources)

        def missing(summary):
            sources = dict(summary['runner_runtime_sources'])
            del sources[name]
            return dict(summary, runner_runtime_sources=sources)

        tampers = {
            'changed source': (changed, 'stale differential evidence'),
            'inventory differs': (missing, 'stale differential evidence'),
            'no fingerprints': (lambda s: {k: v for k, v in s.items() if k != 'runner_runtime_sources'},
                                'no source/runner fingerprints'),
            'cases changed': (lambda s: dict(s, cases_sha256='0' * 64), 'cases_sha256'),
            'cases unbound': (lambda s: {k: v for k, v in s.items() if k != 'cases_sha256'}, 'cases_sha256'),
        }
        for label, (tamper, message) in tampers.items():
            with self.subTest(label=label):
                code, result, err = self.run_check(rows, tamper=tamper)
                self.assertEqual(code, 2, err)
                self.assertIsNone(result)
                self.assertIn(message, err)
        self.assertEqual(self.run_check(rows)[0], 0)

    def test_other_functions_and_unbound_roots_do_not_count(self):
        code, _, err = self.run_check([case('value_match', 'value'), case('search_cap', 'value', search('capped'), 'other')])
        self.assertEqual(code, 0, err)
        code, result, err = self.run_check([case('search_cap', 'value', search('capped'))], function='ret')
        self.assertEqual(code, 0, err)
        self.assertIsNone(result['roots'][0]['outcomes'])

    def test_without_diff_type_evidence_alone_decides(self):
        code, result, err = self.run_check([case('search_cap', 'value', search('capped'))], diff=False)
        self.assertEqual(code, 0, err)
        self.assertIsNone(result['roots'][0]['outcomes'])

    def test_incomplete_summary_is_an_input_error(self):
        code, _, err = self.run_check([case('value_match', 'value')], complete=False)
        self.assertEqual(code, 2, err)


class ContractTests(unittest.TestCase):
    """The taxonomy as a contract vocabulary (V06): what a goal admits, judged against outcome counts."""

    def test_default_contract_admits_values_and_error_returns_only_where_absence_is_claimed(self):
        for strength in ('safety', 'partial_correctness', 'total_correctness'):
            self.assertEqual(outcomes.contract_admits(strength, None), {O.VALID, O.NONDETERMINISTIC_VALID, O.ERROR_RETURN})
        # A strength that claims nothing about failures is not refuted by one.
        for strength in ('resource_bound', 'correspondence'):
            self.assertEqual(outcomes.contract_admits(strength, None), outcomes.CONTRACT_OUTCOMES)

    def test_declarations_are_validated(self):
        self.assertEqual(outcomes.contract_admits('resource_bound', ['valid', 'panic', 'deadlock']),
                         {O.VALID, O.PANIC, O.DEADLOCK})
        # Divergence is incomplete evidence (fuel ran out), never an admitted program outcome.
        for strength, declared in (('total_correctness', ['divergence']), ('safety', ['panic']),
                                   ('safety', ['search_cap']), ('safety', ['unspecified_timer']),
                                   ('safety', ['unsupported_semantics']), ('safety', ['bogus']),
                                   ('safety', []), ('safety', ['valid', 'valid']), ('safety', 'valid')):
            with self.assertRaises(ValueError, msg=(strength, declared)):
                outcomes.contract_admits(strength, declared)

    def test_evidence_only_refutes(self):
        verdict = lambda counts, declared=None: outcomes.contract('total_correctness', declared, counts)['status']
        self.assertEqual(verdict({}), 'no_evidence')
        self.assertEqual(verdict({'valid': 4, 'error_return': 2}), 'not_refuted')
        self.assertEqual(verdict({'valid': 4, 'panic': 1}), 'refuted')
        self.assertEqual(verdict({'error_return': 1}, ['valid']), 'refuted')
        self.assertEqual(verdict({'valid': 1, 'search_cap': 1}), 'unassessed')
        self.assertEqual(verdict({'valid': 1, 'unspecified_timer': 1}), 'unassessed')
        self.assertEqual(verdict({'panic': 1, 'search_cap': 1}), 'refuted')

    def test_every_outcome_is_a_contract_outcome_or_incomplete_evidence(self):
        self.assertEqual(outcomes.CONTRACT_OUTCOMES | outcomes.INCOMPLETE, set(O))
        self.assertFalse(outcomes.CONTRACT_OUTCOMES & outcomes.INCOMPLETE)


if __name__ == '__main__':
    unittest.main()
