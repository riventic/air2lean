"""Bounded mocks only: never execute the AIR translator, Lean, Zig or Lake."""
import contextlib
import copy
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest import mock

sys.dont_write_bytecode = True
SCRIPTS = Path(__file__).resolve().parents[3] / 'scripts'
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location('project_diagnostics', SCRIPTS / 'project-diagnostics.py')
adapter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(adapter)
project = adapter.project


def diagnostic(file, code='JSON_SYNTAX', phase='decode', category='malformed_input', chain=()):
    return dict(code=code, phase=phase, category=category, message='display only', message_truncated=False,
        file=file, function=None, anchor={'id_space': 'unavailable', 'instruction': None, 'type': None,
        'global': None, 'nearest_dbg_line': None}, source_span=None, source_span_status='unavailable_in_AIR',
        dependency_chain=list(chain), dependency_scope=adapter.DEPENDENCIES,
        prerequisites=[], first_error_in_unit=True)


def receipt(files, diagnostics=(), truncated=False):
    items = list(diagnostics)
    return dict(schema=1, kind=adapter.KIND, status='rejected' if items or truncated else 'checked',
        complete=not items and not truncated, truncated=truncated, diagnostic_limit=256,
        diagnostics_observed=len(items) + int(truncated),
        diagnostic_payload_bytes=sum(len(json.dumps(d, separators=(',', ':'), ensure_ascii=False).encode()) for d in items),
        diagnostics=items, files=[dict(file=f, function='unit', normalized=True,
        structure_valid=True, local_check='passed') for f in files],
        scope='selected AIR validation; first error within opaque prerequisite units',
        proof_status='not_run', runtime_outcomes='not_observed', source_correspondence='not_attested',
        dependency_completeness='not_attested; direct normalized calls and explicit spawn workers only')


class AdapterTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='air2lean-diagnostic-mock-')
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.tool = self.base / 'producer'
        self.tool.write_text('hashed mock identity; never executed')
        self.air = dict(schema=11, zig_version='0.16.0', name='unit', body=[])
        (self.base / 'air.json').write_text(json.dumps(self.air))
        (self.base / 'profile.json').write_text(json.dumps(dict(name='legacy-abi64-le', zig_version='0.16.0')))
        for name in ('source.zig', 'patch', 'runtime', 'toolchain', 'contract'):
            (self.base / name).write_text('evidence')
        self.root = dict(id='first', function='unit', air=['air.json'], namespace='Unit', prefix='',
                         contracts=['contract'], goals=[], assumptions=[], exclusions=[])
        self.manifest = dict(schema=1, profile='profile.json', float_semantics='ieee',
            source_closure=['source.zig'], components=dict(compiler_patch=['patch'], runtime=['runtime'],
            toolchain=['toolchain']), allowed_assumptions=[], roots=[self.root])
        self.path = self.base / 'project.json'
        self.save()
        self.calls = []
        self.patch = mock.patch.object(project, 'git_state', return_value=dict(revision=None, dirty=None, reason='offline mock'))
        self.patch.start()
        self.addCleanup(self.patch.stop)

    def save(self):
        self.path.write_text(json.dumps(self.manifest))

    def runner(self, argv, cwd, limits):
        self.assertEqual(argv[1], '--diagnostics-json')
        self.assertEqual(argv[3:], ['--profile', 'legacy-abi64-le', '--diagnostic-limit', '256'])
        self.assertNotIn('-o', argv)
        files = sorted((cwd / 'air').glob('*.json'))
        self.calls.append((cwd.name, [p.read_bytes() for p in files]))
        result = receipt([str(p) for p in files])
        for source in files:
            try:
                json.loads(source.read_bytes())
            except ValueError:
                result = receipt([str(p) for p in files], [diagnostic(str(source))])
                break
        raw = json.dumps(result).encode()
        return dict(returncode=0 if result['status'] == 'checked' else 1, stdout=raw, stderr=b'', failure=None)

    def check(self, runner=None):
        return adapter.check_project(self.path, self.tool, 256, runner or self.runner)[0]

    def test_success_preserves_evidence_and_never_emits(self):
        report = self.check()
        self.assertEqual(report['status'], 'checked')
        self.assertTrue(report['complete'])
        self.assertEqual(report['root_checks'][0]['producer']['files'][0]['file'], 'air.json')
        self.assertEqual(report['root_checks'][0]['path_map'][0]['staged'], '000000.json')
        self.assertEqual(report['translator']['sha256'], project.digest(self.tool.read_bytes()))
        for name in project.input_names(self.manifest):
            self.assertEqual(report['evidence']['files']['input/' + name]['sha256'],
                             project.digest((self.base / name).read_bytes()))
        self.assertTrue(all(s['status'] == 'not_run' for s in report['evidence']['roots'][0]['stages'].values()))
        self.assertEqual(report['proof_status'], 'not_run')
        self.assertFalse(list(self.base.rglob('Gen.lean')))

    def test_readable_malformed_unit_does_not_stop_sibling(self):
        (self.base / 'bad.json').write_bytes(b'{')
        self.root['air'] = ['bad.json']
        self.root['function'] = 'unknown'
        self.manifest['roots'].append(dict(self.root, id='sibling', air=['air.json'], function='unit'))
        self.save()
        report = self.check()
        self.assertEqual([c[0] for c in self.calls], ['first', 'sibling'])
        self.assertEqual(self.calls[0][1], [b'{'])
        self.assertEqual([r['status'] for r in report['root_checks']], ['rejected', 'checked'])
        bad = report['root_checks'][0]
        self.assertEqual(bad['producer']['diagnostics'][0]['file'], 'bad.json')
        self.assertEqual(bad['preflight'][0]['stage'], 'import')
        self.assertFalse(report['complete'])

    def test_missing_dependency_blocks_closure_but_not_independent_root(self):
        self.root['air'].append('missing.json')
        self.manifest['roots'].append(dict(self.root, id='sibling', air=['air.json']))
        self.save()
        report = self.check()
        self.assertEqual([r['status'] for r in report['root_checks']], ['blocked', 'checked'])
        self.assertEqual([c[0] for c in self.calls], ['sibling'])
        self.assertIn('AIR_UNAVAILABLE', [d['code'] for d in report['root_checks'][0]['preflight']])

    def test_typed_dependency_chain_and_anchors_retained(self):
        def runner(argv, cwd, limits):
            source = str(cwd / 'air' / '000000.json')
            d = diagnostic(source, 'CALLEE_BLOCKED', 'program', 'validation_failure', ['unit', 'mid', 'bad'])
            d['anchor'] = {'id_space': 'canonical', 'instruction': 42, 'type': None, 'global': None, 'nearest_dbg_line': 7}
            r = receipt([source], [d])
            return dict(returncode=1, stdout=json.dumps(r).encode(), stderr=b'', failure=None)
        result = self.check(runner)['root_checks'][0]['producer']['diagnostics'][0]
        self.assertEqual(result['dependency_chain'], ['unit', 'mid', 'bad'])
        self.assertEqual(result['anchor']['id_space'], 'canonical')
        self.assertEqual(result['anchor']['instruction'], 42)
        self.assertIsNone(result['source_span'])

    def test_profile_schema_and_import_boundaries(self):
        for document, stage in [(dict(self.air, schema=True), 'schema'),
                                (dict(self.air, zig_version='0.15.2'), 'profile')]:
            (self.base / 'air.json').write_text(json.dumps(document))
            report = self.check()
            self.assertEqual(report['root_checks'][0]['status'], 'rejected')
            self.assertEqual(report['root_checks'][0]['preflight'][0]['stage'], stage)
        (self.base / 'profile.json').write_text('{')
        self.calls.clear()
        report = self.check()
        self.assertEqual(report['root_checks'][0]['status'], 'blocked')
        self.assertFalse(self.calls)
        self.assertIn('PROJECT_PROFILE', [d['code'] for d in report['root_checks'][0]['preflight']])

    def test_declared_root_absent_cannot_pass(self):
        self.root['function'] = 'not_in_air'
        self.save()
        r = self.check()['root_checks'][0]
        self.assertEqual(r['status'], 'rejected')
        self.assertIn('PROJECT_ROOT', [d['code'] for d in r['preflight']])

    def test_shared_source_import_failure_retains_air_check_and_hashes(self):
        (self.base / 'source.zig').unlink()
        report = self.check()
        self.assertEqual(report['root_checks'][0]['status'], 'rejected')
        self.assertEqual(len(self.calls), 1)
        self.assertNotIn('input/source.zig', report['evidence']['files'])
        self.assertIn('input/air.json', report['evidence']['files'])

    def test_count_truncation_preserves_rejection(self):
        def runner(argv, cwd, limits):
            r = receipt([str(cwd / 'air' / '000000.json')], truncated=True)
            return dict(returncode=1, stdout=json.dumps(r).encode(), stderr=b'', failure=None)
        report = self.check(runner)
        self.assertTrue(report['truncated'])
        self.assertFalse(report['complete'])
        self.assertEqual(report['status'], 'rejected')

    def test_invalid_protocol_controls(self):
        air_dir = self.base / 'selected'
        mapping = {str(air_dir / '000000.json'): 'air.json'}
        good = receipt(mapping)
        bads = [dict(good, schema=True), dict(good, schema=2), dict(good, proof_status='proved'),
                dict(good, diagnostics_observed=1), dict(good, diagnostic_payload_bytes=1024 * 1024 + 1),
                dict(good, truncated=True), dict(good, files=[]), dict(good, unexpected=1)]
        d = diagnostic(next(iter(mapping)))
        for field, value in [('code', 'NEW_UNREVIEWED'), ('phase', 'proof'), ('source_span', {}),
                             ('file', '/different/path'), ('message', 'x' * 2049)]:
            mutated = dict(d, **{field: value})
            bads.append(receipt(mapping, [mutated]))
        for r in bads:
            with self.subTest(r=r), self.assertRaises((ValueError, TypeError)):
                adapter.validate_receipt(json.dumps(r).encode(), 0 if r['status'] == 'checked' else 1,
                                         mapping, air_dir, 256)
        understated = receipt(mapping, [d])
        understated['diagnostic_payload_bytes'] = 1
        with self.assertRaisesRegex(ValueError, 'retained diagnostic payload'):
            adapter.validate_receipt(json.dumps(understated).encode(), 1, mapping, air_dir, 256)
        with self.assertRaises(ValueError):
            adapter.validate_receipt(json.dumps(good).encode(), 1, mapping, air_dir, 256)
        for raw in [b'{', b'{"schema":1,"schema":1}', b'\xff']:
            with self.assertRaises((ValueError, UnicodeError)):
                adapter.validate_receipt(raw, 1, mapping, air_dir, 256)

    def test_protocol_error_continues_sibling(self):
        self.manifest['roots'].append(dict(self.root, id='sibling'))
        self.save()
        def runner(argv, cwd, limits):
            if cwd.name == 'first':
                return dict(returncode=0, stdout=b'{}', stderr=b'', failure=None)
            return self.runner(argv, cwd, limits)
        report = self.check(runner)
        self.assertEqual([r['status'] for r in report['root_checks']], ['error', 'checked'])
        self.assertEqual(report['root_checks'][0]['preflight'][-1]['stage'], 'protocol')

    def test_exit_stderr_and_timeout_failure_honesty(self):
        for patch in [dict(returncode=7), dict(stderr=b'unstructured failure'), dict(failure='CHECK_TIMEOUT')]:
            def runner(argv, cwd, limits):
                result = self.runner(argv, cwd, limits)
                result.update(patch)
                return result
            record = self.check(runner)['root_checks'][0]
            self.assertEqual(record['status'], 'error')
            self.assertFalse(record['complete'])

    def test_normalized_reports_deterministic_except_raw_receipt_hash(self):
        first, second = self.check(), self.check()
        for report in (first, second):
            for root in report['root_checks']:
                root['execution'].pop('stdout_sha256')
        self.assertEqual(first, second)

    def test_atomic_no_clobber_and_input_preservation(self):
        destination = self.base / 'report.json'
        destination.write_text('KEEP')
        before = self.path.read_bytes()
        stdout, stderr = io.StringIO(), io.StringIO()
        real_check = adapter.check_project
        def offline(*args):
            return real_check(*args, runner=self.runner)
        with mock.patch.object(adapter, 'check_project', side_effect=offline), \
             mock.patch.object(adapter.signal, 'signal'), contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            result = adapter.main(['diagnosticcheck', str(self.path), '--translator', str(self.tool), '--out', str(destination)])
        self.assertEqual(result, 2)
        self.assertEqual(stdout.getvalue(), '')
        self.assertEqual(destination.read_text(), 'KEEP')
        self.assertEqual(self.path.read_bytes(), before)
        self.assertFalse(list(self.base.glob('Gen.lean')))

    def test_report_input_overlap_rejected_before_producer(self):
        with mock.patch.object(adapter, 'check_project') as checker, mock.patch.object(adapter.signal, 'signal'), \
             contextlib.redirect_stderr(io.StringIO()):
            rc = adapter.main(['diagnosticcheck', str(self.path), '--translator', str(self.tool), '--out', str(self.path)])
        self.assertEqual(rc, 2)
        checker.assert_not_called()

    def test_changed_producer_not_attested(self):
        def runner(argv, cwd, limits):
            result = self.runner(argv, cwd, limits)
            self.tool.write_text('changed')
            return result
        with self.assertRaisesRegex(ValueError, 'translator changed'):
            self.check(runner)

    def test_project_receipt_budget_skips_remaining_roots(self):
        self.manifest['roots'].append(dict(self.root, id='sibling'))
        self.manifest['limits'] = dict(max_total_output_bytes=1)
        self.save()
        def runner(argv, cwd, limits):
            return dict(returncode=1, stdout=b'x', stderr=b'', failure='CHECK_OUTPUT_LIMIT')
        report = self.check(runner)
        self.assertEqual(report['root_checks'][1]['status'], 'not_run')
        self.assertTrue(report['root_checks'][1]['truncated'])
        self.assertFalse(report['complete'])

    def test_directory_failure_is_typed_producer_evidence(self):
        def runner(argv, cwd, limits):
            d = diagnostic(None, 'INPUT_READ', 'input', 'io_failure')
            r = receipt([], [d])
            return dict(returncode=1, stdout=json.dumps(r).encode(), stderr=b'', failure=None)
        r = self.check(runner)['root_checks'][0]
        self.assertEqual(r['status'], 'rejected')
        self.assertEqual(r['producer']['diagnostics'][0]['code'], 'INPUT_READ')
        self.assertFalse(r['complete'])

    def test_retained_payload_bound_is_checked_independently(self):
        air = self.base / 'air'
        mapping = {str(air / '000000.json'): 'air.json'}
        d = diagnostic(next(iter(mapping)))
        d['message'] = 'x' * 1024
        r = receipt(mapping, [d] * 1100)
        r.update(diagnostic_limit=4096, diagnostic_payload_bytes=1)
        with self.assertRaisesRegex(ValueError, 'retained diagnostic payload'):
            adapter.validate_receipt(json.dumps(r).encode(), 1, mapping, air, 4096)

    def test_successful_atomic_receipt_matches_stdout(self):
        destination = self.base / 'receipt.json'
        stdout, stderr = io.StringIO(), io.StringIO()
        real_check = adapter.check_project
        def offline(*args):
            return real_check(*args, runner=self.runner)
        with mock.patch.object(adapter, 'check_project', side_effect=offline), \
             mock.patch.object(adapter.signal, 'signal'), contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            status = adapter.main(['diagnosticcheck', str(self.path), '--translator', str(self.tool), '--out', str(destination)])
        self.assertEqual(status, 0, stderr.getvalue())
        self.assertEqual(destination.read_bytes(), stdout.getvalue().encode())
        self.assertFalse(list(self.base.rglob('Gen.lean')))

    def test_interruption_preserves_prior_receipt(self):
        destination = self.base / 'receipt.json'
        destination.write_text('KEEP')
        stdout, stderr = io.StringIO(), io.StringIO()
        real_check = adapter.check_project
        def cancelled(argv, cwd, limits):
            raise KeyboardInterrupt
        def offline(*args):
            return real_check(*args, runner=cancelled)
        with mock.patch.object(adapter, 'check_project', side_effect=offline), \
             mock.patch.object(adapter.signal, 'signal'), contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            rc = adapter.main(['diagnosticcheck', str(self.path), '--translator', str(self.tool), '--out', str(destination)])
        self.assertEqual(rc, 130)
        self.assertEqual(destination.read_text(), 'KEEP')
        self.assertEqual(stdout.getvalue(), '')
        self.assertEqual(json.loads(stderr.getvalue())['diagnostics'][0]['code'], 'CANCELLED')

    def test_unfinished_self_expiring_mock_descendant_is_cancelled(self):
        marker = self.base / 'late'
        child = 'import time,pathlib;time.sleep(2);pathlib.Path(' + repr(str(marker)) + ').write_text("late")'
        parent = 'import subprocess,sys;subprocess.Popen([sys.executable,"-c",' + repr(child) + '])'
        result = adapter.invoke([sys.executable, '-c', parent], self.base,
                                dict(project.LIMITS, timeout_seconds=3, max_output_bytes=1024))
        self.assertEqual(result['failure'], 'CHECK_DESCENDANTS')
        time.sleep(2.1)
        self.assertFalse(marker.exists())

    def test_bounded_python_mock_runner_timeout_and_output(self):
        limits = dict(project.LIMITS, timeout_seconds=1, max_output_bytes=1024)
        result = adapter.invoke([sys.executable, '-c', 'import time;time.sleep(2)'], self.base, limits)
        self.assertEqual(result['failure'], 'CHECK_TIMEOUT')
        result = adapter.invoke([sys.executable, '-c', 'print("x"*4096)'], self.base, limits)
        self.assertIsNotNone(result['failure'])
        self.assertLessEqual(len(result['stdout']) + len(result['stderr']), 1024)


if __name__ == '__main__':
    unittest.main()
