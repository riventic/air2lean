#!/usr/bin/env python3
"""Host-dispatch and single-row boundaries, without toolchain builds or Docker."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location('local_ci_memory_boundary', ROOT / 'scripts/local-ci-steps.py')
runner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(runner)
IN_PROCESS_HOST = runner.in_process_host
IMAGE = 'sha256:' + '1' * 64


class MemoryBoundary(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.snapshot = self.root / 'snapshot'
        self.artifacts = self.root / 'artifacts'
        self.imports = self.root / 'imports'
        self.results = self.root / 'row-results'
        for path in (self.snapshot, self.artifacts, self.imports, self.results, self.root / '.github/workflows'):
            path.mkdir(parents=True)
        self.workflow_bytes = b'captured workflow\n'
        (self.root / '.github/workflows/ci.yml').write_bytes(self.workflow_bytes)
        self.source = b'withheld fixture marker: whole-source archive bytes'
        self.digest = hashlib.sha256(self.source).hexdigest()
        self.workflow_digest = hashlib.sha256(self.workflow_bytes).hexdigest()
        self.stamp = f'revision=test\ntracked_clean=yes\nsnapshot_sha256={self.digest}\n'
        (self.snapshot / 'source.tar').write_bytes(self.source)
        (self.snapshot / 'files').write_bytes(b'')
        for path in (self.snapshot, self.artifacts):
            (path / 'source-revision').write_text(self.stamp)
        (self.imports / 'manifest.json').write_text('{}\n')
        self.workflow = {'jobs': {
            'producer': {'runs-on': 'ubuntu-24.04', 'steps': []},
            'consumer': {'runs-on': 'ubuntu-24.04', 'needs': ['producer'], 'steps': []},
            'other': {'runs-on': 'ubuntu-24.04', 'steps': []},
        }}
        previous = Path.cwd()
        os.chdir(self.root)
        self.addCleanup(os.chdir, previous)
        environment = patch.dict(os.environ, AIR2LEAN_LOCAL_IMAGE_ID=IMAGE,
                                 AIR2LEAN_LOCAL_IMPORTS=str(self.imports / 'manifest.json'),
                                 AIR2LEAN_LOCAL_PRODUCERS='{}',
                                 AIR2LEAN_LOCAL_BOOTSTRAP=str(self.snapshot / 'bootstrap.sh'))
        environment.start()
        self.addCleanup(environment.stop)
        outside = patch.object(runner, 'in_container', return_value=False)
        outside.start()
        self.addCleanup(outside.stop)
        host = patch.object(runner, 'in_process_host', return_value=True)
        host.start()
        self.addCleanup(host.stop)

    def prepare_row(self, part='producer'):
        (self.snapshot / 'source.tar').unlink(missing_ok=True)
        payload = runner.job_payload(self.workflow, part, self.digest, self.workflow_digest)
        raw = (runner.CR.canonical(payload) + '\n').encode()
        (self.snapshot / 'job.json').write_bytes(raw)
        os.environ['AIR2LEAN_LOCAL_JOB_PAYLOAD_SHA256'] = hashlib.sha256(raw).hexdigest()
        return payload

    def make_row(self, part='producer'):
        self.prepare_row(part)
        with patch.object(runner, 'in_container', return_value=True):
            return runner.WorkflowRun(None, self.artifacts, self.snapshot, row_only=True)

    def make_dispatch(self):
        return runner.WorkflowRun(self.workflow, self.artifacts, self.snapshot, dispatch=True, restricted=True)

    def receipt(self, selected, *, uploads=(), refs=None, **changes):
        payload = runner.job_payload(self.workflow, selected, self.digest, self.workflow_digest)
        payload_sha = hashlib.sha256((runner.CR.canonical(payload) + '\n').encode()).hexdigest()
        report = {'part': selected, 'success': True, 'snapshot_sha256': self.digest, 'source': self.stamp,
                  'workflow_sha256': self.workflow_digest, 'image_id': IMAGE, 'runner': 'linux/amd64',
                  'job_id': payload['job_id'], 'row': payload['row'], 'job_payload_sha256': payload_sha,
                  'producer_refs': {} if refs is None else refs, 'uploads': list(uploads)}
        report.update(changes)
        directory = self.results / selected.replace('/', '-')
        directory.mkdir(exist_ok=True)
        (directory / 'row.json').write_text(json.dumps(report))

    def checked_fixture_export(self, run):
        def export(part, payload, payload_sha, refs, succeeded):
            raw = (self.results / part.replace('/', '-') / 'row.json').read_bytes()
            return run.validate_row_receipt(part, payload, payload_sha, refs, raw, succeeded), raw
        return export

    def producer_ref(self, part='producer'):
        return {'part': part, 'snapshot_sha256': self.digest, 'workflow_sha256': self.workflow_digest,
                'row_sha256': '2' * 64}

    def test_container_rejects_archive_constructor_before_reading_any_bytes(self):
        with patch.object(runner, 'in_container', return_value=True), \
             patch.object(Path, 'read_bytes', side_effect=AssertionError('read archive before rejecting mode')), \
             self.assertRaisesRegex(ValueError, 'requires --row'):
            runner.WorkflowRun(self.workflow, self.artifacts, self.snapshot)

    def test_native_linux_rejects_legacy_archive_execution_before_reading_any_bytes(self):
        with patch.object(runner, 'in_process_host', return_value=False), \
             patch.object(Path, 'read_bytes', side_effect=AssertionError('read archive before rejecting mode')), \
             self.assertRaisesRegex(ValueError, 'in-process local CI is only available.*macOS'):
            runner.WorkflowRun(self.workflow, self.artifacts, self.snapshot)

    def test_native_linux_rejects_worker_execution_before_reading_any_bytes(self):
        with patch.object(runner, 'in_process_host', return_value=False), \
             patch.object(Path, 'read_bytes', side_effect=AssertionError('worker read source outside container')), \
             self.assertRaisesRegex(ValueError, '--row requires a Docker container'):
            runner.WorkflowRun(self.workflow, self.artifacts, self.snapshot, row_only=True)

    def test_native_linux_can_dispatch_without_retaining_source_bytes(self):
        with patch.object(runner, 'in_process_host', return_value=False):
            run = self.make_dispatch()
        self.assertIsNone(run.source)
        self.assertIsNone(run.inventory)
        self.assertEqual((self.snapshot / 'source.tar').read_bytes(), self.source)

    def test_in_process_host_requires_actual_darwin_and_arm64(self):
        for platform, machine, expected in (('darwin', 'arm64', True), ('darwin', 'x86_64', False),
                                             ('linux', 'aarch64', False), ('linux', 'arm64', False)):
            uname = os.uname_result(('system', 'node', 'release', 'version', machine))
            with self.subTest(platform=platform, machine=machine), \
                 patch.object(runner.sys, 'platform', platform), patch.object(runner.os, 'uname', return_value=uname):
                self.assertEqual(IN_PROCESS_HOST(), expected)

    def test_row_rejects_an_accessible_source_archive(self):
        with patch.object(runner, 'in_container', return_value=True), \
             self.assertRaisesRegex(ValueError, 'must not have access.*archive'):
            runner.WorkflowRun(None, self.artifacts, self.snapshot, row_only=True)

    def test_row_never_loads_archive_inventory_or_history_bytes(self):
        history = self.snapshot / 'main.bundle'
        history.write_bytes(b'unrestricted preflight history')
        self.prepare_row()
        actual_read = Path.read_bytes

        def read(path):
            if path.parent == self.snapshot and path.name != 'job.json':
                self.fail(f'row loaded snapshot bytes: {path.name}')
            if path == self.root / '.github/workflows/ci.yml':
                self.fail('row loaded the full workflow')
            return actual_read(path)

        with patch.object(Path, 'read_bytes', read), patch.object(runner, 'in_container', return_value=True):
            run = runner.WorkflowRun(None, self.artifacts, self.snapshot, row_only=True)
        self.assertIsNone(run.source)
        self.assertIsNone(run.inventory)
        self.assertEqual(run.history, history)
        self.assertEqual(run.source_sha, self.digest)

    def test_row_executes_one_job_without_reset_or_dependency_execution(self):
        run = self.make_row('consumer')
        with patch.object(run, 'run_row') as row, \
             patch.object(runner, 'reset_checkout', side_effect=AssertionError('reset inside row')):
            run.run('consumer')
        row.assert_called_once_with('consumer', 'consumer', {})
        self.assertEqual(run.completed, {'consumer'})

    def test_dispatch_preserves_host_capture_and_successful_producer_transport(self):
        history = self.snapshot / 'main.bundle'
        history.write_bytes(b'host-only main history')
        bootstrap = self.snapshot / 'bootstrap.sh'
        bootstrap.write_text('host bootstrap\n')
        self.workflow['jobs']['producer']['steps'] = [
            {'name': 'upload compiled', 'uses': 'actions/upload-artifact@pin',
             'with': {'name': 'compiled', 'path': 'build.tar'}}]
        run = self.make_dispatch()
        seen = []

        def container(command, *, env):
            self.assertEqual(command[:3], ['bash', str(bootstrap), '--container-row'])
            part = command[3]
            seen.append(part)
            imports = json.loads(Path(env['AIR2LEAN_LOCAL_IMPORTS']).read_text())
            refs = json.loads(env['AIR2LEAN_LOCAL_PRODUCERS'])
            if part == 'producer':
                self.assertEqual(imports, {})
                output = self.artifacts / 'uploads/compiled'
                output.mkdir(parents=True)
                (output / 'build.tar').write_bytes(b'actual producer output')
                self.receipt(part, uploads=['compiled'], refs=refs)
            else:
                self.assertEqual(imports, {'compiled': str(self.artifacts / 'uploads/compiled')})
                self.assertEqual(refs['compiled']['part'], 'producer')
                self.receipt(part, refs=refs)

        with patch.object(runner, 'call', side_effect=container), \
             patch.object(run, 'export_row', side_effect=self.checked_fixture_export(run)), \
             patch.object(runner, 'reset_checkout', side_effect=AssertionError('reset on dispatch path')), \
             patch.object(run, 'run_row', side_effect=AssertionError('row on host dispatch path')):
            run.run('consumer')
        self.assertEqual(seen, ['producer', 'consumer'])
        self.assertEqual(run.completed, {'producer', 'consumer'})
        self.assertEqual((self.snapshot / 'source.tar').read_bytes(), self.source)
        self.assertEqual(history.read_bytes(), b'host-only main history')
        self.assertTrue(bootstrap.exists())

    def test_dispatch_does_not_import_unrelated_completed_jobs(self):
        run = self.make_dispatch()
        output = self.artifacts / 'uploads/unrelated'
        output.mkdir(parents=True)
        run.uploads['unrelated'] = output
        run.upload_producers['unrelated'] = self.producer_ref('other')

        def container(command, *, env):
            self.assertEqual(json.loads(Path(env['AIR2LEAN_LOCAL_IMPORTS']).read_text()), {})
            self.receipt(command[-1])

        with patch.object(runner, 'call', side_effect=container), \
             patch.object(run, 'export_row', side_effect=self.checked_fixture_export(run)):
            run.run('producer')

    def test_dispatch_rejects_failed_or_mismatched_row_receipts(self):
        changes = ({'success': False}, {'snapshot_sha256': '0' * 64},
                   {'workflow_sha256': '0' * 64}, {'image_id': 'sha256:' + '0' * 64},
                   {'runner': 'linux/arm64'}, {'part': 'consumer'}, {'source': 'different snapshot'},
                   {'job_payload_sha256': '0' * 64}, {'job_id': 'consumer'}, {'row': {'unexpected': True}},
                   {'producer_refs': {'unexpected': self.producer_ref()}})
        for change in changes:
            with self.subTest(change=change):
                run = self.make_dispatch()

                def container(command, *, env):
                    self.receipt(command[-1], **change)

                with patch.object(runner, 'call', side_effect=container), \
                     patch.object(run, 'export_row', side_effect=self.checked_fixture_export(run)), \
                     self.assertRaisesRegex(ValueError, 'source-mismatched.*receipt'):
                    run.run('producer')
                self.assertEqual(run.completed, set())
                self.assertEqual(run.uploads, {})

    def test_dispatch_registers_nothing_when_scoped_export_fails(self):
        run = self.make_dispatch()
        with patch.object(runner, 'call'), \
             patch.object(run, 'export_row', side_effect=ValueError('missing declared artifact')), \
             self.assertRaisesRegex(ValueError, 'missing declared artifact'):
            run.run('producer')
        self.assertEqual(run.uploads, {})
        self.assertEqual(run.upload_producers, {})

    def test_failed_worker_keeps_diagnostics_without_registering_a_producer(self):
        self.workflow['jobs']['producer']['steps'] = [
            {'name': 'failure diagnostic', 'if': 'failure()', 'uses': 'actions/upload-artifact@pin',
             'with': {'name': 'diagnostic', 'path': 'failure.txt'}}]
        run = self.make_dispatch()
        failure = subprocess.CalledProcessError(7, ['fixture-worker'])

        def worker(command, *, env):
            directory = self.snapshot / 'containers'
            directory.mkdir()
            (directory / 'producer.id').write_text('3' * 64)
            self.receipt('producer', uploads=['diagnostic'], success=False)
            raise failure

        def export(part, payload, payload_sha, refs, succeeded):
            self.assertFalse(succeeded)
            report, raw = self.checked_fixture_export(run)(part, payload, payload_sha, refs, succeeded)
            output = self.artifacts / 'uploads/diagnostic'
            output.mkdir(parents=True)
            (output / 'failure.txt').write_text('retained failed-row diagnostic\n')
            return report, raw

        with patch.object(runner, 'call', side_effect=worker), patch.object(run, 'export_row', side_effect=export), \
             self.assertRaises(subprocess.CalledProcessError) as raised:
            run.run('producer')
        self.assertIs(raised.exception, failure)
        self.assertTrue((self.artifacts / 'uploads/diagnostic/failure.txt').is_file())
        self.assertEqual(run.completed, set())
        self.assertEqual(run.uploads, {})
        self.assertEqual(run.upload_producers, {})

    def test_imports_require_a_matching_source_bound_producer(self):
        output = self.imports / 'compiled'
        output.mkdir()
        (self.imports / 'manifest.json').write_text(json.dumps({'compiled': str(output)}))
        self.prepare_row('consumer')
        with patch.object(runner, 'in_container', return_value=True), \
             self.assertRaisesRegex(ValueError, 'matching producer references'):
            runner.WorkflowRun(None, self.artifacts, self.snapshot, row_only=True)
        ref = self.producer_ref() | {'snapshot_sha256': '0' * 64}
        with patch.dict(os.environ, AIR2LEAN_LOCAL_PRODUCERS=json.dumps({'compiled': ref})), \
             patch.object(runner, 'in_container', return_value=True), \
             self.assertRaisesRegex(ValueError, 'source-mismatched artifact producer'):
            runner.WorkflowRun(None, self.artifacts, self.snapshot, row_only=True)

    def test_row_imports_cannot_traverse_the_owned_import_namespace(self):
        self.prepare_row('consumer')
        outside = self.root / 'outside'
        outside.mkdir()
        for name, value in (('..', str(self.imports / '..')), ('compiled', str(outside))):
            (self.imports / 'manifest.json').write_text(json.dumps({name: value}))
            with self.subTest(name=name), \
                 patch.dict(os.environ, AIR2LEAN_LOCAL_PRODUCERS=json.dumps({name: self.producer_ref()})), \
                 patch.object(runner, 'in_container', return_value=True), \
                 self.assertRaisesRegex(ValueError, 'invalid local CI artifact import|owned directory'):
                runner.WorkflowRun(None, self.artifacts, self.snapshot, row_only=True)

    def test_initialize_uses_separate_commit_and_seal_without_opening_an_archive(self):
        pathspec = self.snapshot / 'files'
        bootstrap = self.snapshot / 'bootstrap.sh'
        with patch.object(runner, 'remove_check_trees') as cleanup, \
             patch.object(runner, 'commit_snapshot') as commit, \
             patch.object(runner, 'seal_snapshot') as seal, \
             patch.object(Path, 'read_bytes', side_effect=AssertionError('initializer read source archive')):
            runner.initialize_checkout(pathspec)
        cleanup.assert_called_once_with(self.root)
        commit.assert_called_once_with(pathspec)
        seal.assert_called_once_with(self.snapshot, bootstrap)
        self.assertFalse(pathspec.exists())

    def test_cli_dispatches_on_host_and_selects_a_single_worker_row(self):
        for arguments, dispatch, row_only in ((['--dispatch', 'part', 'consumer'], True, False),
                                               (['--row', 'full', 'consumer'], False, True)):
            with self.subTest(arguments=arguments), \
                 patch.object(runner.TM, 'parse_workflow_yaml', return_value=self.workflow), \
                 patch.object(runner, 'WorkflowRun') as run:
                runner.main(arguments)
            self.assertEqual(run.call_args.kwargs.get('dispatch', False), dispatch)
            self.assertEqual(run.call_args.kwargs.get('row_only', False), row_only)
            run.return_value.run.assert_called_once_with('consumer')

    def test_cli_rejects_unknown_worker_modes_before_constructing_a_runner(self):
        with patch.object(runner.TM, 'parse_workflow_yaml', return_value=self.workflow), \
             patch.object(runner, 'WorkflowRun') as run, \
             self.assertRaisesRegex(ValueError, 'unsupported local CI row mode'):
            runner.main(['--row', 'unrecognized', 'consumer'])
        run.assert_not_called()

    def test_keyed_projection_excludes_other_jobs_rows_and_never_run_steps(self):
        self.workflow = {
            'name': 'keyed workflow metadata', 'permissions': {'contents': 'read'},
            'jobs': {
                'test': {'runs-on': 'ubuntu-24.04', 'needs': ['producer'],
                         'strategy': {'matrix': {'include': [
                             {'zig': '0.17.0', 'part': 'lean', 'examples': 'selected'},
                             {'zig': '0.16.0', 'part': 'lean', 'examples': 'OTHER_ROW_DATA'}]}},
                         'steps': [
                             {'name': 'selected', 'if': "matrix.zig == '0.17.0'", 'run': 'selected text'},
                             {'name': 'other row', 'if': "matrix.zig == '0.16.0'", 'run': 'OTHER_ROW_TEXT'},
                             {'name': 'never', 'if': False, 'run': 'NEVER_RUN_TEXT'}]},
                'producer': {'runs-on': 'ubuntu-24.04', 'needs': ['grandproducer'],
                             'steps': [{'name': 'keyed direct need', 'run': 'DIRECT_NEED_TEXT'}]},
                'grandproducer': {'runs-on': 'ubuntu-24.04',
                                  'steps': [{'name': 'transitive', 'run': 'TRANSITIVE_UNKEYED_TEXT'}]},
                'other': {'runs-on': 'ubuntu-24.04',
                          'steps': [{'name': 'unrelated', 'run': 'UNRELATED_JOB_TEXT'}]},
            }}
        payload = runner.job_payload(self.workflow, 'test/0.17.0/lean', self.digest, self.workflow_digest)
        encoded = runner.CR.canonical(payload)
        for unkeyed in ('OTHER_ROW_DATA', 'OTHER_ROW_TEXT', 'NEVER_RUN_TEXT',
                        'TRANSITIVE_UNKEYED_TEXT', 'UNRELATED_JOB_TEXT'):
            with self.subTest(unkeyed=unkeyed):
                self.assertNotIn(unkeyed, encoded)
        self.assertIn('DIRECT_NEED_TEXT', encoded)
        self.assertEqual(payload['definitions']['needs'], {'producer': self.workflow['jobs']['producer']})
        self.assertEqual(payload['definitions']['workflow'],
                         {'name': self.workflow['name'], 'permissions': self.workflow['permissions']})
        self.assertEqual(payload['row'], {'zig': '0.17.0', 'part': 'lean', 'examples': 'selected'})
        legacy_projection = {
            'job': runner.CR.job_definition(self.workflow['jobs']['test'], payload['row'], 'test'),
            'needs': {name: self.workflow['jobs'][name]
                      for name in runner.CR.needs_of(self.workflow['jobs']['test'])},
            'workflow': {key: value for key, value in self.workflow.items() if key != 'jobs'},
        }
        self.assertEqual(runner.CR.canonical(payload['definitions']), runner.CR.canonical(legacy_projection))

    def test_shared_key_projection_preserves_non_matrix_definitions_bytes(self):
        self.workflow['jobs']['consumer']['steps'] = [{'name': 'never', 'if': False, 'run': 'keyed text'}]
        selected = self.workflow['jobs']['consumer']
        legacy_projection = {
            'job': runner.CR.job_definition(selected, None, 'consumer'),
            'needs': {name: self.workflow['jobs'][name] for name in runner.CR.needs_of(selected)},
            'workflow': {key: value for key, value in self.workflow.items() if key != 'jobs'},
        }
        actual = runner.CR.keyed_definitions(self.workflow, 'consumer', None)
        self.assertEqual(runner.CR.canonical(actual), runner.CR.canonical(legacy_projection))
        self.assertEqual(actual['job']['steps'], selected['steps'])

    def test_worker_registry_does_not_require_unkeyed_transitive_jobs(self):
        self.workflow['jobs']['producer']['needs'] = ['grandproducer']
        self.workflow['jobs']['grandproducer'] = {'runs-on': 'ubuntu-24.04', 'steps': []}
        run = self.make_row('consumer')
        self.assertEqual(set(run.workflow['jobs']), {'consumer', 'producer'})
        self.assertEqual(run.workflow['jobs']['producer']['needs'], ['grandproducer'])
        self.assertNotIn('grandproducer', run.rows)

    def test_worker_constructor_and_main_never_read_the_full_workflow(self):
        self.prepare_row('consumer')
        full_workflow = self.root / '.github/workflows/ci.yml'
        actual_text, actual_bytes = Path.read_text, Path.read_bytes

        def text(path, *args, **kwargs):
            if path.absolute() == full_workflow:
                self.fail('worker read full workflow text')
            return actual_text(path, *args, **kwargs)

        def data(path, *args, **kwargs):
            if path.absolute() == full_workflow:
                self.fail('worker read full workflow bytes')
            return actual_bytes(path, *args, **kwargs)

        with patch.object(runner, 'in_container', return_value=True), \
             patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', data), \
             patch.object(runner.TM, 'parse_workflow_yaml', side_effect=AssertionError('worker parsed full YAML')):
            run = runner.WorkflowRun(None, self.artifacts, self.snapshot, row_only=True)
            with patch.object(runner, 'WorkflowRun', return_value=run), patch.object(run, 'run') as execute:
                runner.main(['--row', 'part', 'consumer'])
            execute.assert_called_once_with('consumer')
        self.assertEqual(run.workflow_sha, self.workflow_digest)

    def test_worker_rejects_a_full_workflow_argument(self):
        self.prepare_row()
        with patch.object(runner, 'in_container', return_value=True), \
             self.assertRaisesRegex(ValueError, 'never a full workflow'):
            runner.WorkflowRun(self.workflow, self.artifacts, self.snapshot, row_only=True)

    def test_job_payload_digest_and_source_mismatches_fail_during_loading(self):
        payload = self.prepare_row()
        path = self.snapshot / 'job.json'
        path.write_bytes(path.read_bytes() + b'\n')
        with patch.object(runner, 'in_container', return_value=True), \
             self.assertRaisesRegex(ValueError, 'payload digest'):
            runner.WorkflowRun(None, self.artifacts, self.snapshot, row_only=True)
        for change in ({'snapshot_sha256': '0' * 64}, {'part': 'other'}, {'job_id': 'other'},
                       {'row': {'zig': '0.17.0'}}, {'workflow_sha256': 'not a digest'}):
            raw = (runner.CR.canonical(payload | change) + '\n').encode()
            path.write_bytes(raw)
            with self.subTest(change=change), \
                 patch.dict(os.environ, AIR2LEAN_LOCAL_JOB_PAYLOAD_SHA256=hashlib.sha256(raw).hexdigest()), \
                 patch.object(runner, 'in_container', return_value=True), self.assertRaises(ValueError):
                runner.WorkflowRun(None, self.artifacts, self.snapshot, row_only=True)

    def test_worker_rejects_a_different_part_without_executing_a_row(self):
        run = self.make_row('producer')
        with patch.object(run, 'run_row') as execute, \
             self.assertRaisesRegex(ValueError, 'does not select this part'):
            run.run('consumer')
        execute.assert_not_called()

    def test_upload_receipt_cannot_add_an_undeclared_artifact(self):
        self.workflow['jobs']['producer']['steps'] = [
            {'name': 'own artifact', 'uses': 'actions/upload-artifact@pin',
             'with': {'name': 'owned', 'path': 'result.tar'}}]
        run = self.make_dispatch()
        payload = runner.job_payload(self.workflow, 'producer', self.digest, self.workflow_digest)
        payload_sha = hashlib.sha256((runner.CR.canonical(payload) + '\n').encode()).hexdigest()
        self.receipt('producer', uploads=['foreign'])
        raw = (self.results / 'producer/row.json').read_bytes()
        with self.assertRaisesRegex(ValueError, 'upload is not declared by this row'):
            run.validate_row_receipt('producer', payload, payload_sha, {}, raw, True)

    def test_export_tree_accepts_regular_files_and_rejects_links(self):
        directory = self.root / 'export'
        directory.mkdir()
        (directory / 'regular').write_text('exported data\n')
        runner.check_export_tree(directory)
        (directory / 'link').symlink_to(self.root / '.github/workflows/ci.yml')
        with self.assertRaisesRegex(ValueError, 'unsafe local CI export entry'):
            runner.check_export_tree(directory)


if __name__ == '__main__':
    unittest.main()
