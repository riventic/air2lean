#!/usr/bin/env python3
"""Host-dispatch and single-row boundaries, without toolchain builds or Docker."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
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
        for path in (self.snapshot, self.artifacts, self.imports, self.root / '.github/workflows'):
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

    def make_row(self):
        (self.snapshot / 'source.tar').unlink(missing_ok=True)
        with patch.object(runner, 'in_container', return_value=True):
            return runner.WorkflowRun(self.workflow, self.artifacts, self.snapshot, row_only=True)

    def make_dispatch(self):
        return runner.WorkflowRun(self.workflow, self.artifacts, self.snapshot, dispatch=True, restricted=True)

    def receipt(self, selected, *, uploads=(), refs=None, **changes):
        report = {'part': selected, 'success': True, 'snapshot_sha256': self.digest, 'source': self.stamp,
                  'workflow_sha256': self.workflow_digest, 'image_id': IMAGE, 'runner': 'linux/amd64',
                  'producer_refs': {} if refs is None else refs, 'uploads': list(uploads)}
        report.update(changes)
        directory = self.artifacts / selected.replace('/', '-')
        directory.mkdir(exist_ok=True)
        (directory / 'row.json').write_text(json.dumps(report))

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
            runner.WorkflowRun(self.workflow, self.artifacts, self.snapshot, row_only=True)

    def test_row_never_loads_archive_inventory_or_history_bytes(self):
        history = self.snapshot / 'main.bundle'
        history.write_bytes(b'unrestricted preflight history')
        (self.snapshot / 'source.tar').unlink()
        actual_read = Path.read_bytes

        def read(path):
            if path.parent == self.snapshot:
                self.fail(f'row loaded snapshot bytes: {path.name}')
            return actual_read(path)

        with patch.object(Path, 'read_bytes', read), patch.object(runner, 'in_container', return_value=True):
            run = runner.WorkflowRun(self.workflow, self.artifacts, self.snapshot, row_only=True)
        self.assertIsNone(run.source)
        self.assertIsNone(run.inventory)
        self.assertEqual(run.history, history)
        self.assertEqual(run.source_sha, self.digest)

    def test_row_executes_one_job_without_reset_or_dependency_execution(self):
        run = self.make_row()
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

        with patch.object(runner, 'call', side_effect=container):
            run.run('producer')

    def test_dispatch_rejects_failed_or_mismatched_row_receipts(self):
        changes = ({'success': False}, {'snapshot_sha256': '0' * 64},
                   {'workflow_sha256': '0' * 64}, {'image_id': 'sha256:' + '0' * 64},
                   {'runner': 'linux/arm64'}, {'part': 'consumer'}, {'source': 'different snapshot'},
                   {'producer_refs': {'unexpected': self.producer_ref()}})
        for change in changes:
            with self.subTest(change=change):
                run = self.make_dispatch()

                def container(command, *, env):
                    self.receipt(command[-1], **change)

                with patch.object(runner, 'call', side_effect=container), \
                     self.assertRaisesRegex(ValueError, 'source-mismatched.*receipt'):
                    run.run('producer')
                self.assertEqual(run.completed, set())
                self.assertEqual(run.uploads, {})

    def test_dispatch_validates_all_uploads_before_registering_any(self):
        run = self.make_dispatch()
        (self.artifacts / 'uploads/present').mkdir(parents=True)

        def container(command, *, env):
            self.receipt(command[-1], uploads=['present', 'absent'])

        with patch.object(runner, 'call', side_effect=container), \
             self.assertRaisesRegex(ValueError, 'missing or duplicate produced artifact absent'):
            run.run('producer')
        self.assertEqual(run.uploads, {})
        self.assertEqual(run.upload_producers, {})

    def test_imports_require_a_matching_source_bound_producer(self):
        output = self.imports / 'compiled'
        output.mkdir()
        (self.imports / 'manifest.json').write_text(json.dumps({'compiled': str(output)}))
        (self.snapshot / 'source.tar').unlink()
        with patch.object(runner, 'in_container', return_value=True), \
             self.assertRaisesRegex(ValueError, 'matching producer references'):
            runner.WorkflowRun(self.workflow, self.artifacts, self.snapshot, row_only=True)
        ref = self.producer_ref() | {'snapshot_sha256': '0' * 64}
        with patch.dict(os.environ, AIR2LEAN_LOCAL_PRODUCERS=json.dumps({'compiled': ref})), \
             patch.object(runner, 'in_container', return_value=True), \
             self.assertRaisesRegex(ValueError, 'source-mismatched artifact producer'):
            runner.WorkflowRun(self.workflow, self.artifacts, self.snapshot, row_only=True)

    def test_row_imports_cannot_traverse_the_owned_import_namespace(self):
        (self.snapshot / 'source.tar').unlink()
        outside = self.root / 'outside'
        outside.mkdir()
        for name, value in (('..', str(self.imports / '..')), ('compiled', str(outside))):
            (self.imports / 'manifest.json').write_text(json.dumps({name: value}))
            with self.subTest(name=name), \
                 patch.dict(os.environ, AIR2LEAN_LOCAL_PRODUCERS=json.dumps({name: self.producer_ref()})), \
                 patch.object(runner, 'in_container', return_value=True), \
                 self.assertRaisesRegex(ValueError, 'invalid local CI artifact import|owned directory'):
                runner.WorkflowRun(self.workflow, self.artifacts, self.snapshot, row_only=True)

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
            self.assertEqual(run.call_args.kwargs['dispatch'], dispatch)
            self.assertEqual(run.call_args.kwargs['row_only'], row_only)
            run.return_value.run.assert_called_once_with('consumer')

    def test_cli_rejects_unknown_worker_modes_before_constructing_a_runner(self):
        with patch.object(runner.TM, 'parse_workflow_yaml', return_value=self.workflow), \
             patch.object(runner, 'WorkflowRun') as run, \
             self.assertRaisesRegex(ValueError, 'unsupported local CI row mode'):
            runner.main(['--row', 'unrecognized', 'consumer'])
        run.assert_not_called()


if __name__ == '__main__':
    unittest.main()
