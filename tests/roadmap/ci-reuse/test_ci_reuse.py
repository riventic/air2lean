#!/usr/bin/env python3
"""scripts/ci-reuse.py: keys, the restricted checkout, workflow guards, record lookup and records.

The restricted-checkout tests are the regression for docs/ci.md#restricted-checkout: a part that
reads a file outside its declared inputs fails (the file is withheld and unreadable; a read that
the permission does not stop, as root, is caught by check-restricted), and the restricted HEAD is
a function of the declared content and the tracked names only. Offline.
"""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[3]
_spec = importlib.util.spec_from_file_location('ci_reuse', ROOT / 'scripts/ci-reuse.py')
cr = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cr)
_spec = importlib.util.spec_from_file_location('check_tree', ROOT / 'scripts/check-tree.py')
check_tree = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(check_tree)


class Patterns(unittest.TestCase):
    def test_globs_and_exclusions(self):
        inputs = cr.Inputs(['scripts/**', '*.md', 'tests/**/run.py', 'docs/**', 'docs/exact.md'], ['docs/**'],
                           ['docs/keep.json'])
        for path in ('scripts/a.py', 'scripts/x/y', 'README.md', 'tests/t/run.py', 'tests/run.py', 'docs/keep.json',
                     'docs/exact.md'):  # an exact path is never excluded
            self.assertTrue(inputs.content(path), path)
        for path in ('docs/x.md', 'scriptsx/a', 'tests/t/other.py', 'docs/README.md'):
            self.assertFalse(inputs.content(path), path)

    def test_hashfiles_patterns(self):
        text = ("key: x-${{ hashFiles('a/*.zig', format('zig-patch/{0}/hook.patch', matrix.zig), '!b') }}-"
                "${{ hashFiles('lean-toolchain') }}")
        self.assertEqual(cr.hashfiles_patterns(text), {'a/*.zig', 'zig-patch/*/hook.patch', 'lean-toolchain'})


class GitObjectReads(unittest.TestCase):
    def test_shared_git_argv_disables_replacements_with_default_and_custom_env(self):
        root = Path('/private/tmp/ordinary-repository')
        for environ in (None, {'GIT_INDEX_FILE': 'ordinary-index'}):
            with self.subTest(environ=environ), \
                 patch.object(cr.subprocess, 'run',
                              return_value=subprocess.CompletedProcess([], 0, b'ordinary\n', b'')) as run:
                self.assertEqual(cr.git(root, 'ls-tree', 'HEAD', env=environ), b'ordinary\n')
                self.assertEqual(run.call_args.args[0],
                                 ['git', '--no-replace-objects', '-C', str(root), 'ls-tree', 'HEAD'])
                self.assertIs(run.call_args.kwargs['env'], environ)

    def test_final_seal_existence_check_disables_replacements(self):
        with tempfile.TemporaryDirectory(prefix='air2lean git argv ') as root, \
             patch.object(cr, 'git', return_value=b''), \
             patch.object(cr.subprocess, 'run',
                          return_value=subprocess.CompletedProcess([], 1, b'', b'')) as run:
            tested = '1' * 40
            cr.seal_history(Path(root), tested)
            run.assert_called_once_with(
                ['git', '--no-replace-objects', '-C', root, 'cat-file', '-e', tested + '^{tree}'],
                capture_output=True)


class Workflow(unittest.TestCase):
    def test_reuse_and_release_share_one_captured_data_and_expression_helper(self):
        self.assertIs(cr.TM,cr.RR.TM)

    def test_real_yaml_integer_part_identity_and_scalar_kinds(self):
        text='''jobs:
  test:
    strategy:
      matrix:
        include:
          - zig: "0.17.0"
            part: test
            shard: 1
            full: FALSE
            mutate: null
            examples: 0.0
'''
        path=self.root/'.github/workflows/ci.yml';path.write_text(text)
        workflow=cr.load_workflow(self.root)
        parts=cr.parts(workflow)
        self.assertEqual(list(parts),['test/0.17.0/test/1'])
        row=parts['test/0.17.0/test/1'][1]
        self.assertIs(type(row['shard']),int)
        self.assertIs(row['full'],False);self.assertIsNone(row['mutate'])
        self.assertIs(type(row['examples']),float)

    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='air2lean ci-reuse ')
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        for rel in ('.github/workflows/ci.yml', '.github/ci-inputs.json'):
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / rel, self.root / rel)

    def edit(self, rel, old, new):
        path = self.root / rel
        text = path.read_text()
        self.assertIn(old, text)
        path.write_text(text.replace(old, new, 1))

    def test_committed_workflow_is_guarded_and_declared(self):
        self.assertEqual(cr.check_workflow(ROOT), [])

    def test_unguarded_step_fails(self):
        self.edit('.github/workflows/ci.yml', "        if: ${{ !env.AIR2LEAN_REUSED && matrix.part == 'inputs' }}\n",
                  "        if: ${{ matrix.part == 'inputs' }}\n")
        self.assertTrue(any('without !env.AIR2LEAN_REUSED' in e for e in cr.check_workflow(self.root)))

    def test_undeclared_part_and_run_specific_expression_fail(self):
        data = json.loads((self.root / '.github/ci-inputs.json').read_text())
        data['parts'].pop('test/0.16.0/inputs')
        (self.root / '.github/ci-inputs.json').write_text(json.dumps(data))
        self.edit('.github/workflows/ci.yml', 'run: python3 tests/roadmap/inventory/test_inventory.py',
                  'run: python3 tests/roadmap/inventory/test_inventory.py ${{ github.sha }}')
        errors = cr.check_workflow(self.root)
        self.assertTrue(any('test/0.16.0/inputs has no declaration' in e for e in errors))
        self.assertTrue(any('run-specific github.* expression' in e for e in errors))

    def test_reusable_part_without_inputs_fails(self):
        data = json.loads((self.root / '.github/ci-inputs.json').read_text())
        data['parts']['bitops-native-arm'] = {'note': 'nothing declared'}
        (self.root / '.github/ci-inputs.json').write_text(json.dumps(data))
        self.assertTrue(any('declares no inputs' in e for e in cr.check_workflow(self.root)))

    def test_unrestricted_support_job_fails(self):
        self.edit('.github/workflows/ci.yml', '        run: python3 scripts/ci-reuse.py restrict --support lake --seal\n',
                  '        run: "true"\n')
        self.edit('.github/workflows/ci.yml', '      - name: Restrict the checkout to the declared inputs\n',
                  '      - name: Something else\n')
        self.assertTrue(any('support job lake' in e for e in cr.check_workflow(self.root)))


class Repository(unittest.TestCase):
    """A scratch repository with the reuse machinery, the real workflow and a small tree."""

    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='air2lean ci-reuse key ')
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name) / 'repo'
        for rel in ('.github/workflows/ci.yml', *cr.MACHINERY):
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / rel, self.root / rel)
        data = json.loads((self.root / '.github/ci-inputs.json').read_text())
        data['parts']['bitops-native-arm'] = {'inputs': ['tests/roadmap/bitops-native/**', 'docs/**'],
                                              'exclude': ['docs/**/*.md']}
        (self.root / '.github/ci-inputs.json').write_text(json.dumps(data))
        for rel in ('tests/roadmap/bitops-native/gen.py', 'docs/notes.md', 'docs/table.json'):
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.root / rel).write_text('one\n')
        self.git('init', '-q')
        self.commit()

    def git(self, *args):
        return subprocess.run(['git', '-C', str(self.root), '-c', 'user.name=t', '-c', 'user.email=t@t', *args],
                              check=True, capture_output=True, text=True).stdout.strip()

    def commit(self):
        self.git('add', '-A')
        self.git('commit', '-qm', 'x', '--allow-empty')

    def key(self, part='bitops-native-arm', environ=None):
        return cr.key_of(cr.manifest(self.root, part, environ or {}))

    def restrict(self, part='bitops-native-arm'):
        data = cr.load_declarations(self.root)
        job_id, _ = cr.parts(cr.load_workflow(self.root))[part]
        with contextlib.redirect_stdout(io.StringIO()):
            return cr.restrict(self.root, cr.part_inputs(self.root, data, job_id, entry=data['parts'][part]), part)


class RevisionCapture(Repository):
    """A mutable ref may advance, but one operation consumes one immutable committed tree."""

    PART = 'bitops-native-arm'

    def text_versions(self):
        first = self.git('rev-parse', 'HEAD')
        expected = cr.manifest(self.root, self.PART, {})
        (self.root / 'docs/table.json').write_text('two\n')
        self.commit()
        second = self.git('rev-parse', 'HEAD')
        self.git('checkout', '--quiet', '--detach', first)
        return first, second, expected

    def test_manifest_pins_default_and_explicit_mutable_revisions(self):
        for requested in (None, 'captured'):
            for advance in (False, True):
                with self.subTest(requested=requested, advance=advance):
                    fixture = RevisionCapture()
                    try:
                        fixture.setUp()
                        first, second, expected = fixture.text_versions()
                        ref = 'refs/heads/captured' if requested else 'HEAD'
                        fixture.git('update-ref', ref, first)
                        actual_load = cr.load_workflow

                        def load(*args):
                            workflow = actual_load(*args)
                            if advance:
                                fixture.git('update-ref', ref, second)
                            return workflow

                        with patch.object(cr, 'load_workflow', side_effect=load) as loader:
                            actual = cr.manifest(fixture.root, self.PART, {}, revision=requested)
                        self.assertEqual(actual, expected)
                        self.assertEqual(cr.key_of(actual), cr.key_of(expected))
                        self.assertEqual(loader.call_count, 1)
                        self.assertEqual(fixture.git('rev-parse', ref), second if advance else first)
                    finally:
                        fixture.doCleanups()

    def test_direct_restriction_reads_the_resolved_commit_tree(self):
        for advance in (False, True):
            with self.subTest(advance=advance):
                fixture = RevisionCapture()
                try:
                    fixture.setUp()
                    first, second, expected = fixture.text_versions()
                    data = cr.load_declarations(fixture.root)
                    inputs = cr.part_inputs(fixture.root, data, self.PART,
                                            entry=cr.declaration(data, self.PART))
                    actual_tree = cr.tracked_tree

                    def tree(root, revision='HEAD'):
                        if advance:
                            fixture.git('update-ref', 'HEAD', second)
                        return actual_tree(root, revision)

                    with patch.object(cr, 'tracked_tree', side_effect=tree) as reader, \
                         contextlib.redirect_stdout(io.StringIO()):
                        cr.restrict(fixture.root, inputs, self.PART)
                    self.assertEqual(reader.call_count, 1)
                    self.assertEqual(cr.restricted_state(fixture.root)['tested_commit'], first)
                    self.assertEqual((fixture.root / 'docs/table.json').read_text(), 'one\n')
                    expected_blob = next(item[2] for item in expected['content'] if item[0] == 'docs/table.json')
                    self.assertEqual(fixture.git('rev-parse', 'HEAD:docs/table.json'), expected_blob)
                finally:
                    fixture.doCleanups()

    def test_decision_key_export_and_restriction_share_one_commit(self):
        for advance in (False, True):
            with self.subTest(advance=advance):
                fixture = RevisionCapture()
                try:
                    fixture.setUp()
                    first, second, expected = fixture.text_versions()
                    temp = fixture.root.parent / 'decision-temp'
                    temp.mkdir()
                    environ = {'GITHUB_RUN_ID': '5', 'AIR2LEAN_EVENT': 'workflow_dispatch',
                               'RUNNER_TEMP': str(temp), 'GITHUB_ENV': str(temp / 'decision.env')}
                    actual_manifest = cr._manifest

                    def manifest(*args):
                        captured = actual_manifest(*args)
                        if advance:
                            fixture.git('update-ref', 'HEAD', second)
                        return captured

                    with patch.object(cr, '_manifest', side_effect=manifest), \
                         contextlib.redirect_stdout(io.StringIO()):
                        self.assertEqual(cr.decide(fixture.root, self.PART, 'null', environ), 0)
                    saved = json.loads((temp / 'ci-reuse/manifest.json').read_text())
                    exported = dict(line.split('=', 1) for line in (temp / 'decision.env').read_text().splitlines())
                    self.assertEqual(saved, expected)
                    self.assertEqual(exported['AIR2LEAN_REUSE_KEY'], cr.key_of(expected))
                    self.assertEqual(exported['AIR2LEAN_TESTED_COMMIT'], first)
                    self.assertEqual(cr.restricted_state(fixture.root)['tested_commit'], first)
                    self.assertEqual((fixture.root / 'docs/table.json').read_text(), 'one\n')
                    expected_blob = next(item[2] for item in expected['content'] if item[0] == 'docs/table.json')
                    self.assertEqual(fixture.git('rev-parse', 'HEAD:docs/table.json'), expected_blob)
                finally:
                    fixture.doCleanups()


class Keys(Repository):
    """A key changes with a declared input or any tracked name, and stays with undeclared content."""

    def test_recorded_workflow_data_never_reloads_mutated_live_text(self):
        revision=self.git('rev-parse','HEAD')
        expected=cr.load_workflow(self.root,revision)
        (self.root/'.github/workflows/ci.yml').write_text('value: left: right\n')
        self.assertEqual(cr.load_workflow(self.root,revision),expected)
        with self.assertRaisesRegex(cr.RR.ReleaseError,r'ci.yml:1: unsupported YAML syntax'):
            cr.load_workflow(self.root)

    def test_declared_and_undeclared_changes(self):
        first = self.key()
        (self.root / 'docs/notes.md').write_text('two\n')  # excluded
        self.commit()
        self.assertEqual(self.key(), first)
        (self.root / 'docs/table.json').write_text('two\n')
        self.commit()
        changed = self.key()
        self.assertNotEqual(changed, first)
        (self.root / 'docs/new.md').write_text('a name\n')  # every tracked name is an input
        self.commit()
        self.assertNotEqual(self.key(), changed)
        self.assertNotEqual(self.key(environ={'ImageVersion': '2'}), self.key(environ={'ImageVersion': '3'}))

    def test_key_does_not_name_the_commit(self):
        first = self.key('macos/0.16.0')
        self.commit()
        self.assertEqual(self.key('macos/0.16.0'), first)

    def test_steps_of_other_rows_are_not_inputs(self):
        part, workflow = 'test/0.16.0/mutation/1', self.root / '.github/workflows/ci.yml'
        data = json.loads((self.root / '.github/ci-inputs.json').read_text())
        data['parts'][part] = {'inputs': ['tests/roadmap/bitops-native/**']}  # not the workflow file
        (self.root / '.github/ci-inputs.json').write_text(json.dumps(data))
        self.commit()
        text, anchor = workflow.read_text(), '      - name: Op effects table source checks\n'
        self.assertIn(anchor, text)

        def key_with_step(condition):
            workflow.write_text(text.replace(anchor, '      - name: Added\n        if: %s\n        run: echo added\n\n'
                                             % condition + anchor, 1))
            self.commit()
            return self.key(part)

        first = self.key(part)
        self.assertEqual(key_with_step("${{ !env.AIR2LEAN_REUSED && matrix.part == 'lean' }}"), first)
        self.assertEqual(key_with_step("${{ !env.AIR2LEAN_REUSED && matrix.zig == '0.17.0' }}"), first)
        for condition in ("${{ !env.AIR2LEAN_REUSED && matrix.part == 'mutation' }}",  # this row
                          "${{ !env.AIR2LEAN_REUSED }}",                                 # every row
                          "${{ !env.AIR2LEAN_REUSED && failure() }}",                    # a status function
                          "${{ !env.AIR2LEAN_REUSED && env.OTHER == 'x' }}"):            # run-time state
            self.assertNotEqual(key_with_step(condition), first, condition)

    def test_needed_support_inputs_and_generated_files_are_inputs(self):
        part = 'test/0.16.0/mutation/1'
        data = json.loads((self.root / '.github/ci-inputs.json').read_text())
        data['parts'][part] = {'inputs': ['tests/roadmap/bitops-native/**']}
        (self.root / '.github/ci-inputs.json').write_text(json.dumps(data))
        (self.root / 'Proofs').mkdir()
        (self.root / 'Proofs/A.lean').write_text('one\n')
        self.commit()
        first = self.key(part)
        (self.root / 'Proofs/A.lean').write_text('two\n')  # an input of `lake`, which the row needs
        self.commit()
        changed = self.key(part)
        self.assertNotEqual(changed, first)
        registry = json.loads((self.root / 'assurance/generated.json').read_text())
        installed = self.root / registry['groups'][0]['paths'][0]
        installed.parent.mkdir(parents=True, exist_ok=True)
        installed.write_text('installed\n')  # a whole-tree generated file the row installs
        self.assertNotEqual(self.key(part), changed)
        self.assertEqual(self.key(), self.key())  # bitops-native-arm needs no `generated`

    def test_reuse_false_has_no_key(self):
        data = json.loads((self.root / '.github/ci-inputs.json').read_text())
        data['parts']['bitops-native-arm'] = {'reuse': False}
        (self.root / '.github/ci-inputs.json').write_text(json.dumps(data))
        self.assertIsNone(cr.manifest(self.root, 'bitops-native-arm', {}))


class Restricted(Repository):
    def test_head_is_a_function_of_declared_content_and_names(self):
        tested = self.git('rev-parse', 'HEAD')
        first = self.restrict()
        self.assertEqual(self.git('rev-list', '--count', 'HEAD'), '1')
        self.assertEqual(self.git('log', '-1', '--format=%an %ad', '--date=raw'), 'air2lean restricted checkout 0 +0000')
        self.assertEqual(self.git('status', '--porcelain'), '')
        # Another commit with the same declared content and names: the same restricted HEAD.
        cr.unrestrict(self.root)
        self.assertEqual(self.git('rev-parse', 'HEAD'), tested)
        (self.root / 'docs/notes.md').write_text('prose edit\n')
        self.commit()
        self.assertEqual(self.restrict(), first)

    def test_undeclared_file_is_withheld_and_a_read_fails(self):
        """The regression of docs/ci.md#restricted-checkout: reading an undeclared file fails."""
        self.restrict()
        withheld = self.root / 'docs/notes.md'
        self.assertEqual((self.root / 'docs/table.json').read_text(), 'one\n')  # declared
        self.assertEqual(withheld.stat().st_mode & 0o777, 0)
        self.assertIn('docs/notes.md', self.git('ls-files'))  # its name stays visible
        if os.geteuid():
            with self.assertRaises(PermissionError):
                withheld.read_text()
            self.assertNotEqual(subprocess.run(['cat', str(withheld)], capture_output=True).returncode, 0)
        # A read that the permission does not stop (root) is still caught.
        os.chmod(withheld, 0o644)
        withheld.read_bytes()
        os.chmod(withheld, 0)
        self.assertEqual(cr.check_restricted(self.root, as_root=True), ['docs/notes.md: withheld file was read'])
        os.chmod(withheld, 0o644)
        withheld.write_text('changed\n')
        self.assertEqual(cr.check_restricted(self.root), ['docs/notes.md: withheld file was changed'])

    def test_sealed_checkout_no_longer_holds_the_withheld_content(self):
        (self.root / 'docs/notes.md').write_text('only here\n')
        self.commit()
        self.git('remote', 'add', 'origin', 'https://example.invalid/repo.git')
        self.git('config', 'http.https://example.invalid/.extraheader', 'AUTHORIZATION: basic x')
        tested = self.git('rev-parse', 'HEAD')
        withheld_blob = self.git('rev-parse', 'HEAD:docs/notes.md')
        data = cr.load_declarations(self.root)
        with contextlib.redirect_stdout(io.StringIO()):
            cr.restrict(self.root, cr.part_inputs(self.root, data, 'bitops-native-arm',
                                                  entry=data['parts']['bitops-native-arm']), 'x', seal=True)
        self.assertEqual(self.git('remote'), '')
        self.assertEqual(self.git('config', '--local', '--list').count('extraheader'), 0)
        for obj in (tested, withheld_blob):
            self.assertNotEqual(subprocess.run(['git', '-C', str(self.root), 'cat-file', '-e', obj],
                                               capture_output=True).returncode, 0)
        self.assertEqual(self.git('for-each-ref'), '')

    def test_check_tree_withholds_too(self):
        self.restrict()
        dest = self.root.parent / 'tree'
        check_tree.create(dest, [], self.root)
        self.assertEqual((dest / 'docs/table.json').read_text(), 'one\n')
        self.assertEqual((dest / 'docs/notes.md').stat().st_mode & 0o777, 0)
        os.chmod(dest / 'docs/notes.md', 0o644)
        self.assertEqual((dest / 'docs/notes.md').read_bytes(), cr.WITHHELD)

    def test_record_requires_the_restricted_run_and_unchanged_inputs(self):
        tested = self.git('rev-parse', 'HEAD')
        key = self.key()
        temp = self.root.parent / 'runner-temp'
        (temp / 'ci-reuse').mkdir(parents=True)
        (temp / 'ci-reuse/manifest.json').write_text(cr.canonical(cr.manifest(self.root, 'bitops-native-arm', {})))
        environ = {'AIR2LEAN_PART': 'bitops-native-arm', 'AIR2LEAN_REUSE_KEY': key, 'AIR2LEAN_TESTED_COMMIT': tested,
                   'RUNNER_TEMP': str(temp)}
        out = self.root.parent / 'record.json'
        with self.assertRaises(cr.ReuseError):  # not restricted
            cr.record(self.root, out, environ)
        self.restrict()
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(cr.record(self.root, out, environ), 0)
        body = json.loads(out.read_text())
        self.assertEqual((body['key'], body['tested_commit']), (key, tested))
        self.assertEqual(body['withheld'], 2)  # docs/notes.md and the workflow file
        with self.assertRaises(cr.ReuseError):
            cr.record(self.root, out, dict(environ, AIR2LEAN_REUSE_KEY='0' * 64))


class DataIdentity(Repository):
    def decision_fixture(self):
        self.workflow(self.ROW.replace('part: data','part: first')+
                      self.ROW.replace('part: data','part: second'))
        declarations={'schema':cr.DECLARATIONS_SCHEMA,'parts':{
            'test/0.17.0/'+part:{'inputs':['scripts/**']} for part in ('first','second')}}
        (self.root/cr.DECLARATIONS).write_text(json.dumps(declarations));self.commit()
        workflow=cr.load_workflow(self.root);parts=cr.parts(workflow)
        target='test/0.17.0/first';row=parts[target][1]
        temp=self.root.parent/'decision-temp';temp.mkdir()
        environ={'GITHUB_RUN_ID':'100','GITHUB_RUN_ATTEMPT':'1','AIR2LEAN_EVENT':'pull_request',
                 'RUNNER_TEMP':str(temp),'GITHUB_REPOSITORY':Lookup.REPO,
                 'GITHUB_ENV':str(self.root.parent/'decision.env'),
                 'GITHUB_STEP_SUMMARY':str(self.root.parent/'decision.summary')}
        return target,row,environ,parts

    def test_actual_pr_miss_hit_selfcheck_and_lookup_error_use_captured_parts(self):
        for mode in ('miss','hit','selfcheck','error'):
            with self.subTest(mode=mode):
                fixture=DataIdentity();fixture.setUp()
                try:
                    target,row,environ,parts=fixture.decision_fixture()
                    desired=target if mode=='selfcheck' else next(part for part in parts if part!=target)
                    environ['GITHUB_RUN_ID']=next(str(n) for n in range(100,200)
                        if cr.self_check_part(dict(environ,GITHUB_RUN_ID=str(n)),parts)==desired)
                    preimage=cr.manifest(fixture.root,target,environ);key=cr.key_of(preimage)
                    responses=Lookup();artifact=dict(responses.artifact(),name='ci-reuse-'+key)
                    jobs=[dict(responses.JOBS[0],name=preimage['job_name'])]
                    fetch=responses.fetch_for([] if mode=='miss' else [artifact],responses.run_data(),jobs)
                    if mode=='error':
                        def fetch(*_args):raise OSError('synthetic lookup failure')
                    with patch.object(cr,'self_check_part',wraps=cr.self_check_part) as chooser,\
                         contextlib.redirect_stdout(io.StringIO()):
                        self.assertEqual(cr.decide(fixture.root,'test',json.dumps(row),environ,fetch),0)
                    self.assertEqual(set(chooser.call_args.args[1]),set(parts))
                    exported=Path(environ['GITHUB_ENV']).read_text()
                    self.assertEqual('AIR2LEAN_REUSED=u' in exported,mode=='hit')
                    self.assertEqual('AIR2LEAN_SELF_CHECK=u' in exported,mode=='selfcheck')
                    self.assertEqual(cr.restricted_state(fixture.root) is not None,mode!='hit')
                finally:fixture.doCleanups()

    def test_actual_final_restriction_uses_manifest_capture_after_live_workflow_change(self):
        target,row,environ,_parts=self.decision_fixture()
        actual_manifest=cr._manifest
        def manifest(*args):
            preimage=actual_manifest(*args)
            (self.root/cr.WORKFLOW).write_text('value: malformed:\n')
            return preimage
        with patch.object(cr,'_manifest',side_effect=manifest),\
             patch.object(cr,'load_workflow',wraps=cr.load_workflow) as loader,\
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(cr.decide(self.root,'test',json.dumps(row),environ,lambda *_args:{'artifacts':[]}),0)
        self.assertEqual(loader.call_count,1)
        self.assertIsNotNone(cr.restricted_state(self.root))

    def test_one_declaration_capture_supplies_manifest_and_final_restriction(self):
        for change_after_capture in (False, True):
            with self.subTest(change_after_capture=change_after_capture):
                fixture = DataIdentity()
                fixture.setUp()
                try:
                    target, row, environ, _parts = fixture.decision_fixture()
                    path = fixture.root / cr.DECLARATIONS
                    data = json.loads(path.read_text())
                    data['parts'][target]['inputs'].append('docs/table.json')
                    path.write_text(json.dumps(data))
                    fixture.commit()
                    expected = cr.manifest(fixture.root, target, environ)
                    actual_load, actual_inputs = cr.load_declarations, cr.part_inputs
                    selections = []

                    def capture_declarations(*args):
                        captured = actual_load(*args)
                        if change_after_capture:
                            changed = json.loads(json.dumps(captured))
                            changed['parts'][target]['inputs'].remove('docs/table.json')
                            path.write_text(json.dumps(changed))
                        return captured

                    def capture_inputs(*args, **kwargs):
                        selected = actual_inputs(*args, **kwargs)
                        selections.append(selected)
                        return selected

                    with patch.object(cr, 'load_declarations', side_effect=capture_declarations) as loader, \
                         patch.object(cr, '_parts', wraps=cr._parts) as qualifier, \
                         patch.object(cr, 'part_inputs', side_effect=capture_inputs), \
                         patch.object(cr, 'restrict', wraps=cr.restrict) as restriction, \
                         contextlib.redirect_stdout(io.StringIO()):
                        self.assertEqual(cr.decide(fixture.root, 'test', json.dumps(row), environ,
                                                   lambda *_args: {'artifacts': []}), 0)
                    self.assertEqual(loader.call_count, 1)
                    self.assertEqual(qualifier.call_count, 1)
                    self.assertEqual(len(selections), 1)
                    self.assertIs(restriction.call_args.args[1], selections[0])
                    recorded = json.loads((Path(environ['RUNNER_TEMP']) / 'ci-reuse/manifest.json').read_text())
                    self.assertEqual(recorded, expected)
                    self.assertEqual(recorded['declaration'], selections[0].describe())
                    self.assertIn('docs/table.json', [item[0] for item in recorded['content']])
                    self.assertEqual((fixture.root / 'docs/table.json').read_text(), 'one\n')
                    self.assertIsNotNone(cr.restricted_state(fixture.root))
                finally:
                    fixture.doCleanups()

    def test_multiline_part_labels_refuse_before_decision_side_effects(self):
        self.workflow(self.ROW.replace('part: data', 'part: |-\n              ordinary\n              continued'))
        workflow = cr.load_workflow(self.root)
        row = cr.job_rows(workflow['jobs']['test'])[0]
        self.assertEqual(row['part'], 'ordinary\ncontinued')
        for separator in ('\n', '\r', '\0'):
            row['part'] = 'ordinary' + separator + 'continued'
            with self.subTest(separator=repr(separator)), \
                 patch.object(cr, 'load_workflow', return_value=workflow), \
                 patch.object(cr, 'load_declarations') as declarations, \
                 patch.object(cr, '_manifest') as manifest, \
                 patch.object(cr, 'restrict') as restriction, \
                 patch.object(cr, 'append') as append:
                for action in (lambda: cr.parts(workflow),
                               lambda: cr.manifest(self.root, 'test/0.17.0/' + row['part'], {}),
                               lambda: cr.decide(self.root, 'test', json.dumps(row), {'GITHUB_RUN_ID': '5'})):
                    with self.assertRaisesRegex(cr.ReuseError, 'part ID .*one environment-file value'):
                        action()
                declarations.assert_not_called()
                manifest.assert_not_called()
                restriction.assert_not_called()
                append.assert_not_called()

    def test_valid_part_labels_keep_their_original_bytes(self):
        for label in ('ordinary-label', ' ordinary label ', 'caf\u00e9', 'ordinary/label'):
            with self.subTest(label=label):
                self.workflow(self.ROW.replace('part: data', 'part: "' + label + '"'))
                workflow = cr.load_workflow(self.root)
                row = cr.job_rows(workflow['jobs']['test'])[0]
                expected = 'test/0.17.0/' + label
                self.assertEqual(cr.part_id('test', row), expected)
                self.assertEqual(list(cr.parts(workflow)), [expected])
                with contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(cr.decide(self.root, 'test', json.dumps(row), {}), 0)

    def test_stable_wire_numbers_select_unchanged_original_source_ids(self):
        for literal,wire in (('1.0',1),('1',1),('0.5',0.5),('1000000000000000000',1e18)):
            with self.subTest(literal=literal):
                self.workflow(self.ROW+'            shard: '+literal+'\n');self.commit()
                source_row=cr.job_rows(cr.load_workflow(self.root)['jobs']['test'])[0]
                source_part=cr.part_id('test',source_row);self.declarations(source_part)
                incoming=dict(source_row,shard=wire)
                with patch.object(cr,'_manifest',wraps=cr._manifest) as manifest,contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(cr.decide(self.root,'test',json.dumps(incoming),
                                               {'GITHUB_RUN_ID':'5','AIR2LEAN_EVENT':'schedule'}),0)
                self.assertEqual(manifest.call_args.args[1],source_part)
                self.assertIs(type(cr.job_rows(cr.load_workflow(self.root)['jobs']['test'])[0]['shard']),
                              float if '.' in literal else int)
        self.workflow(self.ROW+'            options:\n              amounts: [1.0, 2]\n');self.commit()
        row=cr.job_rows(cr.load_workflow(self.root)['jobs']['test'])[0]
        incoming=dict(row,options={'amounts':[1,2]})
        with contextlib.redirect_stdout(io.StringIO()):self.assertEqual(cr.decide(self.root,'test',json.dumps(incoming),{}),0)
        self.assertIs(type(cr.job_rows(cr.load_workflow(self.root)['jobs']['test'])[0]['options']['amounts'][0]),float)

    def test_wire_identity_is_per_job_and_collisions_name_both_source_rows(self):
        self.workflow(self.ROW+'            shard: 1\n'+self.ROW+'            shard: 1.0\n')
        with self.assertRaisesRegex(cr.ReuseError,'repeated runner wire row') as caught:
            cr.parts(cr.load_workflow(self.root))
        self.assertIn("'shard': 1}",str(caught.exception));self.assertIn("'shard': 1.0}",str(caught.exception))
        first=self.workflow(self.ROW+'            shard: 1.0\n')
        (self.root/cr.WORKFLOW).write_text(first+first.replace('  test:','  other:').split('jobs:\n',1)[1])
        workflow=cr.load_workflow(self.root)
        self.assertEqual(set(cr.parts(workflow)),{'test/0.17.0/data/1.0','other/0.17.0/data/1.0'})
        for job in ('test','other'):
            row=cr.job_rows(workflow['jobs'][job])[0]
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(cr.decide(self.root,job,json.dumps(dict(row,shard=1)),{}),0)

    def test_numeric_roundtrip_refuses_lossy_float_integer_and_recursive_values(self):
        for field in ('            shard: 1.0000000000000002\n',
                      '            shard: 1000000000000000001\n',
                      '            shard: 9007199254740993\n',
                      '            options: [1, 1.0000000000000002]\n',
                      '            options:\n              amount: 1000000000000000001\n'):
            with self.subTest(field=field):
                self.workflow(self.ROW+field)
                with self.assertRaisesRegex(cr.ReuseError,'test row .*does not round-trip through binary64/G15') as caught:
                    cr.parts(cr.load_workflow(self.root))
                self.assertIn('options' if 'options' in field else 'shard',str(caught.exception))

    def test_job_and_matrix_free_typed_conditions_use_the_shared_qualifier(self):
        for scope in ('job','step'):
            for literal in ('0.0','[true]','\n      value: true' if scope=='job' else '\n          value: true'):
                text='''jobs:
  solo:
    runs-on: ubuntu-24.04
    steps:
      - name: Typed gate
        run: echo gate
'''
                text=text.replace('    steps:', '    if: '+literal+'\n    steps:') if scope=='job' else text.replace(
                    '        run:', '        if: '+literal+'\n        run:')
                (self.root/cr.WORKFLOW).write_text(text);self.declarations('solo');self.commit()
                with self.subTest(scope=scope,literal=literal),self.assertRaisesRegex(cr.ReuseError,
                    "job 'solo': unsupported condition DATA:" if scope=='job' else "step 'Typed gate': unsupported condition DATA:"):
                    cr.manifest(self.root,'solo',{})
        for literal in ('false','true','null',"matrix.unknown == 'runtime'"):
            text='''jobs:
  solo:
    runs-on: ubuntu-24.04
    if: CONDITION
    steps:
      - name: Supported gate
        if: CONDITION
        run: echo gate
'''.replace('CONDITION',literal)
            (self.root/cr.WORKFLOW).write_text(text);self.declarations('solo');self.commit()
            self.assertEqual(cr.manifest(self.root,'solo',{})['definitions']['job']['steps'][0]['name'],'Supported gate')

    def workflow(self,rows,condition='matrix.full',job='test'):
        text='''jobs:
  JOB:
    runs-on: ubuntu-24.04
    strategy:
      matrix:
        include:
'''.replace('JOB',job)+rows+'''    steps:
      - name: Full proof
        if: CONDITION
        run: echo full-proof
'''.replace('CONDITION',condition)
        (self.root/cr.WORKFLOW).write_text(text)
        return text

    ROW='''          - zig: "0.17.0"
            part: data
            examples: ""
            full: true
            mutate: false
'''

    def declarations(self,part):
        (self.root/cr.DECLARATIONS).write_text(json.dumps({'schema':cr.DECLARATIONS_SCHEMA,
                                                         'parts':{part:{'inputs':['scripts/**']}}}))

    def test_shared_matrix_boundary_refuses_axes_before_reuse_manifest(self):
        text=self.workflow(self.ROW,condition='${{ !matrix.flag }}')
        (self.root/cr.WORKFLOW).write_text(text.replace('        include:',
                                                      '        flag: [true]\n        include:',1))
        self.declarations('test/0.17.0/data');self.commit()
        with self.assertRaisesRegex(cr.RR.ReleaseError,'ci.yml: job test: only strategy.matrix.include is supported'):
            cr.manifest(self.root,'test/0.17.0/data',{})

    def test_real_yaml_repeated_part_ids_refuse_before_overwrite_in_all_consumers(self):
        for job in ('test','macos','bitops-native-arm'):
            for first,second in (('',''),('            shard: null\n',''),
                                 ('            shard: 1\n','            shard: "1"\n'),
                                 ('            shard: false\n','            shard: "False"\n')):
                with self.subTest(job=job,first=first,second=second):
                    self.workflow(self.ROW+first+self.ROW.replace('full: true','full: false')+second,job=job)
                    self.commit()
                    for action in (lambda:cr.parts(cr.load_workflow(self.root)),
                                   lambda:cr.manifest(self.root,job+'/0.17.0/data',{}),
                                   lambda:cr.check_workflow(self.root),
                                   lambda:cr.decide(self.root,job,'{}',{})):
                        with self.assertRaisesRegex(cr.ReuseError,'repeated part ID'):
                            action()

    def test_request_row_is_complete_type_sensitive_and_refuses_before_manifest(self):
        self.workflow(self.ROW);self.commit()
        row=cr.job_rows(cr.load_workflow(self.root)['jobs']['test'])[0]
        invalid=[dict(row,full=1),dict(row,mutate=0),dict(row,shard=None),
                 {key:value for key,value in row.items() if key!='examples'},dict(row,extra=None)]
        for request in invalid:
            with self.subTest(request=request),patch.object(cr,'_manifest',side_effect=AssertionError('manifest reached')):
                with self.assertRaisesRegex(cr.ReuseError,'requested job/row does not match'):
                    cr.decide(self.root,'test',json.dumps(request),{'GITHUB_RUN_ID':'5'})
        for raw in ('[]','false','{"zig":"0.17.0","zig":"0.17.0"}',
                    '{"x":NaN}','{"x":1e999}'):
            with self.subTest(raw=raw),self.assertRaisesRegex(cr.ReuseError,'unsupported request row'):
                cr.decide(self.root,'test',raw,{'GITHUB_RUN_ID':'5'})
        with self.assertRaisesRegex(cr.ReuseError,'requested job/row does not match'):
            cr.decide(self.root,'wrong-job',json.dumps(row),{'GITHUB_RUN_ID':'5'})
        self.workflow(self.ROW+'            shard: null\n');self.commit()
        row=cr.job_rows(cr.load_workflow(self.root)['jobs']['test'])[0]
        with contextlib.redirect_stdout(io.StringIO()):self.assertEqual(cr.decide(self.root,'test',json.dumps(row),{}),0)
        del row['shard']
        with self.assertRaisesRegex(cr.ReuseError,'requested job/row does not match'):
            cr.decide(self.root,'test',json.dumps(row),{})

    def test_real_null_collision_cannot_reuse_second_rows_result(self):
        self.workflow(self.ROW+'            shard: null\n'+self.ROW.replace('full: true','full: false'))
        self.declarations('test/0.17.0/data');self.commit()
        requested=cr.job_rows(cr.load_workflow(self.root)['jobs']['test'])[0]
        with patch.object(cr,'lookup',side_effect=AssertionError('foreign row lookup')) as lookup,\
             patch.object(cr,'_manifest',side_effect=AssertionError('foreign row manifest')) as manifest:
            with self.assertRaises(cr.ReuseError) as caught:
                cr.decide(self.root,'test',json.dumps(requested),
                          {'GITHUB_RUN_ID':'5','AIR2LEAN_EVENT':'push','GITHUB_REPOSITORY':'example/repo'})
        self.assertIn('repeated part ID',str(caught.exception))
        self.assertIn("'full': True",str(caught.exception));self.assertIn("'full': False",str(caught.exception))
        self.assertIn("'shard': None",str(caught.exception))
        lookup.assert_not_called();manifest.assert_not_called()

    def test_decide_uses_one_captured_workflow_for_validated_manifest(self):
        self.workflow(self.ROW);self.declarations('test/0.17.0/data');self.commit()
        row=cr.job_rows(cr.load_workflow(self.root)['jobs']['test'])[0]
        before=cr.manifest(self.root,'test/0.17.0/data',{})
        temp=self.root.parent/'decision-temp';temp.mkdir()
        environ={'GITHUB_RUN_ID':'5','AIR2LEAN_EVENT':'schedule','RUNNER_TEMP':str(temp)}
        actual_load=cr.load_workflow
        def load(root,revision=None):
            workflow=actual_load(root,revision)
            (self.root/cr.WORKFLOW).write_text('value: malformed:\n')
            return workflow
        with patch.object(cr,'load_workflow',side_effect=load) as loader,\
             patch.object(cr,'_manifest',wraps=cr._manifest) as manifest,\
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(cr.decide(self.root,'test',json.dumps(dict(reversed(list(row.items())))),environ),0)
        self.assertEqual(loader.call_count,1)
        self.assertEqual(manifest.call_count,1)
        self.assertEqual(manifest.call_args.args[4]['jobs']['test']['strategy']['matrix']['include'][0],row)
        self.assertIn('Full proof',[step['name'] for step in before['definitions']['job']['steps']])
        with self.assertRaises(cr.RR.ReleaseError):cr.manifest(self.root,'test/0.17.0/data',{})

    def test_all_current_numeric_rows_validate_without_transport_normalization(self):
        workflow=cr.load_workflow(self.root)
        environ={'GITHUB_RUN_ID':'5','AIR2LEAN_EVENT':'schedule'}
        count=0
        for part,(job,row) in cr.parts(workflow).items():
            if row is not None and any(type(value) in (int,float) for value in row.values()):
                with self.subTest(part=part),contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(cr.decide(self.root,job,json.dumps(row),environ),0)
                count+=1
        self.assertGreater(count,0)
        self.workflow(self.ROW+'            shard: 1\n');self.declarations('test/0.17.0/data/1');self.commit()
        row=cr.job_rows(cr.load_workflow(self.root)['jobs']['test'])[0]
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(cr.decide(self.root,'test',json.dumps(row),environ),0)
        with self.assertRaisesRegex(cr.ReuseError,'requested job/row does not match'):
            cr.decide(self.root,'test',json.dumps(dict(row,shard=1.0)),{})
        with self.assertRaisesRegex(cr.ReuseError,'requested job/row does not match'):
            cr.decide(self.root,'test',json.dumps(dict(row,shard=1.0000000000000002)),{})
        (self.root/cr.WORKFLOW).write_text('jobs:\n  solo:\n    steps:\n      - name: Gate\n        run: echo gate\n')
        with contextlib.redirect_stdout(io.StringIO()):self.assertEqual(cr.decide(self.root,'solo','null',{}),0)
        with self.assertRaisesRegex(cr.ReuseError,'requested job/row does not match'):
            cr.decide(self.root,'solo','{}',{})

    def test_real_typed_conditions_refuse_unsupported_data_and_preserve_runtime_strings(self):
        for condition,included in (('null',True),('FALSE',False),('TRUE',True),
                                   ("steps.cache.outputs.hit == 'true'",True),('success()',True)):
            with self.subTest(condition=condition):
                self.workflow(self.ROW,condition);self.declarations('test/0.17.0/data');self.commit()
                preimage=cr.manifest(self.root,'test/0.17.0/data',{})
                self.assertEqual(bool(preimage['definitions']['job']['steps']),included)
        for condition in ('0.0','0','[true]','\n          value: true'):
            with self.subTest(condition=condition):
                self.workflow(self.ROW,condition);self.declarations('test/0.17.0/data');self.commit()
                with self.assertRaisesRegex(cr.ReuseError,"ci.yml: step 'Full proof': unsupported condition DATA:"):
                    cr.manifest(self.root,'test/0.17.0/data',{})
        for value in (float('inf'),float('nan'),{}):
            with self.subTest(value=value),self.assertRaisesRegex(cr.ReuseError,"step 'Typed gate': unsupported condition DATA:"):
                cr.may_run({'name':'Typed gate','if':value},{'matrix':{},'runner.os':'Linux'})


class Lookup(unittest.TestCase):
    REPO = 'o/r'

    def fetch_for(self, artifacts, run, jobs, compare='ahead'):
        def fetch(path, _token):
            if '/artifacts?' in path:
                return {'artifacts': artifacts}
            if path.endswith('/runs/7'):
                return run
            if '/compare/' in path:
                return {'status': compare}
            return {'jobs': jobs}
        return fetch

    def artifact(self, **source):
        return {'name': 'ci-reuse-k', 'expired': False, 'created_at': '2026-10-11',
                'workflow_run': dict({'id': 7, 'repository_id': 1, 'head_repository_id': 1}, **source)}

    def run_data(self, **extra):
        return dict({'path': cr.WORKFLOW, 'name': 'CI', 'event': 'merge_group', 'html_url': 'u', 'head_sha': 'c',
                     'head_repository': {'full_name': self.REPO}}, **extra)

    JOBS = [{'name': 'test (x)', 'status': 'completed', 'conclusion': 'success', 'id': 3, 'html_url': 'j'}]

    def test_accepted_record(self):
        self.assertEqual(cr.lookup('k', 'test (x)', self.REPO, 't', self.fetch_for([self.artifact()], self.run_data(), self.JOBS)),
                         (7, 'u', 3, 'j'))

    def test_refused_records(self):
        cases = [
            ([self.artifact(head_repository_id=2)], self.run_data(), self.JOBS),                  # a fork
            ([self.artifact()], self.run_data(event='release'), self.JOBS),                         # another event
            ([self.artifact()], self.run_data(event='schedule'), self.JOBS),                        # unrestricted
            ([self.artifact()], self.run_data(path='.github/workflows/other.yml'), self.JOBS),      # another workflow
            ([self.artifact()], self.run_data(), [dict(self.JOBS[0], conclusion='failure')]),      # job failed
            ([self.artifact()], self.run_data(), [dict(self.JOBS[0], name='test (y)')]),           # another job
            ([dict(self.artifact(), expired=True)], self.run_data(), self.JOBS),                    # expired
        ]
        for artifacts, run, jobs in cases:
            self.assertIsNone(cr.lookup('k', 'test (x)', self.REPO, 't', self.fetch_for(artifacts, run, jobs)))

    def test_queue_reuses_only_full_runs_on_main(self):
        def found(event, compare):
            return cr.lookup('k', 'test (x)', self.REPO, 't',
                             self.fetch_for([self.artifact()], self.run_data(event=event), self.JOBS, compare),
                             events=cr.QUEUE_RECORD_EVENTS, require_main=True)
        self.assertIsNotNone(found('merge_group', 'ahead'))     # main is ahead of the run's commit
        self.assertIsNotNone(found('push', 'ahead'))            # the push run of an earlier main commit
        self.assertIsNotNone(found('workflow_dispatch', 'identical'))
        self.assertIsNone(found('pull_request', 'ahead'))      # a PR run's record
        self.assertIsNone(found('merge_group', 'diverged'))    # a queue run whose commit never became main

    def test_self_check_choice_is_one_part_per_run(self):
        parts = ['a', 'b', 'c', 'd']
        chosen = {cr.self_check_part({'GITHUB_RUN_ID': str(i), 'GITHUB_RUN_ATTEMPT': '1'}, parts) for i in range(40)}
        self.assertEqual(chosen, set(parts))
        env = {'GITHUB_RUN_ID': '5', 'GITHUB_RUN_ATTEMPT': '1'}
        self.assertEqual(cr.self_check_part(env, parts), cr.self_check_part(env, list(reversed(parts))))


if __name__ == '__main__':
    unittest.main()
