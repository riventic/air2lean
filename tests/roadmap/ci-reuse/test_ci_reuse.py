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


class Workflow(unittest.TestCase):
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


class Keys(Repository):
    """A key changes with a declared input or any tracked name, and stays with undeclared content."""

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
            ([self.artifact()], self.run_data(event='push'), self.JOBS),                            # another event
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
