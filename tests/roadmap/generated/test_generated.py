#!/usr/bin/env python3
"""scripts/generated.py: the registry of whole-tree generated files, the determinism comparison,
produced-directory verification and the `generated` branch (entries, pending commits, fetch,
freshness, publish from each main commit's CI run) on a scratch repository. docs/ci.md#whole-tree-generated-files."""
import contextlib
import importlib.util
import io
import json
import os
import shutil
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('generated', ROOT / 'scripts/generated.py')
gen = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gen)
spec = importlib.util.spec_from_file_location('generated_release_record', ROOT / 'scripts/release-record.py')
rr = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rr)


def git(root, *args, env=None):
    return subprocess.run(['git', *args], cwd=root, check=True, capture_output=True, text=True,
                          env=env).stdout.strip()


class Registry(unittest.TestCase):
    def setUp(self):
        self.data = gen.load(ROOT)

    def test_coverage_inventories_follow_the_supported_versions(self):
        versions = [v['version'] for v in json.loads((ROOT / 'compatibility.json').read_text())['zig']['versions']]
        self.assertEqual(sorted(gen.all_paths(self.data, ['coverage'])),
                         sorted('coverage/%s.json' % v for v in versions))

    def test_every_file_is_ignored_and_untracked(self):
        paths = gen.all_paths(self.data)
        self.assertEqual(len(paths), len(set(paths)))
        self.assertEqual(git(ROOT, 'ls-files', '--', *paths), '')
        ignored = git(ROOT, 'check-ignore', '--no-index', '--', *paths).splitlines()
        self.assertEqual(sorted(ignored), sorted(paths))

    def test_groups_name_a_generator_and_only_their_own_run_bound_files(self):
        for group in self.data['groups']:
            self.assertIn(group['generator'], gen.GENERATORS)
            self.assertLessEqual(set(group.get('run_bound', {})), set(group['paths']))

    def test_unknown_group_is_an_error(self):
        with self.assertRaises(gen.Error):
            gen.groups(self.data, ['nope'])


class Comparison(unittest.TestCase):
    def test_only_named_run_bound_fields_are_ignored(self):
        data = {'groups': [{'name': 'g', 'paths': ['r.json'], 'run_bound': {'r.json': ['artifacts', 'links.receipt']}}]}
        with tempfile.TemporaryDirectory() as temp:
            a, b = Path(temp, 'a.json'), Path(temp, 'b.json')
            a.write_text(json.dumps({'artifacts': [1], 'links': {'receipt': 1, 'source': 'x'}, 'v': 1}))
            b.write_text(json.dumps({'artifacts': [2], 'links': {'receipt': 2, 'source': 'x'}, 'v': 1}))
            self.assertEqual(gen.comparable(data, 'r.json', a), gen.comparable(data, 'r.json', b))
            b.write_text(json.dumps({'artifacts': [2], 'links': {'receipt': 2, 'source': 'y'}, 'v': 1}))
            self.assertNotEqual(gen.comparable(data, 'r.json', a), gen.comparable(data, 'r.json', b))
            self.assertNotEqual(gen.comparable(data, 'other.json', a), gen.comparable(data, 'other.json', Path(temp, 'b.json')))


class Workflow(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rr = rr
        cls.ci = cls.rr.parse_workflow_yaml((ROOT / '.github/workflows/ci.yml').read_text())
        cls.publisher = cls.rr.parse_workflow_yaml((ROOT / '.github/workflows/generated.yml').read_text())

    def test_ratchet_is_mandatory_only_for_transitions_and_other_producers_still_run(self):
        steps = self.ci['jobs']['generated']['steps']
        ratchet, = [step for step in steps if step.get('name') == 'Case families retain the authenticated event baseline']
        producer, = [step for step in steps if step.get('name') == 'Regenerate the whole-tree files twice']
        upload, = [step for step in steps if step.get('name') == 'Upload the generated files']
        for event in ('push', 'pull_request', 'merge_group', 'schedule', 'workflow_dispatch'):
            with self.subTest(event=event):
                context = {'github.event_name': event, 'env.AIR2LEAN_REUSED': ''}
                self.assertEqual(self.rr.TM.condition(ratchet['if'], context),
                                 event in ('push', 'pull_request', 'merge_group'))
                self.assertTrue(self.rr.TM.condition(producer.get('if'), context))
                self.assertTrue(self.rr.TM.condition(upload.get('if'), context))

    def test_only_completed_same_repository_main_pushes_wake_publication(self):
        steps = self.publisher['jobs']['publish']['steps']
        publish, = [step for step in steps if 'scripts/generated.py publish ' in step.get('run', '')]
        freshness, = [step for step in steps if 'scripts/generated.py freshness ' in step.get('run', '')]
        good = {'github.event_name': 'workflow_run', 'github.event.workflow_run.event': 'push',
                'github.event.workflow_run.status': 'completed',
                'github.event.workflow_run.head_branch': 'main',
                'github.event.workflow_run.conclusion': 'success',
                'github.event.workflow_run.head_repository.full_name': 'o/r', 'github.repository': 'o/r'}
        self.assertTrue(self.rr.TM.condition(publish['if'], good))
        publishing_group = self.rr.TM.interpolate(self.publisher['concurrency']['group'], good)
        self.assertEqual(publishing_group, 'generated-branch-publish')
        # A failed older push must wake catch-up after a newer successful push waited for it.
        for conclusion in ('failure', 'cancelled'):
            context = dict(good, **{'github.event.workflow_run.conclusion': conclusion})
            self.assertTrue(self.rr.TM.condition(publish['if'], context))
            self.assertEqual(self.rr.TM.interpolate(self.publisher['concurrency']['group'], context), publishing_group)
        changes = [('github.event_name', event) for event in ('schedule', 'workflow_dispatch', 'push')]
        changes += [('github.event.workflow_run.event', event)
                    for event in ('schedule', 'workflow_dispatch', 'merge_group', 'pull_request')]
        changes += [('github.event.workflow_run.head_branch', 'other'),
                    ('github.event.workflow_run.status', 'in_progress'),
                    ('github.event.workflow_run.head_repository.full_name', 'foreign/repo')]
        for key, value in changes:
            with self.subTest(key=key, value=value):
                context = dict(good, **{key: value})
                self.assertFalse(self.rr.TM.condition(publish['if'], context))
                self.assertTrue(self.rr.TM.condition(freshness.get('if'), context))
                # GitHub replaces pending runs even with cancel-in-progress:false. These runs
                # must never replace the only pending publisher of a successful main push.
                self.assertEqual(self.rr.TM.interpolate(self.publisher['concurrency']['group'], context),
                                 'generated-branch-freshness')


class Branch(unittest.TestCase):
    """A scratch repository with a registry of one group and a `generated` branch."""

    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name) / 'repo'
        self.root.mkdir()
        self.env = dict(os.environ, GIT_AUTHOR_NAME='t', GIT_AUTHOR_EMAIL='t@t', GIT_COMMITTER_NAME='t',
                        GIT_COMMITTER_EMAIL='t@t')
        os.environ.update({k: v for k, v in self.env.items() if k.startswith('GIT_')})
        git(self.root, 'init', '-q', '-b', 'main')
        git(self.root, 'commit', '-q', '--allow-empty', '-m', 'before the registry')
        self.data = {'schema': gen.SCHEMA, 'branch': 'generated', 'freshness_minutes': 30,
                     'groups': [{'name': 'g', 'generator': 'premise-index', 'paths': ['out/a.txt']}]}
        (self.root / 'assurance').mkdir()
        (self.root / 'assurance/generated.json').write_text(json.dumps(self.data))
        self.m1 = self.commit('registry')
        self.scratch = Path(temp.name)

    def commit(self, message):
        git(self.root, 'add', '-A')
        git(self.root, 'commit', '-q', '--allow-empty', '-m', message)
        head = git(self.root, 'rev-parse', 'HEAD')
        git(self.root, 'update-ref', 'refs/remotes/origin/main', head)
        return head

    def produced(self, name, text, commit=None):
        directory = self.scratch / name
        (directory / 'out').mkdir(parents=True)
        (directory / 'out/a.txt').write_text(text)
        commit = commit or git(self.root, 'rev-parse', 'HEAD')
        manifest = {'schema': gen.SCHEMA, 'commit': commit, 'tree': git(self.root, 'rev-parse', commit + '^{tree}'),
                    'groups': ['g'], 'files': {'out/a.txt': gen.sha256(directory / 'out/a.txt')}}
        (directory / gen.MANIFEST).write_text(json.dumps(manifest))
        return directory

    def publish(self, commit, directory, run_id=7):
        tree = git(self.root, 'rev-parse', commit + '^{tree}')
        parent = git(self.root, 'rev-parse', '--verify', '--quiet', gen.REMOTE_REF) if self.has_branch() else None
        run_ = {'id': run_id, 'event': 'push', 'head_branch': 'main', 'head_sha': commit,
                'status': 'completed', 'conclusion': 'success', 'html_url': 'https://example/runs/%d' % run_id}
        entry = gen.entry_commit(self.data, [directory], commit, tree, run_, parent, self.root)
        git(self.root, 'update-ref', gen.REMOTE_REF, entry)
        return entry

    def has_branch(self):
        return subprocess.run(['git', 'rev-parse', '--verify', '--quiet', gen.REMOTE_REF], cwd=self.root,
                              capture_output=True).returncode == 0

    def test_entry_tree_is_exactly_the_files_and_names_commit_tree_and_run(self):
        entry = self.publish(self.m1, self.produced('p1', 'one'))
        self.assertEqual(git(self.root, 'ls-tree', '-r', '--name-only', entry), 'out/a.txt')
        message = git(self.root, 'log', '-1', '--format=%B', entry)
        self.assertIn('Main-Commit: ' + self.m1, message)
        self.assertIn('Main-Tree: ' + git(self.root, 'rev-parse', self.m1 + '^{tree}'), message)
        self.assertIn('CI-Run: https://example/runs/7', message)
        self.assertEqual(gen.entries(self.root), {self.m1: entry})

    def test_pending_lists_unpublished_main_commits_since_the_registry_oldest_first(self):
        self.assertEqual(gen.pending(self.root, {}), [self.m1])
        self.publish(self.m1, self.produced('p1', 'one'))
        m2 = self.commit('two')
        m3 = self.commit('three')
        self.assertEqual(gen.pending(self.root, gen.entries(self.root)), [m2, m3])

    def test_publication_requested_from_nonpush_or_failed_runs_is_refused_before_writes(self):
        directory = self.produced('publication', 'one')
        tree = git(self.root, 'rev-parse', self.m1 + '^{tree}')
        good = {'id': 7, 'event': 'push', 'head_branch': 'main', 'head_sha': self.m1,
                'status': 'completed', 'conclusion': 'success', 'html_url': 'https://example/runs/7'}
        changes = [('event', event) for event in ('schedule', 'workflow_dispatch', 'merge_group', 'pull_request')]
        changes += [('head_branch', 'other'), ('head_sha', '0' * 40),
                    ('status', 'in_progress'), ('conclusion', 'failure')]
        for key, value in changes:
            with self.subTest(key=key, value=value):
                with mock.patch.object(gen, 'verified', wraps=gen.verified) as verified:
                    with self.assertRaisesRegex(gen.Error, 'successful CI push on main'):
                        gen.entry_commit(self.data, [directory], self.m1, tree,
                                         dict(good, **{key: value}), None, self.root)
                    verified.assert_not_called()
                self.assertFalse(self.has_branch())

    def test_produced_directory_must_match_commit_tree_and_digests(self):
        m2 = self.commit('two')
        with self.assertRaises(gen.Error):  # produced for m1, not m2
            self.publish(m2, self.produced('p1', 'one', commit=self.m1))
        directory = self.produced('p2', 'two')
        (directory / 'out/a.txt').write_text('tampered')
        with self.assertRaises(gen.Error):
            self.publish(m2, directory)

    def test_fetch_writes_the_published_files_of_a_main_commit(self):
        self.publish(self.m1, self.produced('p1', 'one'))
        m2 = self.commit('two')
        self.publish(m2, self.produced('p2', 'two'))
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(gen.fetch(self.data, None, self.m1, self.root), self.m1)
            self.assertEqual((self.root / 'out/a.txt').read_text(), 'one')
            self.assertEqual(gen.fetch(self.data, None, None, self.root), m2)
        self.assertEqual((self.root / 'out/a.txt').read_text(), 'two')

    def test_install_refuses_files_produced_for_another_tree(self):
        directory = self.produced('p1', 'one')
        self.commit('two')
        with self.assertRaises(gen.Error):
            gen.install(self.data, [directory], self.root)

    def test_freshness_fails_on_an_old_unpublished_commit(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            self.assertEqual(gen.freshness(self.data, 30, None, self.root), 0)  # m1 is minutes old
            self.assertEqual(gen.freshness(self.data, -1, None, self.root), 1)
            self.publish(self.m1, self.produced('p1', 'one'))
            self.assertEqual(gen.freshness(self.data, -1, None, self.root), 0)
        self.assertIn(self.m1, out.getvalue())

    def test_publish_takes_each_commits_ci_run_skips_settled_gaps_and_waits_for_running_ones(self):
        """m1 has a green push run; m2 only ineligible runs; m3 a red run whose producing jobs
        passed; m4 a running one whose provenance job has not finished; m5 a green one. The first
        publish appends m1 and stops at m4; once m4's run ends with provenance red, m4 is
        skipped and m5 is published. A run of another workflow, event or repository never counts."""
        origin = self.scratch / 'origin.git'
        git(self.scratch, 'init', '-q', '--bare', str(origin))
        git(self.root, 'remote', 'add', 'origin', str(origin))
        m2, m3, m4, m5 = (self.commit(m) for m in ('two', 'three', 'four', 'five'))
        data = dict(self.data, groups=self.data['groups'] + [{'name': 'h', 'generator': 'premise-index',
                                                              'paths': ['out/b.txt']}])

        def ci_run(id_, commit, status='completed', event='push', **extra):
            return dict({'id': id_, 'path': gen.WORKFLOW, 'event': event, 'head_sha': commit, 'status': status,
                         'head_branch': 'main', 'conclusion': 'success' if status == 'completed' else None,
                         'head_repository': {'full_name': 'o/r'}, 'created_at': '2026-10-15T00:00:%02dZ' % id_,
                         'html_url': 'u/%d' % id_}, **extra)

        def job(name, conclusion='success', status='completed'):
            return {'name': name, 'status': status, 'conclusion': conclusion}
        green = [job('generated'), job('provenance'), job('test')]
        runs = {self.m1: [ci_run(1, self.m1), ci_run(9, self.m1, event='pull_request'),
                          ci_run(10, self.m1, path='.github/workflows/other.yml')],
                m2: [ci_run(11, m2, event='schedule'), ci_run(12, m2, event='workflow_dispatch'),
                     ci_run(13, m2, event='merge_group'), ci_run(14, m2, head_branch='other'),
                     ci_run(15, m2, head_repository={'full_name': 'foreign/repo'}),
                     ci_run(16, '0' * 40)],
                m3: [ci_run(3, m3, conclusion='failure')],
                m4: [ci_run(4, m4, status='in_progress')], m5: [ci_run(5, m5)]}
        produced = {1: self.produced('p1', 'one', commit=self.m1),
                    5: self.produced('p5', 'five', commit=m5)}

        def fake_run(*args, cwd=gen.ROOT, **kwargs):
            args = [str(a) for a in args]
            if args[:3] == ['gh', 'run', 'download']:
                source, target = produced[int(args[3])], Path(args[args.index('--dir') + 1])
                if args[args.index('--name') + 1] == 'generated-files':
                    shutil.copytree(source, target)
                else:  # the provenance artifact: group h of the same commit
                    (target / 'out').mkdir(parents=True)
                    (target / 'out/b.txt').write_text('b')
                    manifest = json.loads((source / gen.MANIFEST).read_text())
                    (target / gen.MANIFEST).write_text(json.dumps(dict(
                        manifest, groups=['h'], files={'out/b.txt': gen.sha256(target / 'out/b.txt')})))
            else:
                return subprocess.run(args, cwd=cwd, check=True, capture_output=True, **kwargs)

        def fake_api(path):
            if '/jobs?' in path:
                run_id = int(path.split('/runs/')[1].split('/')[0])
                self.assertIn(run_id, (1, 5))
                return {'jobs': green}
            return {'workflow_runs': runs[path.split('head_sha=')[1].split('&')[0]]}

        def published():
            gen.fetch_branch(data, self.root)
            return set(gen.entries(self.root))

        with mock.patch.object(gen, 'run', fake_run), mock.patch.object(gen, 'api', fake_api), \
                contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            gen.publish(data, 'o/r', True, self.root)
            self.assertEqual(published(), {self.m1})
            gen.publish(data, 'o/r', True, self.root)  # m4's run is still going: nothing new
            self.assertEqual(published(), {self.m1})
            runs[m4][0]['status'] = 'completed'
            runs[m4][0]['conclusion'] = 'failure'
            steps = rr.parse_workflow_yaml((ROOT / '.github/workflows/generated.yml').read_text())['jobs']['publish']['steps']
            wakeup, = [step for step in steps if 'scripts/generated.py publish ' in step.get('run', '')]
            older = runs[m4][0]
            self.assertTrue(rr.TM.condition(wakeup['if'], {
                'github.event_name': 'workflow_run', 'github.event.workflow_run.status': older['status'],
                'github.event.workflow_run.event': older['event'],
                'github.event.workflow_run.head_branch': older['head_branch'],
                'github.event.workflow_run.conclusion': older['conclusion'],
                'github.event.workflow_run.head_repository.full_name': older['head_repository']['full_name'],
                'github.repository': 'o/r'}))
            gen.publish(data, 'o/r', True, self.root)
            self.assertEqual(published(), {self.m1, m5})
        log = git(origin, 'log', '--format=%(trailers:key=Main-Commit,valueonly,separator=)', 'generated').split()
        self.assertEqual(log, [m5, self.m1])  # main's order, one fast-forward chain


if __name__ == '__main__':
    unittest.main()
