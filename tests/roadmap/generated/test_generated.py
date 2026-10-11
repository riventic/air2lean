#!/usr/bin/env python3
"""scripts/generated.py: the registry of whole-tree generated files, the determinism comparison,
produced-directory verification and the `generated` branch (entries, pending commits, fetch,
freshness) on a scratch repository. docs/ci.md#whole-tree-generated-files."""
import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('generated', ROOT / 'scripts/generated.py')
gen = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gen)


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
        run_ = {'id': run_id, 'event': 'merge_group', 'html_url': 'https://example/runs/%d' % run_id}
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
        self.assertEqual(gen.pending(self.data, self.root, {}), [self.m1])
        self.publish(self.m1, self.produced('p1', 'one'))
        m2 = self.commit('two')
        m3 = self.commit('three')
        self.assertEqual(gen.pending(self.data, self.root, gen.entries(self.root)), [m2, m3])

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


if __name__ == '__main__':
    unittest.main()
