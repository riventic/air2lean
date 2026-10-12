#!/usr/bin/env python3
"""scripts/ci-reuse.py: keys, trace reduction, coverage, workflow guards and record lookup.

The coverage tests are the unit tests of the CI check "Declared inputs cover every observation"
(docs/ci.md#enforcement): a step that reads a path outside its declared inputs must fail it.
Offline; the end-to-end trace test runs only where strace is installed (Linux).
"""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
_spec = importlib.util.spec_from_file_location('ci_reuse', ROOT / 'scripts/ci-reuse.py')
cr = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cr)

WS = '/w'
TREE = {'scripts/a.py': ('100644', '1' * 40), 'scripts/b.py': ('100644', '2' * 40),
        'docs/x.md': ('100644', '3' * 40), 'tests/t/run.py': ('100644', '4' * 40),
        'README.md': ('100644', '5' * 40)}


def reduce(lines, workspace=WS):
    reducer = cr.Reducer(workspace)
    for line in lines:
        reducer.feed(line + '\n')
    return reducer.finish()


def violations(step, patterns=(), listings=(), tree_names=False, commit_bound=False):
    return cr.coverage([step], cr.Inputs(patterns, listings, tree_names), TREE, commit_bound)


class Patterns(unittest.TestCase):
    def test_globs(self):
        inputs = cr.Inputs(['scripts/**', '*.md', 'tests/**/run.py'])
        for path in ('scripts/a.py', 'scripts/x/y', 'README.md', 'tests/t/run.py', 'tests/run.py'):
            self.assertTrue(inputs.content(path), path)
        for path in ('docs/x.md', 'scriptsx/a', 'tests/t/other.py'):
            self.assertFalse(inputs.content(path), path)
        self.assertTrue(inputs.subtree('scripts') and inputs.subtree('scripts/x'))
        self.assertFalse(inputs.subtree('tests') or inputs.subtree(''))
        self.assertTrue(cr.Inputs(['**']).subtree(''))

    def test_hashfiles_patterns(self):
        text = ("key: x-${{ hashFiles('a/*.zig', format('zig-patch/{0}/hook.patch', matrix.zig), '!b') }}-"
                "${{ hashFiles('lean-toolchain') }}")
        self.assertEqual(cr.hashfiles_patterns(text), {'a/*.zig', 'zig-patch/*/hook.patch', 'lean-toolchain'})


class Reduction(unittest.TestCase):
    def test_paths_resolve_against_the_annotated_cwd(self):
        out = reduce([
            '10 openat(AT_FDCWD</w>, "scripts/a.py", O_RDONLY|O_CLOEXEC) = 3</w/scripts/a.py>',
            '10 newfstatat(AT_FDCWD</w/tests>, "t/run.py", {st_mode=S_IFREG|0644, ...}, 0) = 0',
            '10 openat(AT_FDCWD</w>, "/usr/lib/x.so", O_RDONLY) = 3</usr/lib/x.so>',
            '10 getdents64(3</w/scripts>, 0x55 /* 4 entries */, 32768) = 112',
            '10 openat(AT_FDCWD</w>, "out/r.json", O_WRONLY|O_CREAT|O_TRUNC, 0644) = 4</w/out/r.json>',
            '10 getcwd("/w", 4096) = 3',
        ])
        self.assertEqual(out['observed'], {'out/r.json': ['write'], 'scripts': ['list'],
                                           'scripts/a.py': ['read'], 'tests/t/run.py': ['probe']})

    def test_unfinished_calls_and_deferred_relative_exec(self):
        out = reduce([
            '10 clone(child_stack=NULL, flags=SIGCHLD <unfinished ...>',
            '11 execve("scripts/a.py", ["scripts/a.py", "x"], 0x7ffd /* 9 vars */) = 0',
            '10 <... clone resumed>) = 11',
            '11 openat(AT_FDCWD</w/docs>, "x.md", O_RDONLY) = 3</w/docs/x.md>',
        ])
        self.assertEqual(out['observed'], {'docs/scripts/a.py': ['read'], 'docs/x.md': ['read']})
        self.assertEqual(out['unresolved'], [])

    def test_unresolvable_relative_path_is_reported(self):
        out = reduce(['12 execve("scripts/a.py", ["a"], 0x0 /* 0 vars */) = 0'])
        self.assertTrue(out['unresolved'])

    def test_git_commands_are_classified_not_traced(self):
        out = reduce([
            '20 execve("/usr/bin/git", ["git", "ls-files", "-z"], 0x0 /* 1 var */) = 0',
            '20 openat(AT_FDCWD</w>, "/w/.git/index", O_RDONLY) = 3</w/.git/index>',
            '21 execve("/usr/bin/git", ["git", "-C", "/w", "rev-parse", "HEAD"], 0x0 /* 1 var */) = 0',
            '21 openat(AT_FDCWD</w>, "/w/.git/HEAD", O_RDONLY) = 3</w/.git/HEAD>',
            '22 execve("/usr/bin/git", ["git", "status", "--porcelain=v1"], 0x0 /* 1 var */) = 0',
            '22 newfstatat(AT_FDCWD</w>, "README.md", {...}, AT_SYMLINK_NOFOLLOW) = 0',
            '22 openat(AT_FDCWD</w>, ".git/index", O_RDONLY) = 3</w/.git/index>',
            '23 openat(AT_FDCWD</w>, ".git/HEAD", O_RDONLY) = 3</w/.git/HEAD>',
        ])
        self.assertEqual(out['git'], {'["git","-C","/w","rev-parse","HEAD"]': 'commit',
                                      '["git","ls-files","-z"]': 'names',
                                      '["git","status","--porcelain=v1"]': 'status'})
        self.assertEqual(out['gitdir_by_others'], ['.git/HEAD'])
        self.assertEqual(out['observed'], {})

    def test_threads_and_children_run_their_parents_image_until_execve(self):
        out = reduce([
            '30 execve("/usr/bin/git", ["git", "status", "--porcelain"], 0x0 /* 1 var */) = 0',
            '30 clone3({flags=CLONE_VM|CLONE_THREAD, ...} <unfinished ...>',
            # git's index-preload thread, printed before the clone returns in its parent
            '31 newfstatat(AT_FDCWD</w>, "/w/docs/x.md", {...}, AT_SYMLINK_NOFOLLOW) = 0',
            '30 <... clone3 resumed>, 88) = 31',
            '31 newfstatat(AT_FDCWD</w>, "/w/README.md", {...}, AT_SYMLINK_NOFOLLOW) = 0',
            '40 execve("/usr/bin/bash", ["bash", "s.sh"], 0x0 /* 1 var */) = 0',
            '40 clone(child_stack=NULL, flags=SIGCHLD <unfinished ...>',
            # a forked shell redirects before it becomes git: that open is the shell's
            '41 openat(AT_FDCWD</w>, "/w/scripts/a.py", O_RDONLY) = 3</w/scripts/a.py>',
            '41 execve("/usr/bin/git", ["git", "status"], 0x0 /* 1 var */) = 0',
            '41 newfstatat(AT_FDCWD</w>, "/w/scripts/b.py", {...}, 0) = 0',
            '40 <... clone resumed>) = 41',
            # a clone that never returns in the trace: its image stays unknown, so it counts
            '50 openat(AT_FDCWD</w>, "/w/tests/t/run.py", O_RDONLY) = 3</w/tests/t/run.py>',
        ])
        self.assertEqual(out['observed'], {'scripts/a.py': ['read'], 'tests/t/run.py': ['read']})

    def test_a_reused_pid_does_not_keep_the_old_image(self):
        out = reduce([
            '60 execve("/usr/bin/git", ["git", "status"], 0x0 /* 1 var */) = 0',
            '60 +++ exited with 0 +++',
            '70 execve("/usr/bin/bash", ["bash", "s.sh"], 0x0 /* 1 var */) = 0',
            '70 clone(child_stack=NULL, flags=SIGCHLD <unfinished ...>',
            '60 openat(AT_FDCWD</w>, "/w/scripts/a.py", O_RDONLY) = 3</w/scripts/a.py>',  # a new shell child
            '60 +++ exited with 0 +++',
            '70 <... clone resumed>) = 60',
            '60 newfstatat(AT_FDCWD</w>, "/w/docs/x.md", {...}, 0) = 0',  # a third process, clone not yet seen
        ])
        self.assertEqual(out['observed'], {'docs/x.md': ['probe'], 'scripts/a.py': ['read']})

    def test_git_classes(self):
        self.assertEqual(cr.git_class(['git', 'ls-files', '-z', '--cached', '--others', '--exclude-standard']), 'names')
        self.assertEqual(cr.git_class(['git', 'ls-files', '-s']), 'commit')
        self.assertEqual(cr.git_class(['git', 'rev-parse', '--show-toplevel']), 'none')
        self.assertEqual(cr.git_class(['git', 'show', 'HEAD:x']), 'commit')
        self.assertEqual(cr.git_class(['git', 'fetch', '--depth=1', 'origin', 'a' * 40]), 'none')
        self.assertEqual(cr.git_class(['git', 'cat-file', '-e', 'b' * 40 + '^{commit}']), 'none')
        self.assertEqual(cr.git_class(['git', 'checkout', '--', 'Proofs']), 'commit')

    def test_c_string_escapes(self):
        self.assertEqual(cr.c_string(r'"a\"b\x41\n"'), 'a"bA\n')
        self.assertIsNone(cr.c_string('"abc"...'))
        self.assertIsNone(cr.c_string('NULL'))


class Coverage(unittest.TestCase):
    def step(self, observed, **extra):
        return dict({'complete': True, 'observed': observed, 'git': {}, 'gitdir_by_others': [], 'unresolved': []},
                    **extra)

    def test_read_outside_the_declared_inputs_fails(self):
        step = self.step({'scripts/a.py': ['read'], 'docs/x.md': ['read']})
        self.assertEqual([v[0] for v in violations(step, ['scripts/**'])], ['docs/x.md'])
        self.assertEqual(violations(step, ['scripts/**', 'docs/x.md']), [])

    def test_probe_of_a_tracked_file_needs_its_content(self):
        self.assertTrue(violations(self.step({'README.md': ['probe']}), [], listings=['.']))
        self.assertEqual(violations(self.step({'README.md': ['probe']}), ['README.md']), [])

    def test_directory_listing_needs_a_listing_or_subtree(self):
        step = self.step({'scripts': ['list']})
        self.assertTrue(violations(step, ['scripts/a.py']))
        self.assertEqual(violations(step, [], listings=['scripts']), [])
        self.assertEqual(violations(step, ['scripts/**']), [])
        self.assertEqual(violations(step, [], tree_names=True), [])

    def test_untracked_or_absent_path_needs_its_deepest_tracked_listing(self):
        step = self.step({'tests/t/out/r.json': ['write'], '.lake/build/x.olean': ['read'], 'nope/x': ['probe']})
        problems = {v[0]: v[2] for v in violations(step)}
        self.assertIn("'tests/t'", problems['tests/t/out/r.json'])
        self.assertIn("'.'", problems['.lake/build/x.olean'])
        self.assertEqual(violations(step, [], listings=['tests/t', '.']), [])

    def test_whole_tree_generated_file_needs_the_whole_tree(self):
        step = self.step({'docs/premise-index.md': ['read']})
        generated = {'docs/premise-index.md'}
        problems = cr.coverage([step], cr.Inputs([], ['docs']), TREE, False, generated)
        self.assertIn('whole-tree generated file', problems[0][2])
        self.assertEqual(cr.coverage([step], cr.Inputs(['**']), TREE, False, generated), [])
        installed = self.step({'docs/premise-index.md': ['write']})
        self.assertEqual(cr.coverage([installed], cr.Inputs([]), TREE, False, generated), [])
        probed = self.step({'docs/premise-index.md': ['probe', 'write']})
        self.assertTrue(cr.coverage([probed], cr.Inputs([]), TREE, False, generated))

    def test_read_write_open_also_reads(self):
        out = reduce(['10 openat(AT_FDCWD</w>, "out/r.json", O_RDWR) = 4</w/out/r.json>',
                      '10 openat(AT_FDCWD</w>, "out/s.json", O_RDWR|O_TRUNC) = 5</w/out/s.json>'])
        self.assertEqual(out['observed'], {'out/r.json': ['read', 'write'], 'out/s.json': ['write']})

    def test_commit_identity_needs_commit_bound(self):
        step = self.step({}, git={'["git","rev-parse","HEAD"]': 'commit'})
        self.assertIn('commit_bound', violations(step)[0][2])
        self.assertEqual(violations(step, commit_bound=True), [])
        step = self.step({}, git={'["git","ls-files","-z"]': 'names'})
        self.assertIn('tree_names', violations(step)[0][2])
        self.assertEqual(violations(step, tree_names=True), [])

    def test_incomplete_or_unresolved_traces_fail(self):
        self.assertTrue(cr.coverage([{'complete': False, 'step': '0003'}], cr.Inputs(['**']), TREE))
        self.assertTrue(violations(self.step({}, unresolved=['relative x in pid 4']), ['**'], tree_names=True))

    def test_suggestion_covers_the_trace(self):
        step = self.step({'scripts/a.py': ['read'], 'tests/t/run.py': ['read'], 'scripts': ['list'],
                          'tests/t/out/r.json': ['write'], 'tests': ['probe', 'write']},
                         git={'["git","ls-files","-z"]': 'names'})
        found = cr.suggest([step], TREE)
        self.assertTrue(found['tree_names'])
        self.assertIn('tests/**', found['inputs'])
        self.assertEqual(violations(step, found['inputs'], [l if l != '.' else '' for l in found['listings']],
                                    tree_names=True), [])


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

    def test_opting_out_of_the_tracer_fails(self):
        self.edit('.github/workflows/ci.yml', '      - name: Op effects table source checks\n',
                  '      - name: Op effects table source checks\n        env:\n          AIR2LEAN_UNTRACED: "1"\n')
        self.assertTrue(any('opts out of the tracer' in e for e in cr.check_workflow(self.root)))


class Keys(unittest.TestCase):
    """A key changes with a declared input and stays with an undeclared one."""

    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='air2lean ci-reuse key ')
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        for rel in ('.github/workflows/ci.yml', '.github/ci-inputs.json', *cr.MACHINERY):
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / rel, self.root / rel)
        data = json.loads((self.root / '.github/ci-inputs.json').read_text())
        data['parts']['bitops-native-arm'] = {'inputs': ['tests/roadmap/bitops-native/**'], 'listings': ['tests']}
        (self.root / '.github/ci-inputs.json').write_text(json.dumps(data))
        for rel in ('tests/roadmap/bitops-native/gen.py', 'docs/notes.md'):
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.root / rel).write_text('one\n')
        self.git('init', '-q')
        self.commit()

    def git(self, *args):
        subprocess.run(['git', '-C', str(self.root), '-c', 'user.name=t', '-c', 'user.email=t@t', *args], check=True,
                       capture_output=True)

    def commit(self):
        self.git('add', '-A')
        self.git('commit', '-qm', 'x', '--allow-empty')

    def key(self, part='bitops-native-arm', environ=None):
        return cr.key_of(cr.manifest(self.root, part, environ or {}))

    def test_declared_and_undeclared_changes(self):
        first = self.key()
        (self.root / 'docs/notes.md').write_text('two\n')
        self.commit()
        self.assertEqual(self.key(), first)
        (self.root / 'tests/roadmap/bitops-native/gen.py').write_text('two\n')
        self.commit()
        changed = self.key()
        self.assertNotEqual(changed, first)
        (self.root / 'tests/new.txt').write_text('listed\n')
        self.commit()
        self.assertNotEqual(self.key(), changed)
        self.assertNotEqual(self.key(environ={'ImageVersion': '2'}), self.key(environ={'ImageVersion': '3'}))

    def test_commit_bound_key_names_the_commit(self):
        first = self.key('macos/0.16.0')
        self.commit()
        self.assertNotEqual(self.key('macos/0.16.0'), first)

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

    def test_reuse_false_has_no_key(self):
        data = json.loads((self.root / '.github/ci-inputs.json').read_text())
        data['parts']['bitops-native-arm'] = {'reuse': False}
        (self.root / '.github/ci-inputs.json').write_text(json.dumps(data))
        self.assertIsNone(cr.manifest(self.root, 'bitops-native-arm', {}))


class Lookup(unittest.TestCase):
    REPO = 'o/r'

    def fetch_for(self, artifacts, run, jobs):
        def fetch(path, _token):
            if '/artifacts?' in path:
                return {'artifacts': artifacts}
            if path.endswith('/runs/7'):
                return run
            return {'jobs': jobs}
        return fetch

    def artifact(self, **source):
        return {'name': 'ci-reuse-k', 'expired': False, 'created_at': '2026-10-11',
                'workflow_run': dict({'id': 7, 'repository_id': 1, 'head_repository_id': 1}, **source)}

    def run_data(self, **extra):
        return dict({'path': cr.WORKFLOW, 'name': 'CI', 'event': 'merge_group', 'html_url': 'u',
                     'head_repository': {'full_name': self.REPO}}, **extra)

    JOBS = [{'name': 'test (x)', 'status': 'completed', 'conclusion': 'success', 'id': 3, 'html_url': 'j'}]

    def test_accepted_record(self):
        self.assertEqual(cr.lookup('k', 'test (x)', self.REPO, 't', self.fetch_for([self.artifact()], self.run_data(), self.JOBS)),
                         (7, 'u', 3, 'j'))

    def test_refused_records(self):
        cases = [
            ([self.artifact(head_repository_id=2)], self.run_data(), self.JOBS),                  # a fork
            ([self.artifact()], self.run_data(event='push'), self.JOBS),                            # another event
            ([self.artifact()], self.run_data(path='.github/workflows/other.yml'), self.JOBS),      # another workflow
            ([self.artifact()], self.run_data(), [dict(self.JOBS[0], conclusion='failure')]),      # job failed
            ([self.artifact()], self.run_data(), [dict(self.JOBS[0], name='test (y)')]),           # another job
            ([dict(self.artifact(), expired=True)], self.run_data(), self.JOBS),                    # expired
        ]
        for artifacts, run, jobs in cases:
            self.assertIsNone(cr.lookup('k', 'test (x)', self.REPO, 't', self.fetch_for(artifacts, run, jobs)))

    def test_self_check_choice_is_one_part_per_run(self):
        parts = ['a', 'b', 'c', 'd']
        chosen = {cr.self_check_part({'GITHUB_RUN_ID': str(i), 'GITHUB_RUN_ATTEMPT': '1'}, parts) for i in range(40)}
        self.assertEqual(chosen, set(parts))
        env = {'GITHUB_RUN_ID': '5', 'GITHUB_RUN_ATTEMPT': '1'}
        self.assertEqual(cr.self_check_part(env, parts), cr.self_check_part(env, list(reversed(parts))))


def ptraced():
    """True inside a traced CI step: strace cannot attach to a process that is already traced."""
    try:
        status = Path('/proc/self/status').read_text()
    except OSError:
        return False
    return any(line.split()[1:] != ['0'] for line in status.splitlines() if line.startswith('TracerPid:'))


@unittest.skipUnless(shutil.which('strace') and sys.platform == 'linux' and not ptraced(),
                     'needs strace (Linux) outside a traced step (the CI step itself is traced)')
class EndToEnd(unittest.TestCase):
    def test_traced_step_reading_an_undeclared_file_fails(self):
        with tempfile.TemporaryDirectory() as temp:
            work, traces = Path(temp, 'w'), Path(temp, 't')
            (work / 'scripts').mkdir(parents=True)
            traces.mkdir()
            (work / 'scripts/a.txt').write_text('a')
            (work / 'docs').mkdir()
            (work / 'docs/b.txt').write_text('b')
            script = Path(temp, 'step.sh')
            script.write_text('cat scripts/a.txt docs/b.txt >/dev/null\n')
            env = dict(os.environ, AIR2LEAN_TRACE_DIR=str(traces), AIR2LEAN_REUSE_TOOL=str(ROOT / 'scripts/ci-reuse.py'),
                       GITHUB_WORKSPACE=str(work))
            subprocess.run(['bash', str(ROOT / 'scripts/ci-trace.sh'), str(script)], cwd=work, env=env, check=True)
            steps = cr.read_traces(traces)
            tree = {'scripts/a.txt': ('100644', '1' * 40), 'docs/b.txt': ('100644', '2' * 40)}
            problems = cr.coverage(steps, cr.Inputs(['scripts/**'], ['.']), tree)
            self.assertEqual([p[0] for p in problems], ['docs/b.txt'])
            self.assertEqual(cr.coverage(steps, cr.Inputs(['scripts/**', 'docs/**'], ['.']), tree), [])


if __name__ == '__main__':
    unittest.main()
