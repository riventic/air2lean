#!/usr/bin/env python3
"""D02 theorem inventory regressions: the committed inventory and fail-closed fixtures."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import stat
import sys
import tempfile
import textwrap
import unittest

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location('theorem_inventory', ROOT / 'scripts/theorem-inventory.py')
ti = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ti)

FILES = {
    'compatibility.json': json.dumps({'zig': {'versions': [{'version': '0.16.0'}, {'version': '0.15.2'}]}}),
    'examples/demo/demo.zig': '',
    'examples/conc/zig-versions': '0.16.0\n',
    'Proofs/Demo/Gen.lean': 'namespace Demo\ndef f (x : Nat) : Nat := x\nend Demo\n',
    'tests/golden/0.15.2/demo/Gen.lean': 'namespace Demo\ndef f (x : Nat) : Nat := x + 0\nend Demo\n',
    'Proofs/Demo/Proofs.lean': '''\
        import Proofs.Demo.Gen
        namespace Demo
        theorem f_spec (x : Nat) : f x = x := rfl
        end Demo
        ''',
    'Proofs/Conc/Gen.lean': 'namespace Conc\ndef main : Nat := 0\nend Conc\n',
    'Proofs/Conc/Proofs.lean': '''\
        import Proofs.Conc.Gen
        namespace Conc
        /-- **`main` gives 0 under every schedule**. -/
        theorem main_spec {fuel : Nat} {o : Nat → Nat} {v : Nat}
            (h : (Sched.run dispatch fuel o main mem0).run = some v) : v = 0 := sorry
        /-- One schedule. -/
        theorem main_sc : okVal (Sched.run dispatch 100 (sched []) main mem0) = some 0 := by
          decide +kernel
        end Conc
        ''',
    'docs/proofs.md': '''\
        # Proofs

        ## Proved examples

        | File | Theorems |
        |---|---|
        | `Proofs/Demo/Proofs.lean` | `f_spec` (the identity) |
        | `Proofs/Conc/Proofs.lean` | `main_spec` (0 under every schedule), `main_sc` (one schedule) |
        ''',
    'docs/vector-proofs.md': '# Checked vector addition proofs\n',
    'docs/theorem-inventory.md': f'# Inventory\n\n{ti.BEGIN}\n{ti.END}\n',
}

THEOREMS = [
    {'name': 'Demo.f_spec', 'module': 'Proofs.Demo.Proofs', 'example': 'demo',
     'scope': 'sequential', 'domain': 'every x'},
    {'name': 'Conc.main_spec', 'module': 'Proofs.Conc.Proofs', 'example': 'conc',
     'scope': 'all-schedules', 'domain': 'every fuel and oracle'},
    {'name': 'Conc.main_sc', 'module': 'Proofs.Conc.Proofs', 'example': 'conc',
     'scope': 'single-schedule', 'domain': 'one oracle'},
]


class Fixture:
    def __init__(self, root: Path):
        self.root = root
        for rel, text in FILES.items():
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(textwrap.dedent(text))
        self.save({'schema': 1, 'theorems': [dict(t) for t in THEOREMS], 'runs': {}})

    def load(self):
        return json.loads((self.root / ti.INVENTORY).read_text())

    def save(self, inv):
        (self.root / ti.INVENTORY).parent.mkdir(parents=True, exist_ok=True)
        (self.root / ti.INVENTORY).write_text(json.dumps(inv))

    def guard(self, name, command, log_text, outcome='success', exit_code=0):
        log = self.root.parent / f'{name}.log'
        log.write_text(log_text)
        report = self.root.parent / f'{name}.json'
        report.write_text(json.dumps({
            'cwd': str(self.root), 'command': command, 'outcome': outcome, 'exit_code': exit_code,
            'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest(), 'log_truncated': False,
            'revision': {'head': 'f' * 40, 'tracked_dirty': False}, 'started_utc': '2026-10-07T00:00:00'}))
        return report, log

    def record(self, run, zig, report, log, target='linux'):
        self.assert_main(['record', '--run', run, '--zig', zig, '--target', target,
                          '--guard-report', str(report), '--guard-log', str(log)])

    def assert_main(self, argv, code=0):
        status = ti.main(['--root', str(self.root), *argv])
        if status != code:
            raise AssertionError(f'{argv}: exit {status}, wanted {code}')

    def record_all(self):
        """The committed translations (both versions of conc/demo) and the 0.15.2 demo golden."""
        self.record('all', '0.16.0', *self.guard('all', ['lake', 'build', 'Proofs'], 'Build completed\n'))
        swap = 'tests/golden/0.15.2/demo/Gen.lean'
        digest = hashlib.sha256((self.root / swap).read_bytes()).hexdigest()
        self.record('demo-0152', '0.15.2', *self.guard(
            'demo', ['python3', str(self.root / 'scripts/theorem-inventory.py'), 'swap-build',
                     '--swap', f'demo={swap}', '--', 'Proofs.Demo.Proofs'],
            f'{ti.SWAP_PREFIX}demo {swap} {digest}\nBuild completed\n'))
        ti.check(self.root, write=True)

    def errors(self):
        return ti.check(self.root)


class FixtureTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.fx = Fixture(Path(self.temp.name) / 'repo')

    def tearDown(self):
        self.temp.cleanup()

    def assertError(self, fragment):
        errors = self.fx.errors()
        self.assertTrue(any(fragment in e for e in errors), errors)

    def test_translations_follow_check_sh(self):
        self.assertEqual(ti.translations(self.fx.root, 'demo'), [
            {'zig': '0.16.0', 'target': 'linux', 'gen': 'Proofs/Demo/Gen.lean'},
            {'zig': '0.15.2', 'target': 'linux', 'gen': 'tests/golden/0.15.2/demo/Gen.lean'}])
        self.assertEqual([t['zig'] for t in ti.translations(self.fx.root, 'conc')], ['0.16.0'])
        darwin = self.fx.root / 'tests/golden/0.16.0/conc/Gen-darwin.lean'
        darwin.parent.mkdir(parents=True)
        darwin.write_text('x')
        self.assertEqual(ti.translations(self.fx.root, 'conc')[1],
                         {'zig': '0.16.0', 'target': 'darwin', 'gen': str(darwin.relative_to(self.fx.root))})

    def test_no_run_is_no_result(self):
        self.assertError('Demo.f_spec: no current check result for 0.16.0/linux')
        self.assertError('Conc.main_spec: no current check result for 0.16.0/linux')

    def test_recorded_runs_pass(self):
        self.fx.record_all()
        self.assertEqual(self.fx.errors(), [])
        run = self.fx.load()['runs']['demo-0152']
        self.assertEqual(run['modules'], ['Proofs.Demo.Proofs'])
        self.assertEqual(run['gens']['demo']['path'], 'tests/golden/0.15.2/demo/Gen.lean')
        self.assertEqual(run['command'][1], 'scripts/theorem-inventory.py')
        doc = (self.fx.root / ti.DOC).read_text()
        self.assertIn('`Demo.f_spec`', doc)
        self.assertIn('0.15.2/linux: pass, run `demo-0152`', doc)

    def test_one_version_missing(self):
        self.fx.record('all', '0.16.0', *self.fx.guard('all', ['lake', 'build', 'Proofs'], 'ok\n'))
        errors = self.fx.errors()
        self.assertTrue(any('Demo.f_spec: no current check result for 0.15.2/linux' in e for e in errors))
        self.assertFalse(any('0.16.0/linux' in e for e in errors), errors)

    def test_failed_run_is_no_result(self):
        self.fx.record('all', '0.16.0', *self.fx.guard('all', ['lake', 'build', 'Proofs'], 'error\n',
                                                       outcome='child_failed', exit_code=1))
        self.assertError('Demo.f_spec: no current check result for 0.16.0/linux')

    def test_edited_proof_or_translation_is_stale(self):
        self.fx.record_all()
        path = self.fx.root / 'Proofs/Demo/Proofs.lean'
        path.write_text(path.read_text() + '\n')
        self.assertError('Demo.f_spec: no current check result for 0.16.0/linux')
        self.fx.record_all()
        gen = self.fx.root / 'tests/golden/0.15.2/demo/Gen.lean'
        gen.write_text(gen.read_text() + '\n')
        self.assertError('Demo.f_spec: no current check result for 0.15.2/linux')

    def test_excluded_translation_needs_a_reason_and_a_translation(self):
        inv = self.fx.load()
        inv['theorems'][0]['excluded'] = [{'zig': '0.15.2', 'target': 'linux', 'reason': 'differs'}]
        self.fx.save(inv)
        self.assertFalse(any('Demo.f_spec: no current check result for 0.15.2' in e for e in self.fx.errors()))
        inv['theorems'][0]['excluded'] = [{'zig': '0.14.1', 'target': 'linux', 'reason': 'x'}]
        self.fx.save(inv)
        self.assertError('Demo.f_spec: excludes 0.14.1/linux, which is not a translation')

    def test_narrow_theorem_labeled_all_schedules_in_docs(self):
        self.fx.record_all()
        doc = self.fx.root / 'docs/proofs.md'
        doc.write_text(doc.read_text().replace('`main_sc` (one schedule)', '`main_sc` (0 under every schedule)'))
        self.assertError('docs/proofs.md:8: says every schedule of `main_sc`, whose scope is single-schedule')

    def test_prose_claim_and_negated_rule(self):
        self.fx.record_all()
        readme = self.fx.root / 'README.md'
        readme.write_text('A one-schedule theorem is not labeled all-schedules; see `main_sc`.\n'
                          '`main_sc` holds under every schedule.\n')
        errors = self.fx.errors()
        self.assertEqual([e for e in errors if 'README.md' in e],
                         ['README.md:2: says every schedule of `main_sc`, whose scope is single-schedule'])

    def test_doc_comment_claim_on_narrow_theorem(self):
        self.fx.record_all()
        path = self.fx.root / 'Proofs/Conc/Proofs.lean'
        path.write_text(path.read_text().replace('/-- One schedule. -/', '/-- 0 under every schedule. -/'))
        self.fx.record_all()
        self.assertError('Conc.main_sc: its doc comment claims every schedule')

    def test_section_comment_is_not_a_doc_comment(self):
        path = self.fx.root / 'Proofs/Conc/Proofs.lean'
        path.write_text(path.read_text().replace(
            '/-- One schedule. -/', '/-! The specs over all schedules are above.\n-/'))
        self.fx.record_all()
        self.assertEqual(self.fx.errors(), [])

    def test_all_schedules_scope_needs_the_statement(self):
        inv = self.fx.load()
        inv['theorems'][2]['scope'] = 'all-schedules'
        self.fx.save(inv)
        self.assertError('Conc.main_sc: scope all-schedules, but its statement does not quantify')

    def test_unknown_scope_and_missing_theorem(self):
        inv = self.fx.load()
        inv['theorems'][0]['scope'] = 'most-schedules'
        inv['theorems'][1]['name'] = 'Conc.gone_spec'
        self.fx.save(inv)
        self.assertError("Demo.f_spec: unknown scope 'most-schedules'")
        self.assertError('Conc.gone_spec: no `theorem` of this name')

    def test_unlisted_proved_example(self):
        inv = self.fx.load()
        del inv['theorems'][0]
        self.fx.save(inv)
        self.assertError('docs/proofs.md: `f_spec` (Proofs.Demo.Proofs) is not in')

    def test_stale_document(self):
        self.fx.record_all()
        doc = self.fx.root / ti.DOC
        doc.write_text(doc.read_text().replace('every x', 'every y'))
        self.assertError('docs/theorem-inventory.md is stale')

    def test_record_rejects_a_foreign_log(self):
        report, log = self.fx.guard('all', ['lake', 'build', 'Proofs'], 'ok\n')
        log.write_text('edited\n')
        self.fx.assert_main(['record', '--run', 'x', '--zig', '0.16.0', '--guard-report', str(report),
                             '--guard-log', str(log)], code=1)
        self.assertEqual(self.fx.load()['runs'], {})

    def test_record_rejects_a_changed_swapped_translation(self):
        swap = 'tests/golden/0.15.2/demo/Gen.lean'
        report, log = self.fx.guard('demo', ['python3', 'x', 'swap-build', '--', 'Proofs.Demo.Proofs'],
                                    f'{ti.SWAP_PREFIX}demo {swap} {"0" * 64}\n')
        self.fx.assert_main(['record', '--run', 'x', '--zig', '0.15.2', '--guard-report', str(report),
                             '--guard-log', str(log)], code=1)

    def test_swap_build_restores_the_committed_translation(self):
        bin_dir = Path(self.temp.name) / 'bin'
        bin_dir.mkdir()
        lake = bin_dir / 'lake'
        seen = Path(self.temp.name) / 'seen'
        lake.write_text(f'#!/bin/sh\ncat Proofs/Demo/Gen.lean > {seen}\nexit 3\n')
        lake.chmod(lake.stat().st_mode | stat.S_IEXEC)
        committed = (self.fx.root / 'Proofs/Demo/Gen.lean').read_text()
        old_path = os.environ['PATH']
        os.environ['PATH'] = f'{bin_dir}{os.pathsep}{old_path}'
        try:
            status = ti.main(['--root', str(self.fx.root), 'swap-build', '--swap',
                              'demo=tests/golden/0.15.2/demo/Gen.lean', '--', 'Proofs.Demo.Proofs'])
        finally:
            os.environ['PATH'] = old_path
        self.assertEqual(status, 3)
        self.assertEqual(seen.read_text(), FILES['tests/golden/0.15.2/demo/Gen.lean'])
        self.assertEqual((self.fx.root / 'Proofs/Demo/Gen.lean').read_text(), committed)


class RepositoryTests(unittest.TestCase):
    def test_committed_inventory_is_current(self):
        self.assertEqual(ti.check(ROOT), [])

    def test_threaded_clients_are_all_schedules_and_facts_are_narrower(self):
        inv = json.loads((ROOT / ti.INVENTORY).read_text())
        scope = {t['name']: t['scope'] for t in inv['theorems']}
        for name in ('Sync.RwLockRead.rwLockRead_spec', 'Sync.RwLockSnapshotPair.snapshotPair_safe',
                     'Threadsync.MutexCounter.mutexCounter_spec', 'Atomics.Stack.stackPush_safe'):
            self.assertEqual(scope[name], 'all-schedules', name)
        for name in ('sb_sc', 'mp_sees_data', 'tryLock_new'):
            self.assertEqual(scope[name], 'single-schedule', name)
        for name in ('Zig.readOpts_zero', 'Sync.RwLockContract.held_pair_wp', 'Sync.MutexOps.lock_spec'):
            self.assertEqual(scope[name], 'single-step', name)

    def test_f05_exclusion_is_in_the_statement_and_the_domain(self):
        inv = json.loads((ROOT / ti.INVENTORY).read_text())
        op128 = next(t for t in inv['theorems'] if t['name'] == 'op128_spec')
        self.assertIn('except 3, 5, 6 and 9', op128['domain'])
        statement = ti.declarations((ROOT / 'Proofs/Floatops/Proofs.lean').read_text())['op128_spec']
        self.assertIn('sel ≠ 3 ∧ sel ≠ 5 ∧ sel ≠ 6 ∧ sel ≠ 9', statement['statement'])


if __name__ == '__main__':
    unittest.main()
