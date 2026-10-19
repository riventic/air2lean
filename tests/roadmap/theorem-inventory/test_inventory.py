#!/usr/bin/env python3
"""D02 theorem inventory regressions: the committed inventory and fail-closed fixtures."""
import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shlex
import stat
import subprocess
import sys
import tempfile
import textwrap
import unittest
from unittest import mock

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location('theorem_inventory', ROOT / 'scripts/theorem-inventory.py')
ti = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ti)
REGEN_SPEC = importlib.util.spec_from_file_location('inventory_regen', ROOT / 'scripts/regen.py')
regen = importlib.util.module_from_spec(REGEN_SPEC)
REGEN_SPEC.loader.exec_module(regen)

FILES = {
    'lean-toolchain': 'fixture-toolchain\n',
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
            (h : (Sched.run env dispatch fuel o main mem0).run = some v) : v = 0 := sorry
        /-- One schedule. -/
        theorem main_sc : okVal (Sched.run env dispatch 100 (sched []) main mem0) = some 0 := by
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
    # Stub attestation: exit 0 unless a listed path is named in STALE.
    'scripts/gen-integrity.py': '''\
        import sys
        from pathlib import Path
        stale = (Path(__file__).parent / 'STALE').read_text().split() if (Path(__file__).parent / 'STALE').exists() else []
        assert sys.argv[1] == 'attest'
        bad = [p for p in sys.argv[2:] if p in stale]
        if bad:
            sys.exit('error: ' + ' '.join(bad) + ': not a fresh translation of its committed AIR')
        ''',
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
        self.lake = (root.parent / 'toolchain/bin/lake').resolve()
        self.lake.parent.mkdir(parents=True)
        self.lake.write_text('#!/bin/sh\nexit 0\n')
        self.lake.chmod(self.lake.stat().st_mode | stat.S_IEXEC)
        self.lake.with_name('lean').write_text('fixture Lean identity only\n')
        self.save({'schema': 1, 'theorems': [dict(t) for t in THEOREMS], 'runs': {}})

    def load(self):
        return json.loads((self.root / ti.INVENTORY).read_text())

    def save(self, inv):
        (self.root / ti.INVENTORY).parent.mkdir(parents=True, exist_ok=True)
        (self.root / ti.INVENTORY).write_text(json.dumps(inv))

    def producer(self):
        return {'path': str(self.lake), 'sha256': hashlib.sha256(self.lake.read_bytes()).hexdigest(),
                'bytes': self.lake.stat().st_size}

    def guard(self, name, command, log_text, outcome='success', exit_code=0, prepare=True):
        """Stub guard metadata; prepare valid commands as a fresh selected-producer run."""
        tools = []
        try:
            build = ti.parse_build_command(self.root, command, lake=str(self.lake))
            if prepare:
                command = build.invocation(self.lake)
            observer = {'path': '/fixture/observer', 'sha256': 'e' * 64, 'bytes': 1}
            tools = [self.producer() if build.kind == 'lake' else observer, observer, observer]
            if build.kind == 'swap':
                tools.append(self.producer())
        except ti.Error:
            pass  # Malformed commands remain malformed for rejection controls.
        log = self.root.parent / f'{name}.log'
        log.write_text(log_text)
        report = self.root.parent / f'{name}.json'
        report.write_text(json.dumps({
            'schema': 1, 'cwd': str(self.root), 'command': command, 'requested_command': command,
            'tools': tools, 'outcome': outcome, 'exit_code': exit_code,
            'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest(), 'log_truncated': False,
            'pins': [{'path': str((self.root / 'lean-toolchain').resolve()),
                      'sha256': ti.sha256(self.root / 'lean-toolchain'),
                      'bytes': (self.root / 'lean-toolchain').stat().st_size}],
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

    @contextlib.contextmanager
    def fake_lake(self, exit_code=0):
        """Observe check-tree bytes without elaborating Lean or qualifying a proof."""
        bin_dir = self.root.parent / 'bin'
        bin_dir.mkdir(exist_ok=True)
        seen = self.root.parent / 'seen'
        self.lake.write_text(f'#!/bin/sh\ncat Proofs/Demo/Gen.lean > {shlex.quote(str(seen))}\nexit {exit_code}\n')
        shadow = bin_dir / 'lake'
        shadow.write_text(f'#!/bin/sh\ntouch {shlex.quote(str(self.root.parent / "shadow-called"))}\nexit 97\n')
        shadow.chmod(shadow.stat().st_mode | stat.S_IEXEC)
        old_path = os.environ['PATH']
        os.environ['PATH'] = f'{bin_dir}{os.pathsep}{old_path}'
        try:
            yield seen
        finally:
            os.environ['PATH'] = old_path


class FixtureTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.fx = Fixture(Path(self.temp.name) / 'repo')
        self.selected_lake_impl = ti.selected_lake
        resolver = mock.patch.object(ti, 'selected_lake', return_value=self.fx.lake)
        self.lake_resolver = resolver.start()
        self.addCleanup(resolver.stop)

    def tearDown(self):
        self.temp.cleanup()

    def assertError(self, fragment):
        errors = self.fx.errors()
        self.assertTrue(any(fragment in e for e in errors), errors)

    def assertRunCurrent(self, run_id, expected):
        with mock.patch.object(regen, 'ROOT', self.fx.root):
            self.assertEqual(regen.run_is_current(ti, self.fx.load()['runs'][run_id]), expected)

    def assertReplayRuns(self, *run_ids):
        # Exercise dispatch only: no guard, replay, record command or compiler executes.
        with mock.patch.object(regen, 'ROOT', self.fx.root), \
                mock.patch.object(regen, 'load', return_value=ti), \
                mock.patch.object(regen, 'guarded', return_value=('report.json', 'guard.log')) as guarded, \
                mock.patch.object(regen, 'run') as run, \
                mock.patch.object(regen, 'ok', return_value=True), \
                mock.patch.object(regen, 'lake_env', return_value={}):
            regen.step_inventory(False)
        self.assertEqual([call.args[0] for call in guarded.call_args_list],
                         ['inventory-' + name for name in sorted(run_ids)])
        self.assertEqual(run.call_count, len(run_ids))
        return guarded.call_args_list

    def assertReplayRejected(self):
        # Unsupported historical argv must be refused before any guarded dispatch.
        resolves = self.lake_resolver.call_count
        with mock.patch.object(regen, 'ROOT', self.fx.root), \
                mock.patch.object(regen, 'load', return_value=ti), \
                mock.patch.object(regen, 'guarded') as guarded, \
                mock.patch.object(regen, 'run') as run, \
                mock.patch.object(regen, 'lake_env') as lake_env:
            with self.assertRaisesRegex(regen.Failed, 'refusing replay'):
                regen.step_inventory(False)
        guarded.assert_not_called()
        run.assert_not_called()
        lake_env.assert_not_called()
        self.assertEqual(self.lake_resolver.call_count, resolves)

    def assertSwapRejected(self, spec, fragment):
        command = ['python3', str(self.fx.root / 'scripts/theorem-inventory.py'),
                   'swap-build', '--swap', spec, '--', 'Proofs.Demo.Proofs']
        error = io.StringIO()
        with contextlib.redirect_stderr(error):
            self.fx.assert_main(command[2:], code=1)
        self.assertIn(fragment, error.getvalue())
        alias, _, source = spec.partition('=')
        report, log = self.fx.guard('bad-swap', command,
                                   f'{ti.SWAP_PREFIX}{alias} {source} {"0" * 64}\n')
        error = io.StringIO()
        with contextlib.redirect_stderr(error):
            self.fx.assert_main(['record', '--run', 'bad-swap', '--zig', '0.15.2',
                                 '--guard-report', str(report), '--guard-log', str(log)], code=1)
        self.assertIn(fragment, error.getvalue())
        self.assertEqual(self.fx.load()['runs'], {})

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

    def test_retained_translation(self):
        # A theorem over a retained translation (`gen`): only that file, its version from the
        # profile record; a run records it under its module, and an edit makes the run stale.
        profile = {'profile': {'zig_version': '0.17.0', 'target_triple': 'x86_64-linux-musl'}}
        (self.fx.root / 'Proofs/Demo/Open.lean').write_text(
            f'{ti.PROFILE_PREFIX}{json.dumps(profile)}\nnamespace Demo.Open\ndef g : Nat := 0\nend Demo.Open\n')
        (self.fx.root / 'Proofs/Demo/OpenProofs.lean').write_text(
            'import Proofs.Demo.Open\nnamespace Demo\ntheorem g_spec : Open.g = 0 := rfl\nend Demo\n')
        inv = self.fx.load()
        inv['theorems'].append({'name': 'Demo.g_spec', 'module': 'Proofs.Demo.OpenProofs', 'example': 'demo',
                                'gen': 'Proofs/Demo/Open.lean', 'scope': 'sequential', 'domain': 'g'})
        self.fx.save(inv)
        self.assertError('Demo.g_spec: no current check result for 0.17.0/linux (Proofs/Demo/Open.lean)')
        self.fx.record_all()
        self.assertEqual(self.fx.errors(), [])
        self.assertEqual(self.fx.load()['runs']['all']['gens']['Proofs.Demo.Open']['path'],
                         'Proofs/Demo/Open.lean')
        gen = self.fx.root / 'Proofs/Demo/Open.lean'
        gen.write_text(gen.read_text() + '\n')
        self.assertError('Demo.g_spec: no current check result for 0.17.0/linux')
        inv = self.fx.load()
        inv['theorems'][-1].update(name='Demo.f_spec', module='Proofs.Demo.Proofs')
        self.fx.save(inv)
        self.assertError('Demo.f_spec: Proofs.Demo.Proofs does not import Proofs.Demo.Open')

    def test_canonical_and_deeper_gen_coexist_and_invalidate_separately(self):
        profile = {'profile': {'zig_version': '0.16.0', 'target_triple': 'x86_64-linux-musl'}}
        case_path = 'Proofs/Demo/Gen/V0_16_0/Linux/Gen.lean'
        case_module = 'Proofs.Demo.Gen.V0_16_0.Linux.Gen'
        gen = self.fx.root / case_path
        gen.parent.mkdir(parents=True)
        gen.write_text(f'{ti.PROFILE_PREFIX}{json.dumps(profile)}\n'
                       'namespace Demo.Gen.V0_16_0.Linux\ndef g : Nat := 0\nend Demo.Gen.V0_16_0.Linux\n')
        (self.fx.root / 'Proofs/Demo/CaseProofs.lean').write_text(
            f'import Proofs.Demo.Gen\nimport {case_module}\n'
            'namespace Demo\ntheorem case_spec : Gen.V0_16_0.Linux.g = 0 := rfl\nend Demo\n')
        inv = self.fx.load()
        inv['theorems'].append({'name': 'Demo.case_spec', 'module': 'Proofs.Demo.CaseProofs',
                                'example': 'demo', 'gen': case_path,
                                'scope': 'sequential', 'domain': 'g'})
        self.fx.save(inv)
        self.fx.record_all()

        self.assertEqual(self.fx.errors(), [])
        run = self.fx.load()['runs']['all']
        canonical = 'Proofs/Demo/Gen.lean'
        self.assertEqual(run['gens']['demo'],
                         {'path': canonical, 'sha256': ti.sha256(self.fx.root / canonical)})
        self.assertEqual(run['gens'][case_module], {'path': case_path, 'sha256': ti.sha256(gen)})
        self.assertNotIn(case_module, run['sources'])
        self.assertEqual(self.fx.load()['runs']['demo-0152']['gens']['demo']['path'],
                         'tests/golden/0.15.2/demo/Gen.lean')

        gen.write_text(gen.read_text() + '\n')
        errors = self.fx.errors()
        self.assertTrue(any('Demo.case_spec: no current check result for 0.16.0/linux' in e
                            for e in errors), errors)
        self.assertFalse(any('Demo.f_spec: no current check result' in e for e in errors), errors)
        self.fx.record('case-refresh', '0.16.0', *self.fx.guard(
            'case-refresh', ['lake', 'build', 'Proofs.Demo.CaseProofs'], 'Build completed\n'))
        ti.check(self.fx.root, write=True)
        self.assertEqual(self.fx.errors(), [])
        self.assertEqual(self.fx.load()['runs']['case-refresh']['gens'][case_module]['sha256'],
                         ti.sha256(gen))

    def test_imported_deeper_gen_without_profile_is_hash_checked(self):
        helper = self.fx.root / 'Proofs/Demo/Helper/Gen.lean'
        helper.parent.mkdir(parents=True)
        helper.write_text('namespace Demo.Helper\ndef g : Nat := 0\nend Demo.Helper\n')
        proof = self.fx.root / 'Proofs/Demo/Proofs.lean'
        proof.write_text('import Proofs.Demo.Helper.Gen\n' + proof.read_text())
        self.fx.record_all()

        self.assertEqual(self.fx.errors(), [])
        run = self.fx.load()['runs']['all']
        self.assertEqual(run['gens']['Proofs.Demo.Helper.Gen'],
                         {'path': 'Proofs/Demo/Helper/Gen.lean', 'sha256': ti.sha256(helper)})
        self.assertNotIn('Proofs.Demo.Helper.Gen', run['sources'])
        helper.write_text(helper.read_text() + '\n')
        self.assertError('Demo.f_spec: no current check result for 0.16.0/linux')

    def test_legacy_incomplete_or_foreign_deeper_gen_evidence_is_rejected(self):
        # A check tree copies unignored untracked imports too. These are stub inventory
        # records, including a legacy-incomplete shape, never real Lean qualification.
        subprocess.run(['git', 'init', '-q', str(self.fx.root)], check=True)
        subprocess.run(['git', '-C', str(self.fx.root), 'add', '.'], check=True)
        helper_path = 'Proofs/Demo/Aux/Gen.lean'
        helper_module = 'Proofs.Demo.Aux.Gen'
        helper = self.fx.root / helper_path
        helper.parent.mkdir(parents=True)
        helper.write_text('namespace Demo.Aux\ndef g : Nat := 0\nend Demo.Aux\n')
        proof = self.fx.root / 'Proofs/Demo/Proofs.lean'
        proof.write_text(f'import {helper_module}\n' + proof.read_text())
        with self.fx.fake_lake():
            self.fx.assert_main(['swap-build', '--swap', 'demo=tests/golden/0.15.2/demo/Gen.lean',
                                 '--', 'Proofs.Demo.Proofs'])
        copied = self.fx.root / '.lake/check-tree/theorem-inventory' / helper_path
        self.assertEqual(copied.read_bytes(), helper.read_bytes())
        untracked = subprocess.run(['git', '-C', str(self.fx.root), 'ls-files', '--others',
                                    '--exclude-standard'], check=True, capture_output=True, text=True).stdout
        self.assertIn(helper_path, untracked.splitlines())
        self.fx.record_all()
        self.assertEqual(self.fx.errors(), [])
        self.assertRunCurrent('all', True)
        self.assertRunCurrent('demo-0152', True)
        canonical_sha = ti.sha256(self.fx.root / 'Proofs/Demo/Gen.lean')
        foreign = 'tests/foreign-gen.lean'
        (self.fx.root / foreign).write_bytes(helper.read_bytes())
        inv = self.fx.load()
        for run in inv['runs'].values():
            run['gens'][helper_module]['path'] = foreign
        self.fx.save(inv)
        self.assertError('Demo.f_spec: no current check result for 0.16.0/linux')
        self.assertRunCurrent('all', False)
        self.assertRunCurrent('demo-0152', False)
        self.assertReplayRuns('all', 'demo-0152')

        for run in inv['runs'].values():
            del run['gens'][helper_module]
        self.fx.save(inv)
        self.assertError('Demo.f_spec: no current check result for 0.16.0/linux')
        self.assertRunCurrent('all', False)
        self.assertRunCurrent('demo-0152', False)
        self.assertReplayRuns('all', 'demo-0152')
        helper.write_text(helper.read_text() + '\n')
        self.assertEqual(ti.sha256(self.fx.root / 'Proofs/Demo/Gen.lean'), canonical_sha)
        self.assertError('Demo.f_spec: no current check result for 0.16.0/linux')
        self.assertRunCurrent('all', False)
        self.assertRunCurrent('demo-0152', False)
        self.fx.record_all()
        self.assertEqual(self.fx.errors(), [])
        self.assertRunCurrent('all', True)
        self.assertReplayRuns()

    def test_historical_wrong_swap_identity_is_stale_in_reader_and_regen(self):
        self.fx.record_all()
        canonical = 'Proofs/Demo/Gen.lean'
        golden = 'tests/golden/0.15.2/demo/Gen.lean'
        inv = self.fx.load()
        old = inv['runs']['demo-0152']
        old['command'][old['command'].index('--swap') + 1] = 'Demo=' + golden
        old['gens']['demo'] = {'path': canonical, 'sha256': ti.sha256(self.fx.root / canonical)}
        inv['runs'] = {'legacy-mixed': old}
        self.fx.save(inv)
        theorem = THEOREMS[0]
        closure = ti.closure(self.fx.root, [theorem['module']])
        translation = ti.translations(self.fx.root, 'demo')[0]
        self.assertIsNone(ti.current_result(self.fx.root, inv, theorem, translation, closure))
        self.assertRunCurrent('legacy-mixed', False)
        self.assertReplayRuns('legacy-mixed')
        self.assertEqual(self.fx.load()['runs']['legacy-mixed']['gens']['demo']['path'], canonical)

        log = f'{ti.SWAP_PREFIX}demo {golden} {ti.sha256(self.fx.root / golden)}\n'
        self.fx.record('fresh', '0.15.2', *self.fx.guard('fresh', old['command'], log))
        fresh = self.fx.load()
        self.assertEqual(ti.current_result(self.fx.root, fresh, theorem,
                                           ti.translations(self.fx.root, 'demo')[1], closure), 'fresh')
        self.assertRunCurrent('fresh', True)
        self.assertReplayRuns('legacy-mixed')

    def test_regen_preserves_toolchain_all_entry_hashes_and_module_membership(self):
        self.fx.record_all()
        self.assertRunCurrent('all', True)
        self.assertReplayRuns()
        with mock.patch.object(regen, 'ROOT', self.fx.root):
            run = self.fx.load()['runs']['all']
            run['lean_toolchain_sha256'] = '0' * 64
            self.assertFalse(regen.run_is_current(ti, run))
            run = self.fx.load()['runs']['all']
            run['gens']['extra'] = {'path': 'Proofs/Demo/Gen.lean', 'sha256': '0' * 64}
            self.assertFalse(regen.run_is_current(ti, run))
            run = self.fx.load()['runs']['all']
            run['sources']['Proofs.Demo.Missing'] = '0' * 64
            self.assertFalse(regen.run_is_current(ti, run))
        (self.fx.root / 'Proofs/Demo/Extra.lean').write_text('def extra : Nat := 0\n')
        self.assertRunCurrent('all', False)
        self.assertRunCurrent('demo-0152', True)
        self.assertReplayRuns('all')

    def test_unsupported_recorded_commands_are_noncurrent(self):
        self.fx.record_all()
        theorem = THEOREMS[0]
        closure = ti.closure(self.fx.root, [theorem['module']])
        translation = ti.translations(self.fx.root, 'demo')[0]
        script = str(self.fx.root / 'scripts/theorem-inventory.py')
        for command in (None, [], ['unknown'], ['/bin/echo', 'swap-build', '--', 'Proofs'],
                        ['python3', 'x', 'swap-build', '--', 'Proofs'],
                        ['python3', '-c', 'pass', script, 'swap-build', '--', 'Proofs'],
                        ['env', 'python3', script, 'swap-build', '--', 'Proofs'],
                        ['python3', script, '--root', str(self.fx.root / 'other'), 'swap-build', 'Proofs'],
                        ['python3', script, 'check'], ['python3', script, 'swap-build', '--help'],
                        ['python3', script, 'swap-build', '--swap'],
                        ['python3', script, 'swap-build', '--swap=demo.=Proofs/Demo/Gen.lean', 'Proofs'],
                        ['lake', 'env', 'lean', 'Proofs'], ['lake', 'build'],
                        ['lake', '--help', 'build', 'Proofs'], ['lake', '--version'],
                        ['lake', 'build', '--', 'Proofs']):
            with self.subTest(command=command):
                inv = self.fx.load()
                run = inv['runs']['all']
                run['command'] = command
                inv['runs'] = {'all': run}
                self.fx.save(inv)
                self.assertIsNone(ti.current_result(self.fx.root, inv, theorem, translation, closure))
                self.assertRunCurrent('all', False)
                self.assertReplayRejected()
                report, log = self.fx.guard('unsupported', command, '')
                with contextlib.redirect_stderr(io.StringIO()):
                    self.fx.assert_main(['record', '--run', 'unsupported', '--zig', '0.16.0',
                                         '--guard-report', str(report), '--guard-log', str(log)], code=1)
                self.assertEqual(self.fx.load()['runs'], inv['runs'])

    def test_lake_workspace_or_unknown_options_are_rejected_in_every_position(self):
        self.fx.record_all()
        for option in (['--dir', 'OTHER'], ['--dir=OTHER'], ['-d', 'OTHER'],
                       ['--file', 'other.toml'], ['-fother.toml'], ['-Kkey=value'],
                       ['--packages', 'other.json'], ['--update'], ['--old'], ['--unknown']):
            for command in (['lake', *option, 'build', 'Proofs'],
                            ['lake', 'build', *option, 'Proofs'],
                            ['lake', 'build', 'Proofs', *option]):
                with self.subTest(command=command):
                    with self.assertRaisesRegex(ti.Error, 'unsupported Lake option'):
                        ti.parse_build_command(self.fx.root, command)
                    inv = self.fx.load()
                    inv['runs'] = {'all': inv['runs']['all']}
                    inv['runs']['all']['command'] = command
                    self.fx.save(inv)
                    self.assertRunCurrent('all', False)
                    theorem = THEOREMS[0]
                    self.assertIsNone(ti.current_result(self.fx.root, inv, theorem,
                        ti.translations(self.fx.root, 'demo')[0], ti.closure(self.fx.root, [theorem['module']])))
                    self.assertReplayRejected()
                    report, log = self.fx.guard('workspace', command, '')
                    with contextlib.redirect_stderr(io.StringIO()):
                        self.fx.assert_main(['record', '--run', 'workspace', '--zig', '0.16.0',
                                             '--guard-report', str(report), '--guard-log', str(log)], code=1)
                    self.assertEqual(self.fx.load()['runs'], inv['runs'])

    def test_root_preserving_lake_options_record_and_remain_current(self):
        for command in (['lake', '--rehash', 'build', 'Proofs.Demo.Proofs'],
                        ['lake', '-H', 'build', 'Proofs.Demo.Proofs'],
                        ['lake', 'build', '-H', 'Proofs.Demo.Proofs'],
                        ['lake', 'build', 'Proofs.Demo.Proofs', '--rehash', '--no-build',
                         '--log-level=error', '--fail-level', 'warning', '--quiet'],
                        ['lake', '--verbose', 'build', 'Proofs', '--json', '--no-ansi', '--offline']):
            with self.subTest(command=command):
                self.fx.record('valid', '0.16.0', *self.fx.guard('valid', command, 'ok\n'))
                inv = self.fx.load()
                inv['runs'] = {'valid': inv['runs']['valid']}
                self.fx.save(inv)
                self.assertRunCurrent('valid', True)
                self.assertReplayRuns()
                theorem = THEOREMS[0]
                self.assertEqual(ti.current_result(self.fx.root, inv, theorem,
                    ti.translations(self.fx.root, 'demo')[0], ti.closure(self.fx.root, [theorem['module']])), 'valid')

    def test_selected_lake_lookup_fixes_pin_without_running_toolchain(self):
        # Exercise only the resolver's command construction, with Elan itself mocked.
        result = subprocess.CompletedProcess([], 0, str(self.fx.lake) + '\n', '')
        with mock.patch.object(ti.subprocess, 'run', return_value=result) as run:
            self.assertEqual(self.selected_lake_impl(self.fx.root), self.fx.lake)
        self.assertEqual(run.call_args.args[0], ['elan', 'which', 'lake'])
        self.assertEqual(run.call_args.kwargs['cwd'], self.fx.root)
        self.assertEqual(run.call_args.kwargs['env']['ELAN_TOOLCHAIN'], 'fixture-toolchain')
        for result in (subprocess.CompletedProcess([], 1, '', 'not installed'),
                       subprocess.CompletedProcess([], 0, 'relative/lake\n', ''),
                       subprocess.CompletedProcess([], 0, '/missing-toolchain/bin/lake\n', '')):
            with self.subTest(result=result), mock.patch.object(ti.subprocess, 'run', return_value=result):
                with self.assertRaises(ti.Error):
                    self.selected_lake_impl(self.fx.root)

    def test_regen_guard_passes_explicit_tool_capture_before_command(self):
        # Only guard argv construction runs; its subprocess and admission are mocked.
        with mock.patch.object(regen, 'ROOT', self.fx.root), \
                mock.patch.object(regen, 'WORK', self.fx.root.parent / 'mock-guard'), \
                mock.patch.object(regen, 'run', return_value=subprocess.CompletedProcess([], 0)) as run:
            regen.guarded('nested', ['python3', 'scripts/theorem-inventory.py'], tools=[self.fx.lake])
        argv = run.call_args.args[0]
        self.assertEqual(str(argv[argv.index('--tool') + 1]), str(self.fx.lake))
        self.assertLess(argv.index('--tool'), argv.index('--'))

    def test_selected_lake_entry_resolves_its_own_custom_named_target(self):
        physical = self.fx.root.parent / 'store/lake-4.34'
        physical.parent.mkdir()
        physical.write_bytes(self.fx.lake.read_bytes())
        physical.chmod(self.fx.lake.stat().st_mode)
        linked = self.fx.root.parent / 'linked/bin/lake'
        linked.parent.mkdir(parents=True)
        linked.symlink_to(physical)
        # A Lean sibling can point somewhere unrelated: it must never select Lake's directory.
        linked.with_name('lean').symlink_to(self.fx.lake.with_name('lean'))
        result = subprocess.CompletedProcess([], 0, str(linked) + '\n', '')
        with mock.patch.object(ti.subprocess, 'run', return_value=result) as run:
            self.assertEqual(self.selected_lake_impl(self.fx.root), physical.resolve())
        self.assertEqual(run.call_args.args[0], ['elan', 'which', 'lake'])
        self.fx.lake = physical.resolve()
        with mock.patch.object(ti, 'selected_lake', return_value=self.fx.lake):
            self.fx.record_all()
            self.assertEqual(self.fx.errors(), [])
            for saved in self.fx.load()['runs'].values():
                self.assertEqual(ti.prepare_run(self.fx.root, saved)[0].lake, str(self.fx.lake))
            inv = self.fx.load()
            inv['runs'] = {'all': inv['runs']['all']}
            inv['runs']['all']['command'] = ['/bin/echo', 'build', 'Proofs']
            self.fx.save(inv)
            self.assertRunCurrent('all', False)
            self.assertReplayRejected()
        with self.assertRaises(ti.Error):
            ti.parse_build_command(self.fx.root, [str(physical), 'build', 'Proofs'])

    def test_run_preparation_is_lazy_invocation_local_and_direct_calls_are_fresh(self):
        self.fx.record_all()
        inv = self.fx.load()
        filtered = json.loads(json.dumps(inv['runs']['all']))
        filtered['outcome'] = 'child_failed'
        inv['runs']['00-failed'] = filtered
        with mock.patch.object(ti, 'prepare_run', wraps=ti.prepare_run) as prepare:
            rows, errors = ti.results(self.fx.root, inv)
            self.assertEqual(errors, [])
        self.assertEqual(prepare.call_count, 2)  # all once, demo-0152 once, never the failed run.
        self.assertTrue(all(call.args[1]['outcome'] == 'success' for call in prepare.call_args_list))
        self.assertEqual(rows[0]['checks'][0]['run'], 'all')
        self.assertEqual(rows[0]['checks'][1]['run'], 'demo-0152')
        theorem = THEOREMS[0]
        tr = ti.translations(self.fx.root, 'demo')[0]
        closure = ti.closure(self.fx.root, [theorem['module']])
        with mock.patch.object(ti, 'prepare_run', wraps=ti.prepare_run) as prepare:
            self.assertEqual(ti.current_result(self.fx.root, inv, theorem, tr, closure), 'all')
            (self.fx.root / 'Proofs/Demo/Extra.lean').write_text('def extra : Nat := 0\n')
            self.assertIsNone(ti.current_result(self.fx.root, inv, theorem, tr, closure))
        self.assertEqual(prepare.call_count, 2)

    def test_shared_import_scanner_tracks_all_supported_header_forms(self):
        helper_module = 'Proofs.Demo.Helper.Gen'
        helper = self.fx.root / 'Proofs/Demo/Helper/Gen.lean'
        helper.parent.mkdir()
        body = 'namespace Demo.Helper\ndef g : Nat := 0\nend Demo.Helper\n'
        proof = self.fx.root / 'Proofs/Demo/Proofs.lean'
        original = textwrap.dedent(FILES['Proofs/Demo/Proofs.lean'])
        for directive in (f'public import {helper_module}', f'meta import {helper_module}',
                          f'public meta import {helper_module}', f'import all {helper_module}',
                          f'import\n{helper_module}',
                          f'public /- outer /- nested -/ -/ meta import {helper_module}'):
            with self.subTest(directive=directive):
                helper.write_text(body)
                proof.write_text('module\n/- import Proofs.Missing -/\n' + directive + '\n' + original)
                self.fx.record_all()
                self.assertEqual(self.fx.errors(), [])
                self.assertIn(helper_module, self.fx.load()['runs']['demo-0152']['gens'])
                helper.write_text(body + '\n')
                self.assertError('Demo.f_spec: no current check result for 0.16.0/linux')
                self.assertRunCurrent('all', False)
                self.assertRunCurrent('demo-0152', False)
                self.assertReplayRuns('all', 'demo-0152')

    def test_unsupported_import_spelling_fails_closed_in_inventory(self):
        proof = self.fx.root / 'Proofs/Demo/Proofs.lean'
        proof.write_text('import Proofs.Demo.«Helper.Name»\n' + textwrap.dedent(FILES['Proofs/Demo/Proofs.lean']))
        with self.assertRaisesRegex(ti.Error, 'unsupported module spelling'):
            ti.closure(self.fx.root, ['Proofs.Demo.Proofs'])
        self.assertError('unsupported module spelling')

    def test_unimported_gen_drift_is_theorem_current_but_whole_run_stale(self):
        unused = self.fx.root / 'Proofs/Unused/Gen.lean'
        unused.parent.mkdir()
        unused.write_text('def unrelated : Nat := 0\n')
        self.fx.record_all()
        unused.write_text('def unrelated : Nat := 1\n')
        self.assertEqual(self.fx.errors(), [])
        self.assertRunCurrent('all', False)
        self.assertRunCurrent('demo-0152', True)
        self.assertReplayRuns('all')

    def test_direct_and_nested_producer_capture_positions(self):
        commands = (['lake', 'build', 'Proofs'],
                    ['python3', 'scripts/theorem-inventory.py', 'swap-build', 'Proofs'])
        for command in commands:
            with self.subTest(command=command):
                report, log = self.fx.guard('producer', command, '')
                good = json.loads(report.read_text())
                index = 0 if command[0] == 'lake' else 3
                for mutation in ('missing', 'path', 'hash', 'bytes', 'position', 'pin', 'command'):
                    bad = json.loads(json.dumps(good))
                    if mutation == 'missing':
                        del bad['tools']
                    elif mutation in ('path', 'hash', 'bytes'):
                        key = 'sha256' if mutation == 'hash' else mutation
                        bad['tools'][index][key] = {'path': '/foreign/lake', 'sha256': '0' * 64, 'bytes': 0}[key]
                    elif mutation == 'position':
                        bad['tools'] = ([good['tools'][1]] * 3 + [self.fx.producer()]
                                        if index == 0 else [self.fx.producer(), *good['tools'][1:3]])
                    elif mutation == 'pin':
                        bad['pins'][0]['sha256'] = '0' * 64
                    else:
                        bad['requested_command'] = ['/bin/echo', 'success']
                    report.write_text(json.dumps(bad))
                    with self.subTest(mutation=mutation), contextlib.redirect_stderr(io.StringIO()):
                        self.fx.assert_main(['record', '--run', 'bad-producer', '--zig', '0.16.0',
                                             '--guard-report', str(report), '--guard-log', str(log)], code=1)
                    self.assertNotIn('bad-producer', self.fx.load()['runs'])
                report.write_text(json.dumps(good))
                self.fx.record('producer', '0.16.0', report, log)
                run = self.fx.load()['runs']['producer']
                self.assertEqual(run['producer'], self.fx.producer())
                build = ti.parse_build_command(self.fx.root, run['command'], lake=ti.producer_path(run))
                self.assertEqual(build.lake, str(self.fx.lake))
                self.assertRunCurrent('producer', True)

        for command in (['lake', 'build', 'Proofs'],
                        ['/foreign/toolchain/bin/lake', 'build', 'Proofs'],
                        ['python3', 'scripts/theorem-inventory.py', 'swap-build',
                         '--lake', '/foreign/toolchain/bin/lake', 'Proofs']):
            report, log = self.fx.guard('wrong-producer', command, '', prepare=False)
            with self.subTest(command=command), contextlib.redirect_stderr(io.StringIO()):
                self.fx.assert_main(['record', '--run', 'wrong-producer', '--zig', '0.16.0',
                                     '--guard-report', str(report), '--guard-log', str(log)], code=1)
            self.assertNotIn('wrong-producer', self.fx.load()['runs'])

    def test_old_records_renew_selected_producer_without_metadata_inference(self):
        self.fx.record_all()
        inv = self.fx.load()
        for run in inv['runs'].values():
            del run['producer']
        inv['runs']['all']['command'] = ['lake', 'build', 'Proofs']
        inv['runs']['demo-0152']['command'] = [
            'python3', 'scripts/theorem-inventory.py', 'swap-build', '--swap',
            'Demo=./tests/golden/0.15.2/demo/Gen.lean', 'Proofs.Demo.Proofs']
        self.fx.save(inv)
        self.assertError('Demo.f_spec: no current check result for 0.16.0/linux')
        self.assertRunCurrent('all', False)
        self.assertRunCurrent('demo-0152', False)
        calls = self.assertReplayRuns('all', 'demo-0152')
        self.assertEqual(calls[0].args[1], [str(self.fx.lake), 'build', 'Proofs'])
        nested = ti.parse_build_command(self.fx.root, calls[1].args[1])
        self.assertEqual(nested.lake, str(self.fx.lake))
        self.assertEqual(nested.swaps, {'demo': 'tests/golden/0.15.2/demo/Gen.lean'})
        self.assertEqual(calls[1].kwargs['tools'], [self.fx.lake])
        self.assertEqual(self.fx.load(), inv)  # A mocked replay never qualifies or rewrites old success.

    def test_cross_host_producer_paths_are_structural_and_replay_is_local(self):
        self.fx.record_all()
        inv = self.fx.load()
        foreign = '/foreign-host/toolchain/bin/lake-4.34'
        for run in inv['runs'].values():
            plan = ti.parse_build_command(self.fx.root, run['command'], lake=ti.producer_path(run))
            run['command'] = plan.invocation(Path(foreign))
            run['producer']['path'] = foreign
        self.fx.save(inv)
        original_open, original_stat = Path.open, Path.stat

        def checked_open(path, *args, **kwargs):
            self.assertNotEqual(str(path), foreign, 'reader opened the historical producer')
            return original_open(path, *args, **kwargs)

        def checked_stat(path, *args, **kwargs):
            self.assertNotEqual(str(path), foreign, 'reader inspected the historical producer')
            return original_stat(path, *args, **kwargs)

        resolves = self.lake_resolver.call_count
        with mock.patch.object(Path, 'open', checked_open), mock.patch.object(Path, 'stat', checked_stat):
            self.assertEqual(ti.check(self.fx.root, write=True), [])
            self.assertEqual(self.fx.errors(), [])
            self.assertRunCurrent('all', True)
            self.assertRunCurrent('demo-0152', True)
            self.assertReplayRuns()
        self.assertEqual(self.lake_resolver.call_count, resolves)
        for mutation in ('missing', 'path', 'hash', 'bytes', 'pin'):
            bad = json.loads(json.dumps(inv['runs']['all']))
            if mutation == 'missing':
                del bad['producer']
            elif mutation == 'path':
                bad['producer']['path'] = '/other-host/bin/lake'
            elif mutation == 'hash':
                bad['producer']['sha256'] = 'not-a-digest'
            elif mutation == 'bytes':
                bad['producer']['bytes'] = True
            else:
                bad['lean_toolchain_sha256'] = '0' * 64
            with self.subTest(mutation=mutation), mock.patch.object(regen, 'ROOT', self.fx.root):
                self.assertFalse(regen.run_is_current(ti, bad))
                theorem = THEOREMS[0]
                self.assertIsNone(ti.current_result(self.fx.root, {'runs': {'bad': bad}}, theorem,
                    ti.translations(self.fx.root, 'demo')[0], ti.closure(self.fx.root, [theorem['module']])))
        proof = self.fx.root / 'Proofs/Demo/Proofs.lean'
        proof.write_text(proof.read_text() + '\n')
        calls = self.assertReplayRuns('all', 'demo-0152')
        for call in calls:
            self.assertEqual(ti.parse_build_command(self.fx.root, call.args[1], lake=str(self.fx.lake)).lake,
                             str(self.fx.lake))
            self.assertNotIn(foreign, call.args[1])

    def test_swap_build_executes_selected_lake_despite_shadowed_path(self):
        subprocess.run(['git', 'init', '-q', str(self.fx.root)], check=True)
        subprocess.run(['git', '-C', str(self.fx.root), 'add', '.'], check=True)
        with self.fx.fake_lake() as seen:
            self.fx.assert_main(['swap-build', '--lake', str(self.fx.lake), '--swap',
                                 'demo=tests/golden/0.15.2/demo/Gen.lean', 'Proofs.Demo.Proofs'])
            self.assertEqual(seen.read_bytes(), (self.fx.root / 'tests/golden/0.15.2/demo/Gen.lean').read_bytes())
            self.assertFalse((self.fx.root.parent / 'shadow-called').exists())
            with contextlib.redirect_stderr(io.StringIO()):
                self.fx.assert_main(['swap-build', '--lake', str(self.fx.root.parent / 'bin/lake'),
                                     'Proofs.Demo.Proofs'], code=1)
            self.assertFalse((self.fx.root.parent / 'shadow-called').exists())

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

    def test_completion_witness(self):
        ti.check(self.fx.root, write=True)
        table = (self.fx.root / ti.DOC).read_text()
        self.assertIn('| all-schedules (no run shown to complete) |', table)
        inv = self.fx.load()
        inv['theorems'][1]['completes'] = 'Conc.main_sc'
        self.fx.save(inv)
        self.assertFalse(any('completion witness' in e for e in self.fx.errors()))
        ti.check(self.fx.root, write=True)
        self.assertNotIn('no run shown to complete', (self.fx.root / ti.DOC).read_text())
        for witness, fragment in (('Demo.f_spec', 'is not a listed single- or bounded-schedule'),
                                  ('Conc.missing', 'is not a listed single- or bounded-schedule')):
            inv['theorems'][1]['completes'] = witness
            self.fx.save(inv)
            self.assertError(fragment)
        # A witness about another program does not count.
        inv['theorems'][1]['completes'] = 'Conc.main_sc'
        self.fx.save(inv)
        path = self.fx.root / 'Proofs/Conc/Proofs.lean'
        path.write_text(path.read_text().replace('(sched []) main mem0', '(sched []) other mem0'))
        self.assertError('does not show a completed `Sched.run` of the same program')

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
        report, log = self.fx.guard('demo', ['python3', str(self.fx.root / 'scripts/theorem-inventory.py'),
                                           'swap-build', '--swap', f'demo={swap}', '--', 'Proofs.Demo.Proofs'],
                                    f'{ti.SWAP_PREFIX}demo {swap} {"0" * 64}\n')
        self.fx.assert_main(['record', '--run', 'x', '--zig', '0.15.2', '--guard-report', str(report),
                             '--guard-log', str(log)], code=1)

    def test_record_rejects_a_translation_that_is_not_fresh(self):
        swap = 'tests/golden/0.15.2/demo/Gen.lean'
        (self.fx.root / 'scripts/STALE').write_text(swap + '\n')
        digest = hashlib.sha256((self.fx.root / swap).read_bytes()).hexdigest()
        report, log = self.fx.guard('demo', ['python3', str(self.fx.root / 'scripts/theorem-inventory.py'),
                                           'swap-build', '--swap', f'demo={swap}',
                                           '--', 'Proofs.Demo.Proofs'],
                                    f'{ti.SWAP_PREFIX}demo {swap} {digest}\n')
        self.fx.assert_main(['record', '--run', 'x', '--zig', '0.15.2', '--guard-report', str(report),
                             '--guard-log', str(log)], code=1)
        self.assertEqual(self.fx.load()['runs'], {})

    def test_swap_build_never_writes_the_committed_translation(self):
        subprocess.run(['git', 'init', '-q', str(self.fx.root)], check=True)
        subprocess.run(['git', '-C', str(self.fx.root), 'add', '.'], check=True)
        committed = (self.fx.root / 'Proofs/Demo/Gen.lean').read_text()
        with self.fx.fake_lake(exit_code=3) as seen:
            status = ti.main(['--root', str(self.fx.root), 'swap-build', '--swap',
                              'demo=tests/golden/0.15.2/demo/Gen.lean', '--', 'Proofs.Demo.Proofs'])
        self.assertEqual(status, 3)
        self.assertEqual(seen.read_text(), FILES['tests/golden/0.15.2/demo/Gen.lean'])
        self.assertEqual((self.fx.root / 'Proofs/Demo/Gen.lean').read_text(), committed)

    def test_swap_aliases_build_and_record_the_same_golden(self):
        subprocess.run(['git', 'init', '-q', str(self.fx.root)], check=True)
        subprocess.run(['git', '-C', str(self.fx.root), 'add', '.'], check=True)
        canonical = 'Proofs/Demo/Gen.lean'
        swap = 'tests/golden/0.15.2/demo/Gen.lean'
        committed = (self.fx.root / canonical).read_bytes()
        # Stub attestation must see the golden, not silently fall back to this file.
        (self.fx.root / 'scripts/STALE').write_text(canonical + '\n')
        for alias, source in (('demo', swap), ('DeMo', swap), ('Demo', './' + swap)):
            with self.subTest(alias=alias, source=source), self.fx.fake_lake() as seen:
                command = ['python3', str(self.fx.root / 'scripts/theorem-inventory.py'), 'swap-build',
                           '--swap', f'{alias}={source}', '--', 'Proofs.Demo.Proofs']
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    self.fx.assert_main(command[2:])
                self.assertEqual(seen.read_bytes(), (self.fx.root / swap).read_bytes())
                self.assertEqual((self.fx.root / canonical).read_bytes(), committed)
                digest = ti.sha256(self.fx.root / swap)
                self.assertEqual(output.getvalue(), f'{ti.SWAP_PREFIX}demo {swap} {digest}\n')
                for name, log_text in (
                        ('normalized', output.getvalue()),
                        ('legacy-alias', f'{ti.SWAP_PREFIX}{alias} {source} {digest}\n')):
                    self.fx.record(name, '0.15.2', *self.fx.guard(name, command, log_text))
                    self.assertEqual(self.fx.load()['runs'][name]['gens']['demo'],
                                     {'path': swap, 'sha256': digest})
                    self.assertRunCurrent(name, True)

        command = ['python3', str(self.fx.root / 'scripts/theorem-inventory.py'), 'swap-build', '--swap=Demo=' + canonical,
                   '--swap', 'dEmO=./' + swap, '--', 'Proofs.Demo.Proofs']
        output = io.StringIO()
        with self.fx.fake_lake() as seen, contextlib.redirect_stdout(output):
            self.fx.assert_main(command[2:])
        self.assertEqual(seen.read_bytes(), (self.fx.root / swap).read_bytes())
        self.assertEqual(output.getvalue(), f'{ti.SWAP_PREFIX}demo {swap} {ti.sha256(self.fx.root / swap)}\n')
        self.fx.record('last-swap', '0.15.2', *self.fx.guard('last-swap', command, output.getvalue()))
        self.assertEqual(self.fx.load()['runs']['last-swap']['gens']['demo']['path'], swap)
        self.assertRunCurrent('last-swap', True)

    def test_swap_parser_shares_argparse_abbreviations_targets_and_last_alias(self):
        subprocess.run(['git', 'init', '-q', str(self.fx.root)], check=True)
        subprocess.run(['git', '-C', str(self.fx.root), 'add', '.'], check=True)
        script = str(self.fx.root / 'scripts/theorem-inventory.py')
        swap = 'tests/golden/0.15.2/demo/Gen.lean'
        command = ['python3', '-B', '-u', script, '--root', '.', 'swap-build',
                   '--swap=Demo=Proofs/Demo/Gen.lean', '--swap',
                   'dEmO=./' + swap, '--', 'Proofs.Demo.Proofs']
        build = ti.parse_build_command(self.fx.root, command)
        self.assertEqual((build.modules, build.swaps), (['Proofs.Demo.Proofs'], {'demo': swap}))
        for option in ('--swap', '--sw', '--swa'):
            for args in ([option, 'Demo=./' + swap, 'Proofs.Demo.Proofs'],
                         [option + '=Demo=' + swap, '--', 'Proofs.Demo.Proofs'],
                         ['Proofs.Demo.Proofs', option, 'Demo=' + swap]):
                with self.subTest(args=args), self.fx.fake_lake() as seen:
                    command = ['python3', script, 'swap-build', *args]
                    build = ti.parse_build_command(self.fx.root, command)
                    self.assertEqual((build.modules, build.swaps), (['Proofs.Demo.Proofs'], {'demo': swap}))
                    output = io.StringIO()
                    with contextlib.redirect_stdout(output):
                        self.fx.assert_main(command[2:])
                    self.assertEqual(seen.read_bytes(), (self.fx.root / swap).read_bytes())
                    self.fx.record('abbreviation', '0.15.2',
                                   *self.fx.guard('abbreviation', command, output.getvalue()))
                    self.assertRunCurrent('abbreviation', True)
        for tail in (['--swap'], ['--swap=missing-equals', 'Proofs'], ['--unknown', 'Proofs'],
                     ['--', 'Proofs', '--swap', 'bad/path=outside']):
            with self.subTest(tail=tail), self.assertRaises(ti.Error):
                ti.parse_build_command(self.fx.root, ['python3', script, 'swap-build', *tail])

    def test_record_rejects_swap_log_command_identity_mismatch(self):
        command = ['python3', str(self.fx.root / 'scripts/theorem-inventory.py'), 'swap-build', '--swap',
                   'Demo=tests/golden/0.15.2/demo/Gen.lean', '--', 'Proofs.Demo.Proofs']
        canonical = 'Proofs/Demo/Gen.lean'
        log_text = f'{ti.SWAP_PREFIX}demo {canonical} {ti.sha256(self.fx.root / canonical)}\n'
        report, log = self.fx.guard('mismatched-swap', command, log_text)
        error = io.StringIO()
        with contextlib.redirect_stderr(error):
            self.fx.assert_main(['record', '--run', 'mismatched-swap', '--zig', '0.15.2',
                                 '--guard-report', str(report), '--guard-log', str(log)], code=1)
        self.assertIn('swap log identities differ', error.getvalue())
        self.assertEqual(self.fx.load()['runs'], {})

    def test_swap_examples_must_be_single_ascii_identifiers(self):
        source = 'tests/golden/0.15.2/demo/Gen.lean'
        for alias in ('demo.', 'demo/', 'demo\\', 'de mo', 'démó', 'demo:aux'):
            with self.subTest(alias=alias):
                self.assertSwapRejected(f'{alias}={source}', 'one ASCII identifier')

    def test_swap_paths_outside_relative_identity_are_rejected(self):
        for source in (str(self.fx.root / 'tests/golden/0.15.2/demo/Gen.lean'), '../outside.lean'):
            with self.subTest(source=source):
                self.assertSwapRejected(f'Demo={source}', 'repository-relative path')


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

    def test_f05_full_selector_theorem_is_listed_without_exclusion(self):
        inv = json.loads((ROOT / ti.INVENTORY).read_text())
        full = next(t for t in inv['theorems'] if t['name'] == 'op128_spec_full')
        self.assertIn('every selector', full['domain'])
        statement = ti.declarations((ROOT / 'Proofs/Floatops/Proofs.lean').read_text())['op128_spec_full']
        self.assertNotIn('≠', statement['statement'])
        self.assertIn('opSpec128 floatopsTarget op128Profile sel', statement['statement'])

    def test_f05_profile_follows_the_version(self):
        # `op128Profile` elaborates either profile, so pin which one each version's `op128` selects:
        # 0.16.0 (the committed Gen) gives `v016`, the 0.14.1/0.15.2 goldens give `legacy`.
        def op128(path):
            text = (ROOT / path).read_text()
            start = text.index('\ndef op128 ')
            end = text.find('\ndef ', start + 1)
            return text[start:end if end >= 0 else len(text)]
        v016 = op128('Proofs/Floatops/Gen.lean')
        self.assertIn('Zig.Float.divRt016', v016)
        self.assertNotIn('sqrtF128ViaF64', v016)
        for version in ('0.14.1', '0.15.2'):
            legacy = op128(f'tests/golden/{version}/floatops/Gen.lean')
            self.assertIn('Zig.Float.sqrtF128ViaF64', legacy, version)
            self.assertNotIn('Rt016', legacy, version)


if __name__ == '__main__':
    unittest.main()
