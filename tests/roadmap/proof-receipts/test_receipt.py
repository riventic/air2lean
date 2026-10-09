#!/usr/bin/env python3
"""Offline receipt regressions. All compiler/auditor execution is mocked."""
import rss_budget
START_RSS = rss_budget.baseline()  # bare-interpreter peak; the suite's imports count as growth
import copy
import gc
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import types
import unittest

# Small reversible patches avoid unittest.mock's asyncio import in this 32 MiB suite.
_UNSET = object()


class Probe:
    def __init__(self, effect=None):
        self.effect, self.calls = effect, 0

    def __call__(self, *args, **kwargs):
        self.calls += 1
        if isinstance(self.effect, type) and issubclass(self.effect, BaseException):
            raise self.effect()
        if self.effect is not None:
            return self.effect(*args, **kwargs)

    def assert_not_called(self):
        if self.calls:
            raise AssertionError('mock execution unexpectedly called')


class Patch:
    def __init__(self, target, name=None, value=_UNSET, side_effect=None, clear=False):
        self.target, self.name, self.clear = target, name, clear
        self.value = Probe(side_effect) if value is _UNSET else value

    def start(self):
        if self.name is None:
            self.saved = dict(self.target)
            if self.clear:
                self.target.clear()
            self.target.update(self.value)
        else:
            self.saved = getattr(self.target, self.name)
            setattr(self.target, self.name, self.value)
        return self.value

    def stop(self):
        if self.name is None:
            self.target.clear()
            self.target.update(self.saved)
        else:
            setattr(self.target, self.name, self.saved)

    __enter__ = start

    def __exit__(self, *unused):
        self.stop()


mock = types.SimpleNamespace(patch=types.SimpleNamespace(
    object=Patch, dict=lambda target, value, clear=False: Patch(target, value=value, clear=clear)))

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('proof_receipt', ROOT / 'scripts/proof-receipt.py')
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)


class ReceiptTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.base = Path(self.temporary.name).resolve()
        self.root, self.attempt, self.tc = [self.base / n for n in ('repo', 'attempt', 'toolchain')]
        self.root.mkdir()
        self.attempt.mkdir()
        self.names = []
        for name in ('scripts/assumptions.py', 'scripts/normalize-generated.py', 'scripts/build-guard.py',
                     'scripts/proof-receipt.py', 'tests/roadmap/proof-receipts/check.sh', 'assurance/policy.json',
                     'tools/Assurance.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
                     'zig-patch/versions.toml', 'assurance/float-semantics.json', 'scripts/float-semantics.py'):
            self.source(name, (ROOT / name).read_bytes())
        self.source('ZigLean.lean', b'import ZigLean.Basic\n')
        self.source('ZigLean/Basic.lean', b'def trivial := 0\n')
        self.source('Proofs/One.lean', b'import Proofs.One.Gen\ntheorem checked : True := True.intro\n')
        self.source('Proofs/One/Gen.lean', b'namespace Example\ndef generated := 0\nend Example\n')
        self.names.sort()
        self.put(self.tc / 'bin/lean', b'mock compiler bytes; never executed')
        self.put(self.tc / 'bin/lake', b'mock build bytes; never executed')
        self.put(self.tc / 'bin/ps', b'mock observer bytes; never executed')
        (self.tc / 'bin/ps').chmod(0o700)
        self.put(self.tc / 'lib/lean/Init.olean', b'mock imported kernel artifact')
        self.lock = self.base / 'lock'
        self.lock.write_text('')
        self.patchroot = mock.patch.object(r, 'ROOT', self.root)
        self.patchroot.start()
        self.patchgit = mock.patch.object(r, 'git', side_effect=self.git)
        self.patchgit.start()
        self.patchenv = mock.patch.dict(os.environ, {'PATH': str(self.tc / 'bin'), 'LEAN_NUM_THREADS': '1'}, clear=True)
        self.patchenv.start()
        self.plan = {'schema': 1, 'root': str(self.root), 'attempt': str(self.attempt), 'toolchain': str(self.tc),
                     'profile': 'mock-selected-generated-state', 'lock': str(self.lock), 'modules': ['Proofs.One'],
                     'scope': 'explicit-modules', 'python': str(Path(sys.executable).resolve()),
                     'revision': r.revision(), 'sources': r.source_inventory(self.names),
                     'guard': r.fingerprint(self.root / 'scripts/build-guard.py')}
        self.write('plan.json', self.plan)
        self.make_audit()
        self.before = r.context(self.plan)
        self.write('before.json', self.before)
        self.after = {'context': self.before, 'compiled': r.compiled(self.plan), 'profiles': r.profiles()}
        self.write('after.json', self.after)
        self.guard = self.good_guard()
        self.write('guard.json', self.guard)

    def tearDown(self):
        self.patchenv.stop()
        self.patchgit.stop()
        self.patchroot.stop()
        self.temporary.cleanup()
        gc.collect()

    def source(self, name, data):
        self.put(self.root / name, data)
        self.names.append(name)

    def put(self, path, data):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)

    def git(self, *args):
        if args == ('rev-parse', 'HEAD'):
            return b'0123456789abcdef0123456789abcdef01234567\n'
        if args == ('status', '--porcelain', '--untracked-files=no'):
            return b''
        if args == ('ls-files', '-z'):
            return ('\0'.join(self.names) + '\0').encode()
        if args == ('ls-files', '--others', '--exclude-standard', '-z'):
            return b''
        self.fail('unexpected Git invocation: ' + str(args))

    def write(self, name, value):
        (self.attempt / name).write_text(json.dumps(value))

    def make_audit(self):
        own = self.root / '.lake/build/lib/lean'
        for module in ('Proofs.One', 'tools.Assurance'):
            base = own / module.replace('.', '/')
            self.put(base.with_suffix('.olean'), b'checked artifact ' + module.encode())
            self.put(base.with_suffix('.trace'), b'Lake trace ' + module.encode())
        auditor = r.helper('assumptions')
        raw = {'schema_version': 1, 'modules': ['Proofs.One'], 'project_declarations': [],
               'nodes': [{'name': 'Example.checked', 'module': 'Proofs.One', 'kind': 'theorem',
                          'dependencies': [], 'unsafe': False}],
               'theorems': [{'name': 'Example.checked', 'module': 'Proofs.One', 'axioms': []}]}
        audit = auditor.apply_policy(raw, auditor.load_policy(self.root / 'assurance/policy.json'))
        audit.update(scope='explicit-modules', build_checked=True,
                     policy_sha256=r.fingerprint(self.root / 'assurance/policy.json')['sha256'],
                     lean_toolchain=(self.root / 'lean-toolchain').read_text().strip())
        audit['extractor'] = {'source_sha256': r.fingerprint(self.root / 'tools/Assurance.lean')['sha256'],
              'olean_sha256': r.fingerprint(own / 'tools/Assurance.olean')['sha256'],
              'lake_trace_sha256': r.fingerprint(own / 'tools/Assurance.trace')['sha256'],
              'lean_toolchain_sha256': r.fingerprint(self.root / 'lean-toolchain')['sha256'],
              'lake_config_sha256': r.fingerprint(self.root / 'lakefile.toml')['sha256']}
        self.write('audit.json', audit)

    def good_guard(self):
        (self.attempt / 'guard.log').write_text('mock actual-audit summary\n')
        command = [self.plan['python'], str(self.root / 'scripts/proof-receipt.py'), 'worker', str(self.attempt)]
        log = r.fingerprint(self.attempt / 'guard.log')
        return {'schema': 1, 'outcome': 'success', 'exit_code': 0, 'child_status': 0,
                'log_truncated': False, 'drain_incomplete': False, 'cwd': str(self.root),
                'requested_command': command, 'command': command, 'profile': self.plan['profile'],
                'phase': 'proof', 'lock': str(self.lock), 'revision': self.before['revision'],
                'environment_overrides': {'LEAN_NUM_THREADS': '1'},
                'inputs': [r.fingerprint(self.attempt / 'plan.json')] + [r.fingerprint(self.root / p) for p in r.INPUTS] + [self.plan['guard']],
                'outputs': [r.fingerprint(self.attempt / p) for p in r.OUTPUTS],
                'pins': [r.fingerprint(self.root / p) for p in ('lean-toolchain', 'zig-patch/versions.toml')],
                'guard': self.plan['guard'], 'tools': [r.fingerprint(p) for p in
                  (self.plan['python'], self.plan['python'], self.tc / 'bin/ps', self.tc / 'bin/lean', self.tc / 'bin/lake')],
                'log': log['path'], 'log_sha256': log['sha256'], 'log_bytes': log['bytes']}

    def refresh_guard(self):
        self.guard = self.good_guard()
        self.write('guard.json', self.guard)

    def rejected(self):
        with self.assertRaises((ValueError, KeyError, TypeError, OSError)):
            r.seal(self.attempt)
        self.assertFalse((self.attempt / 'receipt.json').exists())

    def test_current_receipt_and_no_clobber(self):
        r.seal(self.attempt)
        original = (self.attempt / 'receipt.json').read_bytes()
        self.assertEqual(r.verify(self.attempt)['status'], 'current')
        with self.assertRaises(FileExistsError):
            r.seal(self.attempt)
        self.assertEqual((self.attempt / 'receipt.json').read_bytes(), original)
        self.assertEqual(r.verify(self.attempt)['checking'], 'not_rerun')

    def test_guard_failure_and_cleanup_classes(self):
        for outcome in ('child_failed', 'timeout', 'cancelled', 'cleanup_failed', 'lock_busy', 'rss_limit'):
            with self.subTest(outcome=outcome):
                self.write('guard.json', dict(self.guard, outcome=outcome))
                self.rejected()

    def test_exact_guard_argv_context_and_status(self):
        for key, value in [('command', ['true']), ('requested_command', ['true']), ('cwd', '/tmp'),
                           ('profile', 'another'), ('phase', 'build'), ('lock', '/tmp/another'),
                           ('exit_code', 1), ('child_status', -15), ('log_truncated', True),
                           ('drain_incomplete', True), ('revision', {'head': 'another', 'tracked_dirty': False}),
                           ('environment_overrides', {})]:
            with self.subTest(key=key):
                self.write('guard.json', dict(self.guard, **{key: value}))
                self.rejected()

    def test_guard_identity_and_log_binding(self):
        for key in ('inputs', 'outputs', 'pins', 'tools'):
            with self.subTest(key=key):
                bad = copy.deepcopy(self.guard)
                bad[key][0]['sha256'] = '0' * 64
                self.write('guard.json', bad)
                self.rejected()
        self.write('guard.json', self.guard)
        (self.attempt / 'guard.log').write_text('different log')
        self.rejected()

    def test_unsafe_audit_graph_cannot_seal(self):
        audit = r.load(self.attempt / 'audit.json')
        cases = [('status', 'fail'), ('scope', 'all-shipped-modules'), ('build_checked', False),
                 ('modules', ['ZigLean']), ('theorems', []), ('theorem_count', 0)]
        for key, value in cases:
            with self.subTest(key=key):
                self.write('audit.json', dict(audit, **{key: value}))
                self.refresh_guard()
                self.rejected()
        hidden = copy.deepcopy(audit)
        hidden['nodes'][0]['dependencies'] = ['sorryAx']
        hidden['nodes'].append({'name': 'sorryAx', 'module': 'Init', 'kind': 'axiom', 'dependencies': []})
        hidden['theorems'][0]['axioms'] = ['sorryAx']
        self.write('audit.json', hidden)
        self.refresh_guard()
        self.rejected()

    def test_missing_and_additional_selected_modules(self):
        missing = dict(self.plan, modules=['Missing'])
        diagnostic = '^selected module source is not tracked$'
        with self.assertRaisesRegex(ValueError, diagnostic):
            r.context(missing)
        self.write('plan.json', dict(self.plan, modules=['Proofs.One', 'ZigLean'], scope='all-shipped-modules'))
        with self.assertRaisesRegex(ValueError, '^shipped inventory changed$'):
            r.plan_for(self.attempt)
        original = r.demand
        def bypass_selected_source(ok, message):
            if message != 'selected module source is not tracked':
                original(ok, message)
        with mock.patch.object(r, 'demand', bypass_selected_source):
            # Removing this guard must fail the exact oracle, without a later rejection.
            with self.assertRaises(AssertionError):
                with self.assertRaisesRegex(ValueError, diagnostic):
                    r.context(missing)

    def test_missing_selected_artifact_and_trace(self):
        own = self.root / '.lake/build/lib/lean/Proofs/One'
        for suffix in ('.olean', '.trace'):
            path = own.with_suffix(suffix)
            original = path.read_bytes()
            path.unlink()
            self.rejected()
            path.write_bytes(original)

    def test_mutable_source_runtime_policy_and_tool_context(self):
        paths = ['Proofs/One.lean', 'Proofs/One/Gen.lean', 'ZigLean/Basic.lean',
                 'assurance/policy.json', 'lean-toolchain', 'lakefile.toml']
        for name in paths:
            with self.subTest(name=name):
                path = self.root / name
                original = path.read_bytes()
                path.write_bytes(original + b'\nchanged')
                self.rejected()
                path.write_bytes(original)
        (self.tc / 'bin/lean').write_text('changed compiler')
        self.rejected()

    def test_library_and_compiled_closure_changes(self):
        r.seal(self.attempt)
        for path in (self.tc / 'lib/lean/New.olean', self.root / '.lake/build/lib/lean/Extra.olean'):
            path.write_text('new unseen artifact')
            with self.assertRaises(ValueError):
                r.verify(self.attempt)
            path.unlink()
        (self.root / '.lake/build/lib/lean/Proofs/One.olean').write_text('changed compiled theorem')
        with self.assertRaises(ValueError):
            r.verify(self.attempt)

    def test_environment_and_module_overlay_rejection(self):
        for name in (*r.OVERLAYS, 'LEAN_NEW_OVERLAY', 'LAKE_NEW_OVERLAY'):
            with mock.patch.dict(os.environ, {name: '/another'}), self.assertRaises(ValueError):
                r.context(self.plan)
        (self.root / 'lakefile.lean').write_text('import Lake')
        with self.assertRaises(ValueError):
            r.context(self.plan)
        (self.root / 'lakefile.lean').unlink()
        self.put(self.root / '.lake/build/lib/lean/Std/Shadow.olean', b'shadow')
        self.rejected()

    def test_regular_files_and_no_symlink_paths(self):
        alias = self.base / 'alias'
        alias.symlink_to(self.tc, target_is_directory=True)
        with self.assertRaises(ValueError):
            r.context(dict(self.plan, toolchain=str(alias)))
        fifo = self.base / 'fifo'
        os.mkfifo(fifo)
        with self.assertRaises(ValueError):
            r.fingerprint(fifo)

    def test_json_duplicate_depth_and_numeric_bounds(self):
        for raw in (b'{"status":"pass","status":"fail"}', b'[' * 65 + b']' * 65,
                    b'{"number":' + b'9' * 25 + b'}', b'{"x":NaN}', b'{"x":1e999}'):
            with self.subTest(raw=raw[:30]), self.assertRaises(ValueError):
                r.parse_json(raw)

    def test_incomplete_attempt_and_interrupted_publication(self):
        with self.assertRaises(FileNotFoundError):
            r.verify(self.attempt)
        with mock.patch.object(r.os, 'link', side_effect=KeyboardInterrupt), self.assertRaises(KeyboardInterrupt):
            r.seal(self.attempt)
        self.assertFalse((self.attempt / 'receipt.json').exists())
        self.assertEqual(sorted(p.name for p in self.attempt.iterdir()),
                         ['after.json', 'audit.json', 'before.json', 'guard.json', 'guard.log', 'plan.json'])

    def test_historical_profile_is_not_relabelled(self):
        self.assertEqual(self.after['profiles']['Proofs/One/Gen.lean']['scope'], 'legacy-or-unannotated')
        self.assertIsNone(self.after['profiles']['Proofs/One/Gen.lean']['metadata'])
        r.seal(self.attempt)
        receipt = r.load(self.attempt / 'receipt.json')
        self.assertEqual(receipt['source_correspondence'], 'not_attested')
        self.assertEqual(receipt['native_adequacy'], 'not_attested')

    def test_float_semantics_labels_are_carried_and_binary_claims_rejected(self):
        audit = r.load(self.attempt / 'audit.json')
        self.assertEqual(audit['float_semantics']['binary_correspondence'], 'not_claimed')
        tampered = copy.deepcopy(audit)
        tampered['theorems'][0]['float_semantics'] = {'scope': 'stated', 'label': 'ieee',
                                                      'binary_correspondence': 'claimed'}
        tampered['float_semantics']['binary_correspondence'] = 'claimed'
        self.write('audit.json', tampered)
        self.refresh_guard()
        self.rejected()
        self.write('audit.json', audit)
        self.refresh_guard()
        r.seal(self.attempt)
        receipt = r.load(self.attempt / 'receipt.json')
        self.assertEqual(receipt['schema'], 2)
        self.assertEqual(receipt['float_semantics'], dict(audit['float_semantics'], theorems={}))
        self.assertEqual(r.helper('float-semantics').report_problems(receipt, root=self.root), [])
        claimed = dict(receipt, float_semantics=dict(receipt['float_semantics'], binary_correspondence='claimed'))
        (self.attempt / 'receipt.json').write_text(json.dumps(claimed))
        with self.assertRaisesRegex(ValueError, 'float-semantics'):
            r.verify(self.attempt)

    def test_prepare_is_fresh_scoped_and_does_not_execute_tools(self):
        fresh = self.base / 'fresh'
        arguments = ['proof-receipt.py', 'prepare', str(fresh), '--toolchain', str(self.tc),
                     '--profile', 'original-label', '--module', 'Proofs.One', '--lock', str(self.lock)]
        with mock.patch.object(r.sys, 'argv', arguments):
            self.assertEqual(r.main(), 0)
        plan = r.load(fresh / 'plan.json')
        self.assertEqual(plan['modules'], ['Proofs.One'])
        self.assertEqual(plan['sources'], self.plan['sources'])
        self.assertEqual(sorted(p.name for p in fresh.iterdir()), ['plan.json'])
        with mock.patch.object(r.sys, 'argv', arguments):
            self.assertEqual(r.main(), 2)
        self.assertEqual(r.load(fresh / 'plan.json'), plan)

    def test_extra_tracked_source_and_unavailable_pins_cannot_seal(self):
        self.source('New.lean', b'new tracked source')
        self.names.sort()
        self.rejected()
        self.names.remove('New.lean')
        bad = copy.deepcopy(self.guard)
        bad['pins'][0] = {'path': str(self.root / 'lean-toolchain'), 'unavailable': True}
        self.write('guard.json', bad)
        self.rejected()

    def test_worker_requires_guard_lock_and_exact_tool_path(self):
        with mock.patch.object(r.fcntl, 'flock', lambda *args: None), self.assertRaises(ValueError):
            r.worker(self.attempt)
        with mock.patch.object(r.fcntl, 'flock', side_effect=BlockingIOError), \
             mock.patch.dict(os.environ, {'PATH': '/other/bin'}), self.assertRaises(ValueError):
            r.worker(self.attempt)

    def test_external_guard_requires_pin_and_remains_bound(self):
        external = self.base / 'reviewed-guard.py'
        external.write_text('reviewed fixture guard; never executed')
        fresh = self.base / 'external-attempt'
        args = ['proof-receipt.py', 'prepare', str(fresh), '--toolchain', str(self.tc),
                '--profile', 'reviewed', '--module', 'Proofs.One', '--lock', str(self.lock), '--guard', str(external)]
        with mock.patch.object(r.sys, 'argv', args):
            self.assertEqual(r.main(), 2)
        self.assertFalse(fresh.exists())
        pin = r.fingerprint(external)['sha256']
        with mock.patch.object(r.sys, 'argv', args + ['--guard-sha256', pin]):
            self.assertEqual(r.main(), 0)
        self.assertEqual(r.load(fresh / 'plan.json')['guard']['sha256'], pin)
        external.write_text('changed reviewed guard')
        with self.assertRaises(ValueError):
            r.plan_for(fresh)

    def test_worker_only_mock_auditor_no_no_build(self):
        (self.attempt / 'before.json').unlink()
        (self.attempt / 'after.json').unlink()
        calls = []
        def runner(argv, cwd):
            calls.append(argv)
            self.assertEqual(cwd, self.root)
            self.assertNotIn('--no-build', argv)
            self.assertEqual(argv[-2:], ['--module', 'Proofs.One'])
            return types.SimpleNamespace(returncode=0)
        with mock.patch.object(r.fcntl, 'flock', side_effect=BlockingIOError), \
             mock.patch.object(r, 'run_child', side_effect=runner):
            self.assertEqual(r.worker(self.attempt), 0)
        self.assertEqual(len(calls), 1)

    def test_worker_detects_changed_source_before_and_during_audit(self):
        (self.attempt / 'before.json').unlink()
        (self.attempt / 'after.json').unlink()
        source = self.root / 'Proofs/One.lean'
        old = source.read_bytes()
        source.write_bytes(old + b'changed')
        with mock.patch.object(r.fcntl, 'flock', side_effect=BlockingIOError), \
             mock.patch.object(r, 'run_child') as run, self.assertRaises(ValueError):
            r.worker(self.attempt)
        run.assert_not_called()
        source.write_bytes(old)
        def change(argv, cwd):
            source.write_bytes(old + b'changed during audit')
            return types.SimpleNamespace(returncode=0)
        with mock.patch.object(r.fcntl, 'flock', side_effect=BlockingIOError), \
             mock.patch.object(r, 'run_child', side_effect=change), self.assertRaises(ValueError):
            r.worker(self.attempt)
        self.assertFalse((self.attempt / 'after.json').exists())

    def test_tracked_relative_source_alias_and_profile_drift(self):
        alias = self.root / 'Aliases/Gen.lean'
        alias.parent.mkdir()
        alias.symlink_to('../Proofs/One/Gen.lean')
        self.names.append('Aliases/Gen.lean')
        self.names.sort()
        rows = r.source_inventory(self.names)
        row = next(row for row in rows if row['path'] == str(alias))
        self.assertEqual((row['kind'], row['link']), ('symlink', '../Proofs/One/Gen.lean'))
        self.assertEqual(row['target'], r.fingerprint(self.root / 'Proofs/One/Gen.lean'))
        self.assertEqual(r.profiles()['Aliases/Gen.lean'], r.profiles()['Proofs/One/Gen.lean'])
        self.plan['sources'] = rows
        self.write('plan.json', self.plan)
        self.before = r.context(self.plan)
        self.write('before.json', self.before)
        self.write('after.json', {'context': self.before, 'compiled': r.compiled(self.plan), 'profiles': r.profiles()})
        self.refresh_guard()
        r.seal(self.attempt)
        self.assertEqual(r.verify(self.attempt)['status'], 'current')
        target = self.root / 'Proofs/One/Gen.lean'
        original = target.read_bytes()
        target.write_bytes(original + b'changed target')
        with self.assertRaises(ValueError): r.verify(self.attempt)
        target.write_bytes(original)
        alias.unlink()
        alias.symlink_to('../Proofs/One/../One/Gen.lean')  # Same content, different literal link.
        with self.assertRaises(ValueError):
            r.verify(self.attempt)

    def test_source_alias_rejects_external_untracked_chain_and_nonregular_targets(self):
        alias, target = self.root / 'Alias.lean', self.root / 'Target.lean'
        self.names.append('Alias.lean')
        self.names.sort()
        self.put(target, b'tiny target')
        for link in (str(target), 'Target.lean', '../outside.lean'):
            alias.symlink_to(link)
            with self.assertRaises(ValueError):
                r.source_inventory(self.names)
            alias.unlink()
        self.names.append('Target.lean')
        self.names.sort()
        target.unlink()
        target.symlink_to('Proofs/One/Gen.lean')
        alias.symlink_to('Target.lean')
        with self.assertRaises(ValueError):
            r.source_inventory(self.names)
        target.unlink()
        os.mkfifo(target)
        with self.assertRaises(ValueError):
            r.source_inventory(self.names)

    def test_inventory_running_budget_and_late_invalid_file(self):
        a, b = self.base / 'a', self.base / 'b'
        a.write_bytes(b'123')
        b.write_bytes(b'45678')
        calls, real = [], r.fingerprint
        def count(path, allowance=None):
            calls.append((Path(path).name, allowance))
            return real(path, allowance)
        with mock.patch.object(r, 'MAX_TOTAL', 7), mock.patch.object(r, 'fingerprint', count):
            with self.assertRaises(ValueError):
                r.inventory([b, a])
        self.assertEqual(calls, [('a', 7), ('b', 4)])
        with mock.patch.object(r, 'MAX_FILE', 4), self.assertRaises(ValueError):
            r.inventory([a, b])
        b.write_bytes(b'4567')
        with mock.patch.object(r, 'MAX_TOTAL', 7):
            self.assertEqual(sum(row['bytes'] for row in r.inventory([b, a])), 7)
            b.unlink()
            os.mkfifo(b)
            with self.assertRaises(ValueError):
                r.inventory([a, b])

    def test_stream_reads_stop_at_remaining_plus_one_and_detect_short_file(self):
        path = self.base / 'stream'
        path.write_bytes(b'not read by fake stream')
        real_fdopen, reads = r.os.fdopen, []
        class Stream:
            def __init__(self, fd, data):
                self.file, self.data = real_fdopen(fd, 'rb'), data
            def __enter__(self): return self
            def __exit__(self, *args): self.file.close()
            def fileno(self): return self.file.fileno()
            def read(self, count):
                chunk, self.data = self.data[:count], self.data[count:]
                reads.append((count, len(chunk)))
                return chunk
        for size, data, allowance in ((0, b'12345678', 5), (8, b'12', 8)):
            stat = types.SimpleNamespace(st_mode=r.stat.S_IFREG | 0o600, st_size=size,
                                        st_mtime_ns=1, st_ctime_ns=1)
            with mock.patch.object(r.os, 'fdopen', lambda fd, mode: Stream(fd, data)), \
                 mock.patch.object(r.os, 'fstat', lambda fd: stat), self.assertRaises(ValueError):
                r.fingerprint(path, allowance)
        self.assertEqual(reads, [(6, 6), (9, 2), (7, 0)])

    def test_malformed_mapping_boundaries_exit_two_without_publication(self):
        audit = r.load(self.attempt / 'audit.json')
        cases = [('plan.json', []), ('plan.json', dict(self.plan, guard=None)),
                 ('before.json', []), ('after.json', []), ('guard.json', []),
                 ('guard.json', dict(self.guard, environment_overrides=None)),
                 ('guard.json', dict(self.guard, environment_overrides=[])),
                 ('audit.json', []), ('audit.json', dict(audit, extractor=[])),
                 ('audit.json', dict(audit, nodes=[[]])), ('audit.json', dict(audit, theorems=[None]))]
        originals = {name: (self.attempt / name).read_bytes() for name in ('plan.json', 'before.json', 'after.json', 'guard.json', 'audit.json')}
        for name, value in cases:
            self.write(name, value)
            if name != 'guard.json': self.refresh_guard()
            messages = []
            sink = types.SimpleNamespace(write=lambda message: messages.append(message), flush=lambda: None)
            with mock.patch.object(r.sys, 'argv', ['receipt', 'seal', str(self.attempt)]), \
                 mock.patch.object(r.sys, 'stderr', sink):
                self.assertEqual(r.main(), 2)
            self.assertNotIn('Traceback', ''.join(messages))
            self.assertFalse((self.attempt / 'receipt.json').exists())
            for restore, raw in originals.items(): (self.attempt / restore).write_bytes(raw)
        manifest = self.root / 'lake-manifest.json'
        manifest.write_text('[]')
        with self.assertRaises(ValueError): r.context(self.plan)

    def test_audit_module_checks_cache_success_locally_and_reset(self):
        audit = r.load(self.attempt / 'audit.json')
        audit['nodes'] += [dict(audit['nodes'][0], name='Example.extra' + str(i), kind='definition') for i in range(20)]
        auditor = r.helper('assumptions')
        audit.update(auditor.apply_policy(audit, auditor.load_policy(self.root / 'assurance/policy.json')))
        actual, calls = r.Path.is_file, []
        def observed(path):
            calls.append(str(path))
            return actual(path)
        with mock.patch.object(r.Path, 'is_file', observed):
            r.audit_ok(self.plan, audit)
            r.audit_ok(self.plan, audit)
        self.assertEqual(calls, [str(self.root / '.lake/build/lib/lean/Proofs/One.olean')] * 2)
        audit['nodes'][-1]['module'] = []
        with self.assertRaises(ValueError): r.audit_ok(self.plan, audit)
        audit['nodes'][-1]['module'] = 'Missing'
        audit.update(auditor.apply_policy(audit, auditor.load_policy(self.root / 'assurance/policy.json')))
        with mock.patch.object(r.Path, 'is_file', observed), self.assertRaises(ValueError):
            r.audit_ok(self.plan, audit)
        self.assertIn(str(self.tc / 'lib/lean/Missing.olean'), calls)

    def test_declaration_budget_is_independent_of_file_budget(self):
        self.assertEqual((r.MAX_FILES, r.MAX_DECLARATIONS), (30000, 65536))
        audit = r.load(self.attempt / 'audit.json')
        node = audit['nodes'][0]
        diagnostic = '^declaration entry must be a JSON object$'
        audit['nodes'] = [node] * 65537
        with self.assertRaisesRegex(ValueError, '^invalid declaration graph$'): r.audit_ok(self.plan, audit)
        for count in (65536, 30930, 30001):
            del audit['nodes'][count:]  # Reuse one allocation within the 32 MiB offline budget.
            audit['nodes'][-1] = None
            with self.assertRaisesRegex(ValueError, diagnostic): r.audit_ok(self.plan, audit)
            audit['nodes'][-1] = node
        audit['nodes'][-1] = None
        with mock.patch.object(r, 'MAX_DECLARATIONS', r.MAX_FILES), self.assertRaises(AssertionError):
            with self.assertRaisesRegex(ValueError, diagnostic): r.audit_ok(self.plan, audit)
        audit['nodes'].clear()
        with self.assertRaisesRegex(ValueError, '^file inventory exceeds bound$'):
            r.inventory([self.root / 'lean-toolchain'] * 30001)
        audit = r.load(self.attempt / 'audit.json')
        audit['nodes'] += [dict(node, name='Example.budget' + str(i), kind='definition') for i in range(2)]
        auditor = r.helper('assumptions')
        audit.update(auditor.apply_policy(audit, auditor.load_policy(self.root / 'assurance/policy.json')))
        with mock.patch.object(r, 'MAX_FILES', 2), mock.patch.object(r, 'MAX_DECLARATIONS', 3):
            r.audit_ok(self.plan, audit)  # Distinct small graph passes the complete policy/artifact validator.


if __name__ == '__main__':
    result = unittest.main(exit=False).result
    rss_budget.enforce(START_RSS)
    if not result.wasSuccessful():
        raise SystemExit(1)
