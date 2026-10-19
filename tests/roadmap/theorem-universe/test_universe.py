#!/usr/bin/env python3
"""Offline regressions for the theorem universe (F2), kernel replay (S1) and freshness (H1).

No Lean, Lake or Zig: Lean and leanchecker are replaced by small scripts. The compiled audit
itself runs in CI (`theorem_universe.py audit`) and in tests/roadmap/architecture-audit/claims.
"""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / filename)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module  # dataclasses resolve their defining module
    spec.loader.exec_module(module)
    return module


universe = load('theorem_universe', 'theorem_universe.py')
assumptions = load('assumptions', 'assumptions.py')
premises = load('premises', 'premises.py')


def installed_inputs(root):
    """Synthetic installed inputs; the tests never invoke Lean or Lake."""
    (root / 'bin').mkdir(parents=True)
    for name in ('lean', 'leanchecker'):
        (root / 'bin' / name).write_bytes(name.encode())
    (root / 'lib/lean').mkdir(parents=True)
    for name in ('lib/libleanshared.so', 'lib/lean/Init.olean', 'lib/lean/Init.ir.sig'):
        (root / name).write_bytes(b'original')


class UniverseTests(unittest.TestCase):
    def test_every_indexed_theorem_file_is_audited(self):
        shipped, units = universe.universe()
        self.assertEqual(shipped, assumptions.shipped_modules())
        config = premises.load_config(ROOT / premises.CONFIG)
        indexed = {f.rel for f in premises.theorem_files(premises.load_repository(ROOT, config))}
        audited = {u.file for u in units} | {m.replace('.', '/') + '.lean' for m in shipped}
        self.assertEqual(indexed - audited, set())
        self.assertTrue({'tutorials/first-proof/Main.lean', 'tests/roadmap/vcs/Result.lean',
                         'case-studies/flow-time/FlowTime/Proofs.lean'} <= audited)
        gated = {u.file: u.gate for u in units if u.gate}
        # A file that imports a gated file inherits its gate (`gate_of`), as the strength log of
        # a gated proof does (tests/roadmap/strength-log/DispatchTemplates.lean).
        self.assertEqual({f: g for f, g in gated.items() if f in universe.GATES}, universe.GATES)
        by_file = {u.file: u for u in units}
        for rel, gate in gated.items():
            if rel not in universe.GATES:
                self.assertIn(gate, {gated[d] for d in by_file[rel].deps if d in gated}, rel)

    def test_witness_fixtures_are_registered_universe_files(self):
        # The shipped audit loads them (assurance/witness-fixtures.json): ungated universe units.
        files = assumptions.witness_fixtures()
        self.assertIn('tests/roadmap/lists-fba/ListsFba/Witness.lean', files)
        units = {u.file: u for u in universe.universe()[1]}
        for rel in files:
            self.assertIsNone(units[rel].gate, rel)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'assurance').mkdir()
            for entries, error in (([{'file': 'Proofs/X.lean', 'reason': 'r'}], 'not a test source'),
                                   ([{'file': 'tests/missing.lean', 'reason': 'r'}], 'not a test source'),
                                   ([{'file': 'tests/a.lean'}], 'file, reason')):
                (root / 'assurance/witness-fixtures.json').write_text(
                    json.dumps({'description': 'd', 'fixtures': entries}))
                with self.assertRaisesRegex(ValueError, error):
                    assumptions.witness_fixtures(root)

    def test_witness_theorems_leave_the_audit_scope(self):
        report = {'modules': ['A', 'W'], 'theorem_count': 2,
                  'theorems': [{'name': 'a', 'module': 'A'}, {'name': 'a.nonvacuous', 'module': 'W'}]}
        assumptions.split_witnesses(report, ['A'], ['W'])
        self.assertEqual((report['modules'], report['witness_modules'], report['theorem_count']), (['A'], ['W'], 1))
        self.assertEqual([t['name'] for t in report['witness_theorems']], ['a.nonvacuous'])

    def test_reserved_or_invalid_module_names_are_staged(self):
        units = {u.file: u for u in universe.universe()[1]}
        for rel in ('tests/roadmap/dispatch/Proofs.lean', 'tests/roadmap/local-parent/Proofs.lean'):
            self.assertIsNone(units[rel].root)
            self.assertTrue(units[rel].module.startswith('Universe.'))
        self.assertEqual(units['tests/roadmap/idle-loops/IdleLoop/Gen.lean'].module, 'IdleLoop.Gen')

    def test_scan_rejects_kernel_bypass_and_placeholders(self):
        source = ('-- sorry in a comment is fine\n/- set_option debug.skipKernelTC true -/\n'
                  'theorem a : True := by sorry\nset_option debug.skipKernelTC true in\n'
                  'run_cmd withOptions (·.setBool `debug.skipKernelTC true) (pure ())\n'
                  'unsafe def b := 0\n@[extern "c"] opaque c : Nat\n')
        errors, tokens = universe.scan_source('X.lean', source)
        self.assertEqual(errors, ['X.lean:3: sorry', 'X.lean:4: kernel-check bypass (set_option debug.)',
                                  'X.lean:5: kernel-check bypass (debug.skipKernelTC)'])
        self.assertEqual(tokens, {'unsafe': 1, '@[extern': 1})
        self.assertEqual(universe.scan(), [])

    def test_compile_rejects_sorry_warnings(self):
        # `lean` exits 0 on `declaration uses 'sorry'`, and examples never reach the olean.
        outputs = iter([(0, "X.lean:1:0: warning: declaration uses 'sorry'\n"), (0, ''), (1, 'error')])
        original = universe.run
        universe.run = lambda *a, **k: subprocess.CompletedProcess(a, *next(outputs))
        try:
            with tempfile.TemporaryDirectory() as temp:
                base = Path(temp)
                compile_once = lambda: universe.compile_unit('X.lean', '.', base / 'X.olean', [], base / 'x.log')
                self.assertIn("declaration uses 'sorry'", compile_once() or '')
                self.assertIsNone(compile_once())
                self.assertIn('exited 1', compile_once())
        finally:
            universe.run = original

    def test_bundles_never_share_a_declaration_name_or_module_name(self):
        unit = lambda f, root, module, names=(), deps=(): universe.Unit(f, root, module, deps, (), None, names)
        units = [unit('a/Main.lean', 'a', 'Main', ('Ex.t',)), unit('a/Solution.lean', 'a', 'Solution', ('Ex.t',)),
                 unit('b/Main.lean', 'b', 'Main', ('Other.t',)), unit('c/X.lean', 'c', 'X', ('Y.u',))]
        by_file = {u.file: u for u in units}
        bundles = universe.bundles(units, by_file, Path('/out'))
        for bundle in bundles:
            files = {u.file for u in bundle}
            self.assertFalse({'a/Main.lean', 'a/Solution.lean'} <= files)
            self.assertFalse({'a/Main.lean', 'b/Main.lean'} <= files)
        self.assertEqual(sorted(u.file for b in bundles for u in b), sorted(by_file))


class ReplayTests(unittest.TestCase):
    """assumptions.kernel_replay against a stand-in leanchecker that rejects module `Bad`."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.toolchain = Path(self.temp.name)
        installed_inputs(self.toolchain)
        self.calls = self.toolchain / 'calls'
        checker = self.toolchain / 'bin/leanchecker'
        checker.write_text(f'#!/bin/sh\necho "$1" >> {self.calls}\n[ "$1" != Bad ] || {{ echo rejected; exit 1; }}\n'
                           '[ "$1" != Killed ] || kill -9 $$\n')
        checker.chmod(0o755)
        (self.toolchain / 'bin/lean').write_text('lean')

    def checked(self):
        return sorted(self.calls.read_text().split()) if self.calls.exists() else []

    def test_rejection_is_recorded_and_fails(self):
        record = assumptions.kernel_replay({'Bad': 'b', 'Good': 'g'}, self.toolchain, '')
        self.assertEqual((record['status'], [r['module'] for r in record['rejected']]), ('fail', ['Bad']))
        self.assertEqual(assumptions.replay_record(record), ({'Bad', 'Good'}, {'Bad'}))

    def test_rejection_records_the_checker_exit_status(self):
        record = assumptions.kernel_replay({'Bad': 'b', 'Good': 'g', 'Killed': 'k'}, self.toolchain, '')
        self.assertEqual(record['status'], 'fail')
        self.assertEqual({r['module']: r['output'] for r in record['rejected']},
                         {'Bad': 'leanchecker exited 1\nrejected\n', 'Killed': 'leanchecker exited -9\n'})
        self.assertEqual(sorted(record['rejected'][0]), ['module', 'output'])

    def test_cache_reuses_only_identical_passed_lake_oleans(self):
        cache, lake = self.toolchain / 'cache.json', frozenset({'Bad', 'Good', 'Other'})
        assumptions.kernel_replay({'Bad': 'b', 'Good': 'g', 'Other': 'o', 'Local': 'l'}, self.toolchain, '', cache, lake)
        self.calls.unlink()
        record = assumptions.kernel_replay({'Bad': 'b', 'Good': 'g', 'Local': 'l', 'New': 'n'},
                                           self.toolchain, '', cache, lake)
        # Rejected and non-Lake modules (test roots reuse names such as `Main`) are re-checked.
        self.assertEqual((record['reused'], self.checked()), (['Good'], ['Bad', 'Local', 'New']))
        self.calls.unlink()
        record = assumptions.kernel_replay({'Good': 'g', 'Other': 'changed'}, self.toolchain, '', cache, lake)
        self.assertEqual((record['reused'], self.checked()), ([], ['Good', 'Other']))

    def test_installed_input_changes_invalidate_cache_with_fixed_project_bytes(self):
        checker = (self.toolchain / 'bin/leanchecker').read_bytes()
        project = self.toolchain / 'project/Lib.olean'
        project.parent.mkdir()
        project.write_bytes(b'fixed project artifact')
        digests, lake = {'Lib': assumptions.file_sha256(project)}, frozenset({'Lib'})
        for index, name in enumerate(('lib/libleanshared.so', 'lib/lean/Init.olean', 'lib/lean/Init.ir.sig')):
            with self.subTest(name=name):
                cache = self.toolchain / f'runtime-cache-{index}.json'
                assumptions.kernel_replay(digests, self.toolchain, '', cache, lake)
                self.calls.unlink()
                self.assertEqual(assumptions.kernel_replay(digests, self.toolchain, '', cache, lake)['reused'], ['Lib'])
                self.assertEqual(self.checked(), [])
                changed = self.toolchain / name
                saved = changed.stat()
                changed.write_bytes(b'modified')
                os.utime(changed, ns=(saved.st_atime_ns, saved.st_mtime_ns))
                replay = assumptions.kernel_replay(digests, self.toolchain, '', cache, lake)
                self.assertEqual((replay['reused'], self.checked()), ([], ['Lib']))
                self.assertEqual((self.toolchain / 'bin/leanchecker').read_bytes(), checker)
                self.assertEqual(project.read_bytes(), b'fixed project artifact')
                self.calls.unlink()

    def test_missing_runtime_cache_binding_requires_replay(self):
        cache, lake, digests = self.toolchain / 'cache.json', frozenset({'Lib'}), {'Lib': 'fixed'}
        assumptions.kernel_replay(digests, self.toolchain, '', cache, lake)
        record = json.loads(cache.read_text())
        del record['toolchain_runtime_sha256']
        cache.write_text(json.dumps(record))
        self.calls.unlink()
        replay = assumptions.kernel_replay(digests, self.toolchain, '', cache, lake)
        self.assertEqual((replay['reused'], self.checked()), ([], ['Lib']))

    def test_runtime_mutation_during_replay_does_not_publish_cache(self):
        cache, lake, digests = self.toolchain / 'cache.json', frozenset({'Lib'}), {'Lib': 'fixed'}
        assumptions.kernel_replay(digests, self.toolchain, '', cache, lake)
        original_cache = cache.read_bytes()
        runner = subprocess.run

        def changed(*args, **kwargs):
            result = runner(*args, **kwargs)
            (self.toolchain / 'lib/lean/Init.ir.sig').write_bytes(b'modified')
            return result

        with mock.patch.object(assumptions.subprocess, 'run', side_effect=changed):
            with self.assertRaisesRegex(ValueError, 'runtime changed during kernel replay'):
                assumptions.kernel_replay({**digests, 'Local': 'fixed'}, self.toolchain, '', cache, lake)
        self.assertEqual(cache.read_bytes(), original_cache)

    def test_extraction_runtime_mismatch_rejects_before_checker(self):
        expected = assumptions.toolchain_runtime_sha256(self.toolchain)
        (self.toolchain / 'lib/lean/Init.olean').write_bytes(b'modified')
        with self.assertRaisesRegex(ValueError, 'between extraction and replay'):
            assumptions.kernel_replay({'Lib': 'fixed'}, self.toolchain, '', expected_runtime=expected)
        self.assertEqual(self.checked(), [])

    def test_gates_share_one_replay_cache(self):
        # Every gate of a build audits through one cache: only changed artifacts replay again.
        cache = self.toolchain / 'gate-cache.json'
        lake = frozenset({'Lib', 'Other'})
        original = (universe.compile_unit, universe.audit_modules)
        digests = {'Lib': 'l1', 'Other': 'o1'}

        def audit(modules, lean_path, output, cache=None, sources=None):
            # What assumptions.py does for the gate's module: the gate-time module is never cacheable.
            assumptions.kernel_replay({**digests, modules[0]: 'g'}, self.toolchain, '', cache, lake)
            return {'status': 'pass', 'exit_code': 0, 'theorem_count': 1, 'violations': []}

        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            gated = sorted(universe.GATES)[0]  # a real gate-audited file: gate() checks the copy's bytes
            source = work / Path(gated).name
            source.write_bytes((ROOT / gated).read_bytes())
            universe.compile_unit = lambda *a, **k: None
            universe.audit_modules = audit
            try:
                run = lambda name: universe.gate(source, work, work, work / name, cache)
                self.assertEqual(run('a')['status'], 'pass')
                module = universe.module_of(str(source), str(work))
                self.assertEqual(self.checked(), sorted([module, 'Lib', 'Other']))
                self.calls.unlink()
                self.assertEqual(run('b')['status'], 'pass')  # identical library: only the gate module replays
                self.assertEqual(self.checked(), [module])
                self.calls.unlink()
                digests['Lib'] = 'l2'  # a changed artifact drops the cache: everything replays again
                self.assertEqual(run('c')['status'], 'pass')
                self.assertEqual(self.checked(), sorted([module, 'Lib', 'Other']))
            finally:
                universe.compile_unit, universe.audit_modules = original

    def worker_counts(self, env, work):
        """Pool sizes `work()` requests under `env` (stage and build-guard variables otherwise cleared)."""
        import concurrent.futures
        sizes, real = [], concurrent.futures.ThreadPoolExecutor

        def pool(n):
            sizes.append(n)
            return real(n)

        keys = ('AIR2LEAN_JOBS', 'AIR2LEAN_REPLAY_JOBS', 'AIR2LEAN_UNIVERSE_JOBS')
        saved = {k: os.environ.pop(k, None) for k in keys}
        os.environ.update(env)
        concurrent.futures.ThreadPoolExecutor, universe.ThreadPoolExecutor = pool, pool
        try:
            work()
        finally:
            concurrent.futures.ThreadPoolExecutor, universe.ThreadPoolExecutor = real, real
            for k in keys:
                os.environ.pop(k, None)
            os.environ.update({k: v for k, v in saved.items() if v is not None})
        return sizes

    def test_worker_counts_follow_the_stage_override_then_the_build_budget(self):
        modules = {'A': 'a', 'B': 'b', 'C': 'c'}
        original = universe.compile_unit
        compiled = []
        universe.compile_unit = lambda source, *a, **k: compiled.append(source)
        units = [universe.Unit(f'{m}.lean', 'r', f'ZZ{m}', (), (), None, ()) for m in modules]
        by_file = {u.file: u for u in units}

        def replay():
            self.calls.unlink(missing_ok=True)
            assumptions.kernel_replay(modules, self.toolchain, '')
            self.assertEqual(self.checked(), sorted(modules))  # every requested module is still checked

        def compile_all():
            compiled.clear()
            universe.compile_all(units, by_file, self.toolchain / 'out')
            self.assertEqual(sorted(compiled), sorted(by_file))

        try:
            for stage, work in (('AIR2LEAN_REPLAY_JOBS', replay), ('AIR2LEAN_UNIVERSE_JOBS', compile_all)):
                self.assertEqual(self.worker_counts({'AIR2LEAN_JOBS': '1'}, work), [1])
                self.assertEqual(self.worker_counts({'AIR2LEAN_JOBS': '1', stage: '2'}, work), [2])
                self.assertEqual(self.worker_counts({}, work), [min(4, os.cpu_count() or 1)])
        finally:
            universe.compile_unit = original

    def test_a_second_gate_run_does_not_reuse_the_first_runs_replay(self):
        # A run's cache is a fresh file in the run's temporary directory; without one nothing is cached.
        self.assertIsNone(universe.gate.__defaults__[0])
        lake, digests = frozenset({'Lib'}), {'Lib': 'l1'}
        for _ in range(2):
            with tempfile.TemporaryDirectory() as run_dir:
                cache = Path(run_dir) / 'replay-cache.json'
                for _ in range(2):  # the second gate of the same run reuses the first one's replay
                    self.calls.unlink(missing_ok=True)
                    assumptions.kernel_replay(digests, self.toolchain, '', cache, lake)
                    self.assertEqual(self.checked(), ['Lib'] if _ == 0 else [])
        self.calls.unlink(missing_ok=True)
        for _ in range(2):  # no cache: every gate replays
            assumptions.kernel_replay(digests, self.toolchain, '', None, lake)
        self.assertEqual(self.checked(), ['Lib', 'Lib'])

    def test_gate_scripts_keep_their_replay_cache_in_the_run_directory(self):
        for script in ('nan-bits', 'enc-exactness', 'packed-casts', 'try-pointers/lifetimes'):
            text = (ROOT / 'tests/roadmap' / script / 'check.sh').read_text()
            self.assertIn('--replay-cache "$work/replay-cache.json"', text, script)
            self.assertIn('work=$(mktemp -d', text, script)


class FreshnessTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.olean = Path(self.temp.name) / 'M.olean'
        self.olean.write_bytes(b'olean')
        self.toolchain = Path(self.temp.name) / 'toolchain'
        installed_inputs(self.toolchain)
        sysroot = mock.patch.object(assumptions, 'lake_env',
                                    side_effect={'LEAN_SYSROOT': str(self.toolchain)}.__getitem__)
        sysroot.start()
        self.addCleanup(sysroot.stop)
        runtime = assumptions.toolchain_runtime_sha256(self.toolchain)
        self.report = {'extractor': {'lean_sysroot': str(self.toolchain), 'toolchain_runtime_sha256': runtime},
                      'freshness': {
            'revision': assumptions.git_revision(), 'lake_trace_check': {'modules': [], 'status': 'up-to-date'},
            'lean_sysroot': str(self.toolchain), 'toolchain_runtime_sha256': runtime,
            'artifacts': [{'module': 'M', 'olean': str(self.olean), 'olean_sha256': assumptions.file_sha256(self.olean),
                           'source': None, 'source_sha256': None}]}}

    def test_installed_input_change_is_stale_with_fixed_report_and_project_artifact(self):
        original_report, original_olean = json.dumps(self.report), self.olean.read_bytes()
        for name in ('lib/libleanshared.so', 'lib/lean/Init.olean', 'lib/lean/Init.ir.sig'):
            with self.subTest(name=name):
                changed = self.toolchain / name
                saved = changed.stat()
                changed.write_bytes(b'modified')
                os.utime(changed, ns=(saved.st_atime_ns, saved.st_mtime_ns))
                with self.assertRaisesRegex(ValueError, 'stale: toolchain runtime changed'):
                    assumptions.verify_fresh(self.report, allow_dirty=True)
                self.assertEqual((json.dumps(self.report), self.olean.read_bytes()), (original_report, original_olean))
                changed.write_bytes(b'original')
                os.utime(changed, ns=(saved.st_atime_ns, saved.st_mtime_ns))
                self.assertEqual(assumptions.verify_fresh(self.report, allow_dirty=True)['artifacts'], 1)

    def test_missing_or_inconsistent_runtime_bindings_are_rejected(self):
        for section, key in (('freshness', 'lean_sysroot'), ('freshness', 'toolchain_runtime_sha256'),
                             ('extractor', 'lean_sysroot'), ('extractor', 'toolchain_runtime_sha256')):
            with self.subTest(section=section, key=key):
                broken = json.loads(json.dumps(self.report))
                del broken[section][key]
                with self.assertRaisesRegex(ValueError, 'runtime binding'):
                    assumptions.verify_fresh(broken, allow_dirty=True)
        broken = json.loads(json.dumps(self.report))
        broken['extractor']['toolchain_runtime_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'runtime binding'):
            assumptions.verify_fresh(broken, allow_dirty=True)

    def test_changed_selected_sysroot_rejects_the_unchanged_old_bound_tree(self):
        other = Path(self.temp.name) / 'other-toolchain'
        installed_inputs(other)
        self.assertEqual(assumptions.toolchain_runtime_sha256(other),
                         self.report['freshness']['toolchain_runtime_sha256'])
        with mock.patch.object(assumptions, 'lake_env', return_value=str(other)):
            with self.assertRaisesRegex(ValueError, 'runtime root changed'):
                assumptions.verify_fresh(self.report, allow_dirty=True)

    def test_runtime_is_recomputed_after_project_artifact_verification(self):
        digest = assumptions.file_sha256

        def changed(path):
            value = digest(path)
            if path == self.olean:
                (self.toolchain / 'lib/lean/Init.ir.sig').write_bytes(b'modified')
            return value

        with mock.patch.object(assumptions, 'file_sha256', side_effect=changed):
            with self.assertRaisesRegex(ValueError, 'stale: toolchain runtime changed'):
                assumptions.verify_fresh(self.report, allow_dirty=True)

    def test_existing_extractor_runtime_is_forwarded_to_replay_and_freshness(self):
        raw = {'modules': ['M'], 'nodes': [], 'extractor': self.report['extractor']}
        values = {'LEAN_SYSROOT': str(self.toolchain), 'LEAN_PATH': self.temp.name}
        with mock.patch.object(assumptions, 'lake_env', side_effect=values.__getitem__), \
                mock.patch.object(assumptions, 'kernel_replay', return_value={'status': 'pass'}) as replay:
            freshness = assumptions.replay_and_freshness(raw)
        runtime = self.report['extractor']['toolchain_runtime_sha256']
        self.assertEqual(replay.call_args.kwargs, {'expected_runtime': runtime})
        self.assertEqual((freshness['lean_sysroot'], freshness['toolchain_runtime_sha256']),
                         (str(self.toolchain.resolve()), runtime))

    def test_changed_artifact_or_revision_is_stale(self):
        self.assertEqual(assumptions.verify_fresh(self.report, allow_dirty=True)['artifacts'], 1)
        self.olean.write_bytes(b'other')
        with self.assertRaisesRegex(ValueError, 'stale'):
            assumptions.verify_fresh(self.report, allow_dirty=True)
        self.report['freshness']['revision'] = {'head': '0' * 40, 'tracked_dirty': False}
        with self.assertRaisesRegex(ValueError, 'revision'):
            assumptions.verify_fresh(self.report, allow_dirty=True)

    def test_dirty_report_needs_permission(self):
        self.report['freshness']['revision']['tracked_dirty'] = True
        with self.assertRaisesRegex(ValueError, 'allow-dirty'):
            assumptions.verify_fresh(self.report)
        self.assertTrue(assumptions.verify_fresh(self.report, allow_dirty=True)['dirty_allowed'])


if __name__ == '__main__':
    unittest.main()
