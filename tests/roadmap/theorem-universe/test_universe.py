#!/usr/bin/env python3
"""Offline regressions for the theorem universe (F2), kernel replay (S1) and freshness (H1).

No Lean, Lake or Zig: Lean and leanchecker are replaced by small scripts. The compiled audit
itself runs in CI (`theorem_universe.py audit`) and in tests/roadmap/architecture-audit/claims.
"""
import importlib.util
import contextlib
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

    def test_a_clash_splits_the_run_and_an_unsplittable_one_fails_closed(self):
        # `Spoof` declares a name a Lake module of `Real` declares (Fixture's claim-head spoofs and
        # ZigLean.Conc.Total): the source parse cannot see it, so their run clashes and is split.
        # `Twice`'s own closure clashes: it cannot be audited at all.
        unit = lambda f: universe.Unit(f + '.lean', '.', f, (), (), None, ())
        units = [unit('Spoof'), unit('Real'), unit('Twice')]
        clash = "error: import Spoof failed, environment already contains 'N' from M"

        def audit_modules(modules, lean_path, output, cache=None, sources=None):
            collision = clash if {'Spoof', 'Real'} <= set(modules) or 'Twice' in modules else None
            return {'modules': modules, 'report': str(output), 'status': 'fail' if collision else 'pass',
                    'exit_code': 1 if collision else 0, 'collision': collision, 'violations': []}

        with mock.patch.multiple(universe, universe=lambda: ([], units), compile_all=lambda *a: [],
                                 audit_modules=audit_modules, write_report=lambda *a: None), \
                tempfile.TemporaryDirectory() as temp:
            report = universe.audit(Path(temp), False, None, None)
        audited = [r['modules'] for r in report['audits'] if r['status'] == 'pass']
        self.assertEqual(sorted(m for run in audited for m in run), ['Real', 'Spoof'])
        self.assertFalse(any({'Spoof', 'Real'} <= set(run) for run in audited))
        self.assertEqual(report['status'], 'fail')
        self.assertEqual(report['errors'], [f'Twice.lean: cannot be audited, its import closure declares a name '
                                            f'twice ({clash})'])


class AuditModulesTests(unittest.TestCase):
    def test_all_declarations_is_opt_in_without_changing_the_audit_context(self):
        modules = ['Example.Main', 'Example.Other']
        self.addCleanup(setattr, universe, 'run', universe.run)
        with tempfile.TemporaryDirectory() as temp:
            work = Path(temp)
            libs = [work / 'one', work / 'two']
            cache, sources = work / 'replay.json', work / 'sources.json'
            for flags in ({}, {'all_declarations': False}, {'all_declarations': True}):
                with self.subTest(flags=flags):
                    enabled = flags.get('all_declarations', False)
                    output = work / 'audit.json'
                    report = {'status': 'pass', 'theorem_count': 2,
                              'kernel_replay': {'status': 'pass'}, 'violations': []}
                    if enabled:
                        report.update(selected_declaration_roots=['Example.Main.unused'],
                                      framework_candidates={'complete': False,
                                                            'ordinary_exemptions': [],
                                                            'declarations': [
                                                                {'name': 'Example.Main.unused',
                                                                 'verdict': 'unknown',
                                                                 'ordinary_exemption': False}]})
                    calls = []

                    def run(command, env):
                        calls.append((command, env))
                        output.write_text(json.dumps(report))
                        return subprocess.CompletedProcess(command, 0, '')

                    universe.run = run
                    result = universe.audit_modules(modules, libs, output, cache, sources, **flags)
                    self.assertEqual(len(calls), 1)
                    command, env = calls[0]
                    self.assertEqual(command.count('--all-declarations'), int(enabled))
                    self.assertEqual([command[i + 1] for i, arg in enumerate(command)
                                      if arg == '--module'], modules)
                    self.assertEqual(command[command.index('--replay-cache') + 1], str(cache))
                    self.assertEqual(command[command.index('--sources') + 1], str(sources))
                    self.assertEqual(command[command.index('--output') + 1], str(output))
                    self.assertIn('--no-build', command)
                    self.assertIn('--allow-no-theorems', command)
                    self.assertEqual(env['LEAN_PATH'], os.pathsep.join(map(str, libs)))
                    self.assertEqual(json.loads(output.read_text()), report)
                    self.assertEqual(set(result), {'modules', 'report', 'status', 'exit_code',
                                                   'theorem_count', 'seconds', 'kernel_replay',
                                                   'collision', 'violations'})
                    self.assertEqual((result['modules'], result['status'], result['exit_code']),
                                     (modules, 'pass', 0))


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
                try:
                    with self.assertRaisesRegex(ValueError, 'stale: toolchain runtime changed'):
                        assumptions.verify_fresh(self.report, allow_dirty=True)
                    self.assertEqual((json.dumps(self.report), self.olean.read_bytes()), (original_report, original_olean))
                finally:
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
                mock.patch.object(assumptions, 'kernel_replay', return_value={'status': 'pass'}) as replay, \
                mock.patch.object(assumptions, 'library_compiled_inputs', return_value=[]) as inputs:
            freshness = assumptions.replay_and_freshness(raw)
            self.assertEqual(set(replay.call_args.kwargs),
                             {'expected_runtime', 'compiled_inputs_sha256', 'validate_inputs'})
            self.assertEqual(replay.call_args.kwargs['compiled_inputs_sha256'], universe.input_digest([]))
            validate = replay.call_args.kwargs['validate_inputs']
            validate()
            inputs.return_value = [['changed synthetic compiled input']]
            with self.assertRaisesRegex(ValueError, 'canonical Lake compiled inputs changed'):
                validate()
        runtime = self.report['extractor']['toolchain_runtime_sha256']
        self.assertEqual(replay.call_args.kwargs['expected_runtime'], runtime)
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


class CompiledUnitTests(unittest.TestCase):
    """Same compiler/audit/freshness flow; all compiler and installation inputs are synthetic."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.toolchain = self.root / 'toolchain'
        installed_inputs(self.toolchain)
        checker = self.toolchain / 'bin/leanchecker'
        checker.write_text('#!/bin/sh\nexit 0\n')
        checker.chmod(0o755)
        self.built = self.root / '.lake/build/lib/lean'
        for rel, data in {'ZigLean/Basic.lean': b'import Init\n',
                          '.lake/build/lib/lean/ZigLean/Basic.olean': b'canonical Lake output',
                          'local/Owned/Basic.lean': b'import ZigLean.Basic\n',
                          'local/Owned/Main.lean': b'import Owned.Basic\ntheorem p : True := trivial\n',
                          'other/Owned/Main.lean': b'import ZigLean.Basic\ntheorem q : True := trivial\n',
                          'local-parent/Proofs.lean': b'theorem staged : True := trivial\n',
                          'lean-toolchain': b'synthetic installation',
                          'lakefile.toml': b'name = "synthetic"\n',
                          'assurance/policy.json': b'{}'}.items():
            path = self.root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        self.basic = universe.Unit('local/Owned/Basic.lean', 'local', 'Owned.Basic', (),
                                   ('ZigLean.Basic',), None, ())
        self.main = universe.Unit('local/Owned/Main.lean', 'local', 'Owned.Main',
                                  (self.basic.file,), (), None, ('p',))
        self.other = universe.Unit('other/Owned/Main.lean', 'other', 'Owned.Main',
                                   (), ('ZigLean.Basic',), None, ('q',))
        self.staged = universe.Unit('local-parent/Proofs.lean', None, 'Universe.Staged', (), (), None, ())
        self.units = [self.basic, self.main, self.other, self.staged]
        self.headers = {'Owned.Main': ['Owned.Basic'], 'Owned.Basic': ['ZigLean.Basic'],
                        'Universe.Staged': ['Init'], 'ZigLean.Basic': ['Init'], 'Init': []}
        self.cache = self.root / 'replay-cache.json'
        self.paths = [self.built, self.toolchain / 'lib/lean']
        self.patch(universe, 'ROOT', self.root)
        self.patch(assumptions, 'ROOT', self.root)
        self.patch(universe, 'assumptions', assumptions)
        self.patch(universe, 'universe', lambda: ([], self.units))
        prepare = universe.prepare_compilation

        def preparing(*args):
            self.active_context = prepare(*args)
            return self.active_context

        self.patch(universe, 'prepare_compilation', preparing)
        self.patch(universe, 'run', self.compiler)
        self.patch(assumptions, 'run', lambda command: '')
        self.patch(assumptions, 'lake_env', {'LEAN_SYSROOT': str(self.toolchain),
                                          'LEAN_PATH': os.pathsep.join(map(str, self.paths))}.__getitem__)
        self.patch(assumptions, 'library_roots', lambda root: ['ZigLean'])
        self.patch(assumptions, 'prepared_tool', contextlib.nullcontext)
        self.patch(assumptions, 'git_revision', lambda: {'head': '1' * 40, 'tracked_dirty': False})
        self.patch(assumptions, 'load_policy', lambda path: {})
        self.patch(assumptions, 'witness_fixtures', lambda: [])
        self.patch(assumptions, 'float_semantics', lambda: mock.Mock(load_registry=lambda *a, **k: {}))
        self.patch(assumptions, 'extract', self.extract)
        self.patch(assumptions, 'apply_policy', lambda raw, *a: {
            'status': 'pass', 'theorem_count': 0, 'theorems': [], 'violations': [],
            'modules': raw['modules'], 'module_imports': raw['module_imports'],
            'kernel_replay': raw['kernel_replay']})
        environment = mock.patch.dict(os.environ, {'AIR2LEAN_UNIVERSE_JOBS': '1', 'AIR2LEAN_REPLAY_JOBS': '1'})
        environment.start()
        self.addCleanup(environment.stop)

    def patch(self, obj, name, value):
        patcher = mock.patch.object(obj, name, value)
        patcher.start()
        self.addCleanup(patcher.stop)

    def compiler(self, command, env=None):
        if command == ['lake', 'env', 'printenv', 'LEAN_PATH']:
            return subprocess.CompletedProcess(command, 0,
                                               os.pathsep.join([*map(str, self.paths), env['LEAN_PATH']]) + '\n')
        # This is the existing explicit-path Lean invocation, not an executable compiler.
        self.assertEqual(command[:3], ['lake', 'env', 'env'])
        self.assertEqual(command[3], 'LEAN_PATH=' + self.active_context['lean_path'])
        self.assertEqual(command[4], 'lean')
        unit = next(record for record in self.active_context['units'].values()
                    if record['compiler_source']['path'] == command[-1])
        self.assertEqual(command[command.index('-R') + 1], unit['compiler_root'])
        output, source = Path(command[command.index('-o') + 1]), self.root / command[-1]
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(b'compiled: ' + source.read_bytes())
        return subprocess.CompletedProcess(command, 0, '')

    def extract(self, modules, build, witnesses, *, all_declarations=False, lean_path=None):
        self.assertFalse(build)
        self.assertEqual(witnesses, [])
        self.assertEqual(lean_path, self.active_context['lean_path'])
        headers, pending = {}, list(modules)
        while pending:
            module = pending.pop()
            if module in headers or module not in self.headers:
                continue
            headers[module] = list(self.headers[module])
            pending.extend(headers[module])
        return {'modules': modules, 'nodes': [{'module': module} for module in modules],
                'module_imports': headers,
                'extractor': {'lean_sysroot': str(self.toolchain),
                              'toolchain_runtime_sha256': assumptions.toolchain_runtime_sha256(self.toolchain)}}

    def compiled(self, selected=None, *, output=None, extra_outputs=None):
        selected = selected or [self.main]
        by_file = {unit.file: unit for unit in self.units}
        output = output or Path(tempfile.mkdtemp(prefix='owned-', dir=self.root))
        context = universe.prepare_compilation(selected, by_file, output)
        for relative, content in (extra_outputs or {}).items():
            extra = universe.lib_of(output, selected[0].root) / relative
            extra.parent.mkdir(parents=True, exist_ok=True)
            extra.write_bytes(content)
        self.assertEqual(universe.compile_all(universe.closure(selected, by_file), by_file, output,
                                             compiled_units=context), [])
        universe.seal_compilation(context)
        return context

    def audited(self, context=None):
        context = context or self.compiled()
        output = Path(context['output_dir']) / 'audit.json'
        result = universe.audit_modules(context['selected_modules'], [], output, self.cache,
                                        compiled_units=context)
        self.assertEqual((result['status'], result['exit_code']), ('pass', 0), result)
        report = json.loads(output.read_text())
        assumptions.verify_fresh(report, allow_dirty=True)
        return report

    def test_default_audit_binds_unused_header_closure_and_preserves_safe_reuse(self):
        # Main's declaration graph deliberately has no Basic node. The header still owns it.
        context = self.compiled(extra_outputs={'Owned/Private.olean': b'private dependency'})
        report = self.audited(context)
        rows = {row['module']: row for row in report['freshness']['artifacts']}
        self.assertIn('Owned.Basic', rows)
        self.assertEqual(rows['Owned.Basic']['source'], self.basic.file)
        repeated = self.audited()
        self.assertEqual(repeated['kernel_replay']['reused'], ['ZigLean.Basic'])
        self.assertTrue({'Owned.Main', 'Owned.Basic'} <= set(repeated['kernel_replay']['modules']))
        self.assertEqual(assumptions.cacheable_modules(
            {**self.headers, 'ZigLean.Basic': ['Owned.Private'], 'Owned.Private': ['Init']}, ['ZigLean.Basic'],
            [*self.paths, universe.lib_of(Path(context['output_dir']), 'local')],
            self.toolchain), frozenset())

    def test_default_owner_forwards_binding_and_uses_fresh_output_namespaces(self):
        output = self.root / 'default-audit'
        with mock.patch.object(self, 'units', [self.basic, self.main, self.staged]):
            first = universe.audit(output, False, None, self.cache)
            self.assertEqual(first['status'], 'pass', first)
            first_report = json.loads(Path(first['audits'][0]['report']).read_text())
            assumptions.verify_fresh(first_report, allow_dirty=True)
            second = universe.audit(output, False, None, self.cache)
            self.assertEqual(second['status'], 'pass', second)
            second_report = json.loads(Path(second['audits'][0]['report']).read_text())
            assumptions.verify_fresh(second_report, allow_dirty=True)
            self.assertNotEqual(first_report['freshness']['compiled_units']['output_dir'],
                                second_report['freshness']['compiled_units']['output_dir'])
            assumptions.verify_fresh(first_report, allow_dirty=True)

    def test_fixed_report_and_outputs_reject_original_and_unused_helper_source_mutation(self):
        report = self.audited()
        fixed = json.dumps(report)
        outputs = {row['olean']: assumptions.file_sha256(self.root / row['olean'])
                   for row in report['freshness']['artifacts']}
        for unit in (self.main, self.basic):
            with self.subTest(module=unit.module):
                path, original = self.root / unit.file, (self.root / unit.file).read_bytes()
                try:
                    path.write_bytes(original + b'-- changed source only\n')
                    with self.assertRaisesRegex(ValueError, f'{unit.module} source changed'):
                        assumptions.verify_fresh(report, allow_dirty=True)
                    self.assertEqual(json.dumps(report), fixed)
                    self.assertEqual(outputs, {path: assumptions.file_sha256(self.root / path) for path in outputs})
                finally:
                    path.write_bytes(original)
                assumptions.verify_fresh(report, allow_dirty=True)

    def test_missing_transplanted_or_stripped_context_is_refused_by_generic_admission(self):
        report = self.audited()
        missing = json.loads(json.dumps(report))
        del missing['freshness']['compiled_units']
        for row in missing['freshness']['artifacts']:
            if row['module'].startswith('Owned.'):
                row.update(source=None, source_sha256=None)
        for selection in (None, [], ['Unrelated']):
            with self.subTest(selection=selection):
                if selection is None:
                    missing.pop('modules', None)
                else:
                    missing['modules'] = selection
                with self.assertRaisesRegex(ValueError, 'no compiler-owned run binding'):
                    assumptions.verify_fresh(missing, allow_dirty=True)
        header_only = json.loads(json.dumps(missing))
        header_only.update(modules=['Unrelated'], module_imports={'Unrelated': ['Owned.Main']})
        for row in header_only['freshness']['artifacts']:
            if row['module'].startswith('Owned.'):
                row['module'] = 'Unrelated.' + row['module']
        with self.assertRaisesRegex(ValueError, 'no compiler-owned run binding'):
            assumptions.verify_fresh(header_only, allow_dirty=True)
        other = self.compiled([self.other])
        transplanted = json.loads(json.dumps(report))
        transplanted['freshness']['compiled_units'] = other
        with self.assertRaisesRegex(ValueError, 'report source/output differs'):
            assumptions.verify_fresh(transplanted, allow_dirty=True)
        stripped = json.loads(json.dumps(report))
        next(row for row in stripped['freshness']['artifacts']
             if row['module'] == self.basic.module).update(source=None, source_sha256=None)
        with self.assertRaisesRegex(ValueError, 'report source/output differs'):
            assumptions.verify_fresh(stripped, allow_dirty=True)

    def test_staged_input_does_not_substitute_for_original_source_identity(self):
        report = self.audited(self.compiled([self.staged]))
        unit = report['freshness']['compiled_units']['units'][self.staged.module]
        unit['source'] = dict(unit['compiler_source'])
        row = next(row for row in report['freshness']['artifacts'] if row['module'] == self.staged.module)
        row.update(source=unit['source']['path'], source_sha256=unit['source']['sha256'])
        original = self.root / self.staged.file
        original.write_bytes(original.read_bytes() + b'-- original-only mutation\n')
        with self.assertRaisesRegex(ValueError, 'Universe.Staged source changed'):
            assumptions.verify_fresh(report, allow_dirty=True)

    def test_missing_changed_or_added_output_companion_is_refused(self):
        context = self.compiled()
        output = Path(context['units'][self.basic.module]['output_path'])
        original = output.read_bytes()
        for kind in ('missing', 'changed', 'added'):
            with self.subTest(kind=kind):
                companion = output.with_suffix('.ir')
                try:
                    if kind == 'missing':
                        output.unlink()
                    elif kind == 'changed':
                        output.write_bytes(b'replaced after compilation')
                    else:
                        companion.write_bytes(b'new loader input')
                    with self.assertRaises(ValueError):
                        universe.verify_compilation(context)
                finally:
                    output.write_bytes(original)
                    companion.unlink(missing_ok=True)
                universe.verify_compilation(context)

    def test_later_compiler_action_cannot_replace_an_earlier_captured_output(self):
        by_file = {unit.file: unit for unit in self.units}
        output = self.root / 'later-action'
        context = universe.prepare_compilation([self.main], by_file, output)
        compiler = self.compiler

        def replace_earlier(command, env=None):
            result = compiler(command, env)
            if command[-1] == self.main.file:
                Path(context['units'][self.basic.module]['output_path']).write_bytes(b'replacement')
            return result

        with mock.patch.object(universe, 'run', side_effect=replace_earlier):
            self.assertEqual(universe.compile_all([self.basic, self.main], by_file, output,
                                                 compiled_units=context), [])
        with self.assertRaisesRegex(ValueError, 'Unit output changed: Owned.Basic'):
            universe.seal_compilation(context)

    def test_unowned_or_missing_actual_header_import_is_refused(self):
        for headers, diagnostic in (({key: value for key, value in self.headers.items() if key != 'Owned.Basic'},
                                     'incomplete import headers: Owned.Basic'),
                                    ({**self.headers, 'Owned.Basic': ['Foreign.Unused'], 'Foreign.Unused': []},
                                     'unowned private import: Foreign.Unused')):
            with self.subTest(headers=headers), mock.patch.object(self, 'headers', headers):
                context = self.compiled(extra_outputs={'Foreign/Unused.olean': b'existing foreign output'})
                output = Path(context['output_dir']) / 'audit.json'
                result = universe.audit_modules(context['selected_modules'], [], output, compiled_units=context)
                self.assertEqual((result['status'], result['exit_code']), ('error', 2))
                self.assertFalse(json.loads(output.read_text()).get('freshness'))
                self.assertIn(diagnostic, result['violations'][0])

    def test_existing_registered_witness_binding_is_preserved_without_unit_qualification(self):
        context = self.compiled(output=self.root / '.lake/assurance/witness-fixtures')
        report = self.audited(context)
        del report['freshness']['compiled_units']
        report.update(modules=['ZigLean.Basic'], witness_modules=['Owned.Main'], scope='all-shipped-modules')
        with mock.patch.object(assumptions, 'witness_fixtures', return_value=[self.main.file]):
            assumptions.verify_fresh(report, allow_dirty=True)
            report['freshness']['artifacts'][0].update(source=None, source_sha256=None)
            with self.assertRaisesRegex(ValueError, 'no matching compiler-owned run binding'):
                assumptions.verify_fresh(report, allow_dirty=True)

    def test_changed_compiled_input_does_not_publish_a_replay_cache_entry(self):
        report = self.audited()
        original_cache = self.cache.read_bytes()
        original_run = subprocess.run
        companion = self.built / 'ZigLean/Basic.ir'

        def changed(*args, **kwargs):
            result = original_run(*args, **kwargs)
            companion.write_bytes(b'changed while checking')
            return result

        context = report['freshness']['compiled_units']
        raw = self.extract(context['selected_modules'], False, [], lean_path=context['lean_path'])
        with mock.patch.object(assumptions.subprocess, 'run', side_effect=changed):
            with self.assertRaisesRegex(ValueError, 'canonical Lake compiled inputs changed'):
                assumptions.replay_and_freshness(raw, self.cache, compiled_units=context)
        self.assertEqual(self.cache.read_bytes(), original_cache)

    def test_native_top_level_lookup_does_not_fall_back_to_a_later_child(self):
        first, second = self.root / 'first', self.root / 'second'
        (first / 'Foo').mkdir(parents=True)
        (second / 'Foo').mkdir(parents=True)
        (second / 'Foo/Child.olean').write_bytes(b'later child')
        with self.assertRaisesRegex(ValueError, 'Foo.Child'):
            assumptions.locate('Foo.Child', [first, second])


if __name__ == '__main__':
    unittest.main()
