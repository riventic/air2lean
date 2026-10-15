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
        self.assertTrue(set(universe.GATES) <= set(gated))
        self.assertTrue(all(gated[f] == script for f, script in universe.GATES.items()))
        # Gate execution audits the dependency closure too, rather than merely assigning a
        # wrapper to a script which never compiles it (the original DispatchTemplates gap).
        covered = {u.file for root in universe.GATES for u in universe.gate_units(units, [root])}
        self.assertEqual(covered, set(gated))

    def test_gate_audits_indirect_clients_and_propagates_their_compile_errors(self):
        from unittest.mock import patch
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'Root.lean').write_text('theorem checked : True := trivial\n')
            copy = root / 'copy'
            copy.mkdir()
            source = copy / 'Root.lean'
            source.write_bytes((root / 'Root.lean').read_bytes())
            units = [universe.Unit('Root.lean', '.', 'Root', (), (), 'gate.sh', ('checked',)),
                     universe.Unit('Client.lean', '.', 'Client', ('Root.lean',), (), 'gate.sh', ('client',)),
                     universe.Unit('Outer.lean', '.', 'Outer', ('Client.lean',), (), 'gate.sh', ('outer',)),
                     universe.Unit('Other.lean', '.', 'Other', (), (), None, ('other',))]
            audited = [{'status': 'pass', 'theorem_count': 3}]
            with patch.object(universe, 'ROOT', root), \
                    patch.object(universe, 'GATES', {'Root.lean': 'gate.sh'}), \
                    patch.object(universe, 'universe', return_value=([], units)), \
                    patch.object(universe, 'compile_all', return_value=[]) as compile_, \
                    patch.object(universe, 'audit_bundles', return_value=(audited, [])) as audit:
                report = universe.gate(source, copy, root / 'generated', root / 'out')
                self.assertEqual(report['status'], 'pass')
                expected = {'Root.lean', 'Client.lean', 'Outer.lean'}
                self.assertEqual(set(report['units']), expected)
                self.assertEqual({u.file for u in compile_.call_args.args[0]}, expected)
                self.assertEqual({u.file for u in audit.call_args.args[0]}, expected)
                self.assertEqual(compile_.call_args.args[4]['Root.lean'], (str(source), str(copy)))
                audit.reset_mock()
                compile_.return_value = ['Outer.lean: declaration uses sorry']
                failed = universe.gate(source, copy, root / 'generated', root / 'out')
                self.assertEqual(failed['status'], 'fail')
                audit.assert_not_called()

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
        (self.toolchain / 'bin').mkdir()
        self.calls = self.toolchain / 'calls'
        checker = self.toolchain / 'bin/leanchecker'
        checker.write_text(f'#!/bin/sh\necho "$1" >> {self.calls}\n[ "$1" != Bad ] || {{ echo rejected; exit 1; }}\n')
        checker.chmod(0o755)
        (self.toolchain / 'bin/lean').write_text('lean')

    def checked(self):
        return sorted(self.calls.read_text().split()) if self.calls.exists() else []

    def test_rejection_is_recorded_and_fails(self):
        record = assumptions.kernel_replay({'Bad': 'b', 'Good': 'g'}, self.toolchain, '')
        self.assertEqual((record['status'], [r['module'] for r in record['rejected']]), ('fail', ['Bad']))
        self.assertEqual(assumptions.replay_record(record), ({'Bad', 'Good'}, {'Bad'}))

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

    def test_changed_shared_runtime_invalidates_replay_with_identical_stubs(self):
        library = self.toolchain / 'lib/lean/libleanshared.so.1'
        library.parent.mkdir(parents=True)
        library.write_bytes(b'original runtime')
        cache = self.toolchain / 'cache.json'
        checker_sha = assumptions.file_sha256(self.toolchain / 'bin/leanchecker')
        assumptions.kernel_replay({'Good': 'g'}, self.toolchain, '', cache, frozenset({'Good'}))
        self.calls.unlink()
        library.write_bytes(b'changed runtime')
        record = assumptions.kernel_replay({'Good': 'g'}, self.toolchain, '', cache, frozenset({'Good'}))
        self.assertEqual(assumptions.file_sha256(self.toolchain / 'bin/leanchecker'), checker_sha)
        self.assertEqual((record['reused'], self.checked()), ([], ['Good']))
        self.calls.unlink()
        module = library.with_name('Init.olean.private')
        module.write_bytes(b'compiled logical inputs')
        record = assumptions.kernel_replay({'Good': 'g'}, self.toolchain, '', cache, frozenset({'Good'}))
        self.assertEqual((record['reused'], self.checked()), ([], ['Good']))
        self.calls.unlink()
        module.write_bytes(b'changed compiled logical inputs')
        record = assumptions.kernel_replay({'Good': 'g'}, self.toolchain, '', cache, frozenset({'Good'}))
        self.assertEqual((record['reused'], self.checked()), ([], ['Good']))
        stable = assumptions.toolchain_runtime_sha256(self.toolchain)
        module.with_name('Init.olean.hash').write_bytes(b'mutable hash metadata')
        self.assertEqual(stable, assumptions.toolchain_runtime_sha256(self.toolchain))

    def test_runtime_digest_binds_symlink_targets_and_link_identity(self):
        library = self.toolchain / 'shared/libleanshared.dylib'
        library.parent.mkdir(parents=True)
        library.write_bytes(b'runtime')
        alias = library.with_name('other.dylib')
        alias.write_bytes(library.read_bytes())
        link = self.toolchain / 'lib/current'
        link.parent.mkdir()
        link.symlink_to('../shared', target_is_directory=True)
        file_link = library.parent / 'selected.dylib'
        file_link.symlink_to(library.name)
        first = assumptions.toolchain_runtime_sha256(self.toolchain)
        self.assertEqual(first, assumptions.toolchain_runtime_sha256(self.toolchain))
        import shutil
        with tempfile.TemporaryDirectory() as other:
            copied = Path(other) / 'toolchain'
            shutil.copytree(self.toolchain, copied, symlinks=True)
            self.assertEqual(first, assumptions.toolchain_runtime_sha256(copied))
        file_link.unlink()
        file_link.symlink_to(alias.name)
        self.assertNotEqual(first, assumptions.toolchain_runtime_sha256(self.toolchain))
        second = assumptions.toolchain_runtime_sha256(self.toolchain)
        alias.write_bytes(b'changed target bytes')
        self.assertNotEqual(second, assumptions.toolchain_runtime_sha256(self.toolchain))
        alias.unlink()
        with self.assertRaisesRegex(ValueError, 'missing.*symlink'):
            assumptions.toolchain_runtime_sha256(self.toolchain)

    def test_runtime_loader_overlays_fail_closed(self):
        from unittest.mock import patch
        with patch.dict(os.environ, {'LD_LIBRARY_PATH': '/external/runtime'}):
            with self.assertRaisesRegex(ValueError, 'loader overlay'):
                assumptions.toolchain_runtime_sha256(self.toolchain)


class FreshnessTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.olean = Path(self.temp.name) / 'M.olean'
        self.olean.write_bytes(b'olean')
        self.report = {'freshness': {
            'revision': assumptions.git_revision(), 'lake_trace_check': {'modules': [], 'status': 'up-to-date'},
            'artifacts': [{'module': 'M', 'olean': str(self.olean), 'olean_sha256': assumptions.file_sha256(self.olean),
                           'source': None, 'source_sha256': None}]}}

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

    def test_missing_or_changed_runtime_library_fails_freshness(self):
        from unittest.mock import patch
        toolchain = Path(self.temp.name) / 'toolchain'
        (toolchain / 'bin').mkdir(parents=True)
        for name in ('lean', 'leanchecker'):
            (toolchain / 'bin' / name).write_bytes(name.encode())
        library = toolchain / 'lib/libleanshared.dylib'
        library.parent.mkdir()
        library.write_bytes(b'runtime')
        self.report['freshness']['toolchain_runtime_sha256'] = assumptions.toolchain_runtime_sha256(toolchain)
        with patch.object(assumptions, 'lake_env', return_value=str(toolchain)):
            self.assertEqual(assumptions.verify_artifacts(self.report), 1)
            library.write_bytes(b'changed runtime')
            with self.assertRaisesRegex(ValueError, 'runtime changed'):
                assumptions.verify_artifacts(self.report)
            library.unlink()
            with self.assertRaisesRegex(ValueError, 'runtime changed'):
                assumptions.verify_artifacts(self.report)

    def test_batch_rehashes_before_acceptance_and_cannot_be_reused(self):
        from unittest.mock import patch
        toolchain = Path(self.temp.name) / 'toolchain'
        (toolchain / 'bin').mkdir(parents=True)
        for name in ('lean', 'leanchecker'):
            (toolchain / 'bin' / name).write_bytes(name.encode())
        library = toolchain / 'lib/libleanshared.so'
        library.parent.mkdir()
        library.write_bytes(b'runtime')
        self.report['freshness']['toolchain_runtime_sha256'] = assumptions.toolchain_runtime_sha256(toolchain)
        with patch.object(assumptions, 'lake_env', return_value=str(toolchain)):
            with self.assertRaisesRegex(ValueError, 'changed during artifact verification'):
                with assumptions.artifact_batch() as verify:
                    self.assertEqual(verify(self.report), 1)
                    library.write_bytes(b'changed after report verification')
            with self.assertRaisesRegex(ValueError, 'batch is closed'):
                verify(self.report)


if __name__ == '__main__':
    unittest.main()
