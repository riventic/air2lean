#!/usr/bin/env python3
"""Offline CI adapter tests with tiny filesystem/compiler-dir and command stubs."""
import gc
import importlib.util
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
START = '# BEGIN proof receipt compiler stash'
END = '# END proof receipt compiler stash'


class StashTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.base = Path(self.temporary.name).resolve()
        self.repo, self.temp, self.bin = [self.base / name for name in ('repo', 'runner-temp', 'bin')]
        for path in (self.repo, self.temp, self.bin): path.mkdir()
        self.originals = {}
        for name in ('host-zig', 'zig-air-0.16.0'):
            path = self.repo / name
            (path / 'lib/libc/darwin').mkdir(parents=True)
            (path / 'lib/libc/darwin/SDKSettings.json').write_text(name)
            (path / 'compiler').write_bytes(name.encode())
            (path / 'compiler').chmod(0o700)
            self.originals[name] = self.snapshot(path)
        self.stub('git', """
import os, sys
from pathlib import Path
assert sys.argv[1:] == ['-C', os.environ['STUB_REPO'], 'ls-files', '-z', '--', 'host-zig', 'zig-air-0.16.0']
if os.environ['STUB_MODE'] == 'tracked': sys.stdout.buffer.write(b'host-zig/tracked' + bytes([0]))
""")
        self.stub('mv', """
import json, os, sys
from pathlib import Path
assert sys.argv[1:4] == ['-T', '--no-clobber', '--']
src, dst = map(Path, sys.argv[4:])
root = Path(os.environ['STUB_REPO'])
with (root / 'moves').open('a') as out: print(json.dumps([str(src), str(dst)]), file=out)
if os.environ['STUB_MODE'] == 'partial' and src == root / 'zig-air-0.16.0': raise SystemExit(11)
if not dst.exists() and not dst.is_symlink(): src.rename(dst)
""")
        self.stub('receipt-wrapper', """
import os
from pathlib import Path
root = Path(os.environ['STUB_REPO'])
assert not (root / 'host-zig').exists() and not (root / 'zig-air-0.16.0').exists()
root.joinpath('called').write_text('both compiler roots absent before receipt prepare/worker')
if os.environ['STUB_MODE'] in ('collision', 'failure-collision'):
    root.joinpath('host-zig').mkdir()
    root.joinpath('host-zig/new-owner').write_text('do not overwrite')
if root.joinpath('untracked.lean').exists(): raise SystemExit(2)
raise SystemExit(17 if os.environ['STUB_MODE'] in ('failure', 'failure-collision') else 0)
""")

    def tearDown(self):
        self.temporary.cleanup()
        gc.collect()

    def stub(self, name, source):
        path = self.bin / name
        path.write_text('#!' + str(Path(sys.executable).resolve()) + '\n' + source)
        path.chmod(0o700)

    def snapshot(self, path):
        return {str(p.relative_to(path)): (p.read_bytes(), p.stat().st_mode & 0o777)
                for p in path.rglob('*') if p.is_file()}

    def run_adapter(self, mode):
        source = (ROOT / '.github/workflows/ci.yml').read_text()
        self.assertEqual((source.count(START), source.count(END)), (1, 1))
        block = source[source.index(START):source.index(END) + len(END)]
        lines = block.splitlines()
        block = lines[0] + '\n' + '\n'.join(line[10:] for line in lines[1:]) + '\n'
        script = self.base / 'adapter.sh'
        script.write_text('set -euo pipefail\n' + block + 'receipt-wrapper\n')
        env = dict(os.environ, repo_root=str(self.repo), temp_root=str(self.temp),
                   STUB_REPO=str(self.repo), STUB_MODE=mode, PYTHONDONTWRITEBYTECODE='1',
                   PATH=str(self.bin) + os.pathsep + str(Path(sys.executable).parent) + os.pathsep + os.defpath)
        result = subprocess.run(['/bin/bash', str(script)], env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, timeout=5)
        stashes = list(self.temp.iterdir())
        self.assertEqual(len(stashes), 1)
        self.assertEqual(stashes[0].resolve(), stashes[0])
        return result, stashes[0]

    def assert_restored(self):
        for name in self.originals: self.assertEqual(self.snapshot(self.repo / name), self.originals[name])

    def test_success_and_failure_restore_compiler_bytes_and_modes(self):
        for mode, status in (('success', 0), ('failure', 17)):
            with self.subTest(mode=mode):
                result, stash = self.run_adapter(mode)
                self.assertEqual(result.returncode, status, result.stderr)
                self.assertTrue((self.repo / 'called').is_file())
                self.assert_restored()
                self.assertEqual(list(stash.iterdir()), [])
                # Each root moved out once and back once; paths/caches are restored.
                self.assertEqual(len((self.repo / 'moves').read_text().splitlines()), 4)
                (self.repo / 'moves').unlink()
                (self.repo / 'called').unlink()
                stash.rmdir()

    def test_partial_move_restores_completed_move_without_calling_receipt(self):
        result, stash = self.run_adapter('partial')
        self.assertEqual(result.returncode, 11, result.stderr)
        self.assertFalse((self.repo / 'called').exists())
        self.assert_restored()
        self.assertEqual(list(stash.iterdir()), [])

    def test_restore_collision_keeps_both_owners_and_never_reports_success(self):
        result, stash = self.run_adapter('collision')
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn(b'restore collision', result.stderr)
        self.assertEqual((self.repo / 'host-zig/new-owner').read_text(), 'do not overwrite')
        self.assertEqual(self.snapshot(stash / 'host-zig'), self.originals['host-zig'])
        self.assertEqual(self.snapshot(self.repo / 'zig-air-0.16.0'), self.originals['zig-air-0.16.0'])

    def test_failure_status_survives_restore_collision(self):
        result, stash = self.run_adapter('failure-collision')
        self.assertEqual(result.returncode, 17, result.stderr)
        self.assertIn(b'restore collision', result.stderr)
        self.assertEqual(self.snapshot(stash / 'host-zig'), self.originals['host-zig'])

    def test_tracked_root_is_rejected_before_moves(self):
        result, stash = self.run_adapter('tracked')
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn(b'contain tracked files', result.stderr)
        self.assertFalse((self.repo / 'moves').exists())
        self.assertFalse((self.repo / 'called').exists())
        self.assert_restored()
        self.assertEqual(list(stash.iterdir()), [])

    def test_missing_symlink_and_nondirectory_roots_are_rejected(self):
        root = self.repo / 'host-zig'
        saved = self.base / 'saved-host'
        root.rename(saved)
        for kind in ('missing', 'symlink', 'file'):
            with self.subTest(kind=kind):
                if kind == 'symlink': root.symlink_to(saved, target_is_directory=True)
                elif kind == 'file': root.write_text('not a compiler directory')
                result, stash = self.run_adapter('success')
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn(b'must be a physical directory', result.stderr)
                self.assertFalse((self.repo / 'moves').exists())
                self.assertFalse((self.repo / 'called').exists())
                self.assertEqual(list(stash.iterdir()), [])
                stash.rmdir()
                if kind != 'missing': root.unlink()
        saved.rename(root)
        self.assert_restored()

    def test_other_untracked_source_is_not_stashed_and_remains_rejected(self):
        source = self.repo / 'untracked.lean'
        source.write_text('unowned source input')
        result, stash = self.run_adapter('success')
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertEqual(source.read_text(), 'unowned source input')
        self.assert_restored()
        self.assertEqual(list(stash.iterdir()), [])
        # Independently exercise the unchanged actual receipt context policy with mock Git.
        spec = importlib.util.spec_from_file_location('receipt_test_fixture', ROOT / 'tests/roadmap/proof-receipts/test_receipt.py')
        fixture = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(fixture)
        case = fixture.ReceiptTests()
        case.setUp()
        try:
            original = case.git
            def git(*args):
                if args == ('ls-files', '--others', '--exclude-standard', '-z'):
                    return b'untracked.lean\0'
                return original(*args)
            with fixture.mock.patch.object(fixture.r, 'git', git), self.assertRaisesRegex(ValueError,
                    '^untracked build input: untracked.lean$'):
                fixture.r.context(case.plan)
        finally:
            case.tearDown()


if __name__ == '__main__':
    result = unittest.main(exit=False).result
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    peak_bytes = peak if sys.platform == 'darwin' else peak * 1024
    print('offline CI stash peak RSS bytes:', peak_bytes)
    if peak_bytes > 32 * 1024 * 1024: raise SystemExit('offline test RSS exceeded 32 MiB')
    if not result.wasSuccessful(): raise SystemExit(1)
