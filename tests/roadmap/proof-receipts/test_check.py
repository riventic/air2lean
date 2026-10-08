#!/usr/bin/env python3
"""Tiny copied-wrapper tests; no actual guard, helper worker or toolchains."""
import gc
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]


class CheckFailureTests(unittest.TestCase):
    """Exercise a copied wrapper with tiny stubs; no real guard/helper/tool runs."""
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.base = Path(self.temporary.name).resolve()
        self.root = self.base / 'repo'
        self.check = self.root / 'tests/roadmap/proof-receipts/check.sh'
        self.check.parent.mkdir(parents=True)
        self.check.write_bytes((ROOT / 'tests/roadmap/proof-receipts/check.sh').read_bytes())
        scripts = self.root / 'scripts'
        scripts.mkdir()
        self.invocations = 0
        (scripts / 'proof-receipt.py').write_text("""
import json, sys
from pathlib import Path
root = Path(__file__).parent.parent
with (root / 'calls').open('a') as out: print(sys.argv[1], file=out)
if sys.argv[1] == 'prepare':
    Path(sys.argv[2]).mkdir()
    root.joinpath('prepare-argv.json').write_text(json.dumps(sys.argv[1:]))
else: raise SystemExit('unexpected seal/verify/worker call')
""")
        (scripts / 'gen-integrity.py').write_text("""
import os, sys
from pathlib import Path
with (Path(__file__).parent.parent / 'calls').open('a') as out: print('gen-integrity', *sys.argv[1:], file=out)
raise SystemExit(int(os.environ.get('STUB_GEN_STATUS', '0')))
""")
        (scripts / 'build-guard.py').write_text("""
import os, sys
from pathlib import Path
log = Path(sys.argv[sys.argv.index('--log') + 1])
kind = os.environ['STUB_LOG_KIND']
if kind == 'regular': log.write_bytes(b'prefix-excluded' * 701 + bytes(range(256)) * 32)
elif kind == 'symlink':
    target = log.parent / 'secret'
    target.write_bytes(b'not diagnostic log')
    log.symlink_to(target)
elif kind == 'fifo': os.mkfifo(log)
elif kind == 'directory': log.mkdir()
log.parent.joinpath('retained').write_bytes(b'prior evidence')
raise SystemExit(int(os.environ['STUB_GUARD_STATUS']))
""")
        self.external_guard = self.base / 'reviewed-guard.py'
        self.external_guard.write_bytes((scripts / 'build-guard.py').read_bytes())
        self.tail = bytes(range(256)) * 32

    def tearDown(self):
        self.temporary.cleanup()
        gc.collect()

    def run_stub(self, kind, status, shell='/bin/bash', modules=('Proofs.One',), external=True):
        self.invocations += 1
        attempt = self.base / ('attempt-' + str(self.invocations))
        guard = self.external_guard if external else self.root / 'scripts/build-guard.py'
        options = ['--guard', str(guard), '--guard-sha256', '0' * 64] if external else []
        environment = dict(os.environ, STUB_LOG_KIND=kind, STUB_GUARD_STATUS=str(status),
                           PATH=str(Path(sys.executable).parent) + os.pathsep + os.defpath,
                           AIR2LEAN_BUILD_LOCK=str(self.base / 'mock-lock'), PYTHONDONTWRITEBYTECODE='1')
        result = subprocess.run([shell, str(self.check), *options, str(attempt),
                                 str(self.base / 'mock-toolchain'), 'mock-failed-audit', *modules],
                                env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=5)
        notice = ('proof receipt incomplete: guarded audit exited ' + str(status) +
                  '; retaining ' + str(attempt) + '\n').encode()
        self.assertEqual(result.returncode, status, result.stderr.decode(errors='replace'))
        self.assertEqual(result.stdout, b'')
        self.assertEqual((self.root / 'calls').read_text().splitlines(), ['gen-integrity attest', 'prepare'])
        expected = ['prepare', str(attempt), '--toolchain', str(self.base / 'mock-toolchain'),
                    '--profile', 'mock-failed-audit', '--lock', str(self.base / 'mock-lock')]
        for module in modules: expected += ['--module', module]
        expected += ['--guard', str(guard)]
        if external: expected += ['--guard-sha256', '0' * 64]
        self.assertEqual(json.loads((self.root / 'prepare-argv.json').read_text()), expected)
        self.assertFalse((attempt / 'receipt.json').exists())
        self.assertEqual((attempt / 'retained').read_bytes(), b'prior evidence')
        (self.root / 'calls').unlink()
        return attempt, result.stderr, notice

    def test_failed_wrapper_bounded_log_tail_and_exact_status(self):
        for status in (2, 37, 130):
            with self.subTest(status=status):
                attempt, stderr, notice = self.run_stub('regular', status)
                self.assertEqual(stderr, notice + self.tail)
                self.assertEqual(len(stderr) - len(notice), 8192)
                self.assertEqual((attempt / 'guard.log').read_bytes(), b'prefix-excluded' * 701 + self.tail)

    def test_failed_wrapper_skips_absent_and_nonregular_logs(self):
        for kind in ('absent', 'symlink', 'fifo', 'directory'):
            with self.subTest(kind=kind):
                attempt, stderr, notice = self.run_stub(kind, 37)
                self.assertEqual(stderr, notice)
                if kind == 'symlink':
                    self.assertTrue((attempt / 'guard.log').is_symlink())
                    self.assertEqual((attempt / 'secret').read_bytes(), b'not diagnostic log')

    def test_stale_generated_module_refuses_before_prepare(self):
        attempt = self.base / 'attempt-stale'
        environment = dict(os.environ, STUB_GEN_STATUS='1', STUB_LOG_KIND='regular', STUB_GUARD_STATUS='0',
                           PATH=str(Path(sys.executable).parent) + os.pathsep + os.defpath,
                           AIR2LEAN_BUILD_LOCK=str(self.base / 'mock-lock'), PYTHONDONTWRITEBYTECODE='1')
        result = subprocess.run(['/bin/bash', str(self.check), str(attempt), str(self.base / 'mock-toolchain'),
                                 'mock-stale-generated'], env=environment, capture_output=True, timeout=5)
        self.assertEqual(result.returncode, 1, result.stderr.decode(errors='replace'))
        self.assertEqual((self.root / 'calls').read_text().splitlines(), ['gen-integrity attest'])
        self.assertFalse(attempt.exists())

    def test_wrapper_empty_arrays_and_quoted_arguments_across_bash(self):
        shells = ['/bin/bash']
        preferred = shutil.which('bash')
        if preferred and Path(preferred).resolve() != Path('/bin/bash').resolve():
            shells.append(preferred)
        for shell in shells:
            for external, modules, status in [(False, (), 2), (True, (), 37),
                    (False, ('Proofs.One', 'Proofs.Two'), 130), (True, ('Proofs.One', 'Proofs.Two'), 37)]:
                with self.subTest(shell=shell, external=external, modules=modules):
                    _, stderr, notice = self.run_stub('regular', status, shell, modules, external)
                    self.assertEqual(stderr, notice + self.tail)


if __name__ == '__main__':
    result = unittest.main(exit=False).result
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    peak_bytes = peak if sys.platform == 'darwin' else peak * 1024
    print('offline peak RSS bytes:', peak_bytes)
    if peak_bytes > 32 * 1024 * 1024:
        raise SystemExit('offline test RSS exceeded 32 MiB')
    if not result.wasSuccessful():
        raise SystemExit(1)
