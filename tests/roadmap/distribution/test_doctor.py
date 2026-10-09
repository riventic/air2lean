#!/usr/bin/env python3
"""Doctor regressions (scripts/doctor.sh, scripts/doctor.py). Every tool is a fake; no downloads."""
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
FILES = ('scripts/doctor.sh', 'scripts/doctor.py', 'scripts/compat.py', 'scripts/workflow-common.sh',
         'scripts/translate.sh', 'scripts/local-ci.sh', 'scripts/clean-env.sh', 'compatibility.json',
         'lean-toolchain', 'tests/diff/lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
         'zig-patch/versions.toml', 'zig-patch/lock.sh', '.github/workflows/ci.yml',
         'Air2Lean/Air/Profile.lean', 'Dockerfile.clean-env', 'tutorials/first-proof/Main.lean')
# Every listed version's hook, copied when present (another track may add a version's hook later).
FILES += tuple('zig-patch/' + e['hook'] for e in
               json.loads((ROOT / 'compatibility.json').read_text())['zig']['versions'])
TOOLCHAIN = (ROOT / 'lean-toolchain').read_text().strip()
FAKE = r'''#!/usr/bin/env python3
import os, pathlib, sys
name = pathlib.Path(sys.argv[0]).name
args = sys.argv[1:]
if name == 'elan':
    if os.environ.get('MOCK_ELAN') == 'broken': sys.exit(3)
    print(os.environ.get('MOCK_TOOLCHAINS', ''))
elif name == 'docker':
    if os.environ.get('MOCK_DOCKER') == 'down':
        print('Cannot connect to the Docker daemon', file=sys.stderr); sys.exit(1)
    print('27.0.0 x86_64')
else:
    assert args == ['version'], args
    marker = pathlib.Path(sys.argv[0]).with_suffix('.version')
    print(marker.read_text().strip() if marker.exists() else '0.16.0')
'''


def write_tool(path, version=None):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(FAKE)
    path.chmod(0o755)
    if version:
        path.with_suffix('.version').write_text(version)


class Doctor(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='air2lean doctor ')
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.repo = self.base / 'repo'
        for rel in FILES:
            if rel.endswith('/hook.patch') and not (ROOT / rel).exists():
                continue
            (self.repo / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / rel, self.repo / rel)
        self.bin = self.base / 'bin'
        write_tool(self.bin / 'elan')
        write_tool(self.bin / 'docker')
        write_tool(self.bin / 'stock-zig')
        self.env = {'PATH': str(self.bin) + os.pathsep + '/usr/bin:/bin', 'HOME': str(self.base),
                    'AIR2LEAN_PYTHON': sys.executable, 'AIR2LEAN_ZIG': str(self.bin / 'stock-zig'),
                    'AIR2LEAN_DOCKER': str(self.bin / 'docker'), 'MOCK_TOOLCHAINS': TOOLCHAIN + ' (default)'}

    def patched(self, version='0.16.0', lock=True, reported=None):
        """A fake patched compiler installed like build.sh: locked by the real lock.sh."""
        prefix = self.repo / ('zig-air-' + version)
        write_tool(prefix / 'bin/zig', reported or version)
        if lock:
            subprocess.run(['bash', str(self.repo / 'zig-patch/lock.sh'), str(prefix)], check=True,
                           stderr=subprocess.DEVNULL)
            (prefix / 'bin/zig-unlocked.version').write_text(reported or version)
        return prefix

    def doctor(self, *args, expected=None, env=None):
        result = subprocess.run(['bash', str(self.repo / 'scripts/doctor.sh'), '--json'] + list(args),
                                cwd=self.base, env=dict(self.env, **(env or {})), universal_newlines=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        report = json.loads(result.stdout)
        self.assertEqual(report['exit_code'], result.returncode)
        if expected is not None:
            self.assertEqual(result.returncode, expected, result.stdout)
        self.assertEqual(report['schema'], 'air2lean-doctor/1')
        for check in report['checks']:
            self.assertIn(check['status'], ('ok', 'note', 'warn', 'fail', 'skip'))
            self.assertTrue(check['id'] and check['message'])
            if check['status'] == 'fail':
                self.assertTrue(check.get('hint'), check)
        return report

    def check(self, report, cid):
        return next(c for c in report['checks'] if c['id'] == cid)

    def test_ready_with_locked_compiler(self):
        self.patched()
        report = self.doctor(expected=0)
        self.assertEqual(report['ready'], {'proofs': True, 'translate': True})
        self.assertEqual(self.check(report, 'patched-zig-0.16.0')['details']['lock'], 'locked')
        self.assertEqual(self.check(report, 'metadata')['status'], 'ok')
        self.assertEqual(self.check(report, 'stock-zig')['status'], 'ok')
        self.assertEqual(self.check(report, 'docker')['status'], 'ok')
        for cid in ('host', 'elan', 'lean-toolchain', 'proof-build', 'translator',
                    'bootstrap-tools', 'disk', 'memory'):
            self.check(report, cid)
        self.assertEqual(self.check(report, 'patched-zig-0.15.2')['status'], 'skip')

    def test_proofs_only_without_zig(self):
        os.unlink(self.bin / 'stock-zig')
        report = self.doctor('--require', 'proofs', expected=0)
        self.assertEqual(report['ready'], {'proofs': True, 'translate': False})
        missing = self.check(report, 'patched-zig-0.16.0')
        self.assertEqual(missing['status'], 'fail')
        self.assertIn('zig-patch/build.sh 0.16.0', missing['hint'])
        self.assertEqual(self.check(report, 'stock-zig')['status'], 'note')
        self.assertEqual(self.doctor(expected=1)['ready']['translate'], False)

    def test_missing_elan_and_toolchain(self):
        os.unlink(self.bin / 'elan')
        report = self.doctor('--require', 'proofs', expected=1)
        self.assertIn('install elan', self.check(report, 'elan')['hint'])
        write_tool(self.bin / 'elan')
        report = self.doctor('--require', 'proofs', expected=1, env={'MOCK_TOOLCHAINS': 'other (default)'})
        self.assertEqual(self.check(report, 'lean-toolchain')['hint'], 'run: elan toolchain install ' + TOOLCHAIN)
        report = self.doctor('--require', 'proofs', expected=1, env={'MOCK_ELAN': 'broken'})
        self.assertEqual(self.check(report, 'elan')['status'], 'fail')

    def test_toolchain_follows_lean_toolchain(self):
        (self.repo / 'lean-toolchain').write_text('leanprover/lean4:v9.9.9\n')
        report = self.doctor('--require', 'proofs', expected=1)
        self.assertIn('v9.9.9', self.check(report, 'lean-toolchain')['hint'])
        self.assertEqual(self.check(report, 'metadata')['status'], 'warn')
        self.assertTrue(any('lean-toolchain' in e for e in self.check(report, 'metadata')['details']['errors']))

    def test_lock_states(self):
        prefix = self.patched()
        wrapper = prefix / 'bin/zig'
        wrapper.write_text(wrapper.read_text().replace('help |', 'help | build |'))
        stale = self.check(self.doctor(expected=0), 'patched-zig-0.16.0')
        self.assertEqual(stale['details']['lock'], 'stale-lock')
        self.assertIn('zig-patch/lock.sh', stale['hint'])
        write_tool(wrapper, '0.16.0')  # an unwrapped compiler next to zig-unlocked: lock was removed
        broken = self.check(self.doctor(expected=1), 'patched-zig-0.16.0')
        self.assertEqual((broken['status'], broken['details']['lock']), ('fail', 'broken-lock'))
        os.unlink(prefix / 'bin/zig-unlocked')
        llvm = self.check(self.doctor(expected=0), 'patched-zig-0.16.0')
        self.assertEqual((llvm['status'], llvm['details']['lock']), ('warn', 'llvm-or-unlocked'))
        self.assertIn('AIR2LEAN_LLVM=1', llvm['message'])

    def test_rejects_unlocked_path_wrong_version_and_unsupported(self):
        prefix = self.patched()
        report = self.doctor('--zig-air', str(prefix / 'bin/zig-unlocked'), expected=1)
        self.assertIn('safety lock', self.check(report, 'patched-zig-0.16.0')['message'])
        self.patched(reported='0.15.2')
        report = self.doctor(expected=1)
        self.assertIn("expected '0.16.0'", self.check(report, 'patched-zig-0.16.0')['message'])
        report = self.doctor('--zig-version', 'latest', expected=1)
        self.assertIn('0.16.0', self.check(report, 'zig-version')['hint'])

    def test_relative_zig_air_and_other_versions(self):
        self.patched()
        self.patched('0.15.2', lock=False)
        report = self.doctor('--zig-air', 'repo/zig-air-0.16.0/bin/zig', expected=0)
        other = self.check(report, 'patched-zig-0.15.2')
        self.assertEqual((other['status'], other['details']['lock']), ('warn', 'llvm-or-unlocked'))

    def test_docker_states(self):
        self.patched()
        self.assertEqual(self.check(self.doctor(env={'MOCK_DOCKER': 'down'}), 'docker')['status'], 'note')
        self.assertEqual(self.check(self.doctor('--no-docker'), 'docker')['status'], 'skip')
        os.unlink(self.bin / 'docker')
        report = self.doctor(expected=0)
        self.assertEqual(self.check(report, 'docker')['status'], 'note')

    def test_resource_thresholds_from_metadata(self):
        meta = json.loads((self.repo / 'compatibility.json').read_text())
        meta['resources']['translate'] = {'min_disk_gib': 10 ** 9, 'min_memory_gib': 10 ** 9}
        meta['resources']['proofs'] = {'min_disk_gib': 1e-6, 'min_memory_gib': 1e-6}
        (self.repo / 'compatibility.json').write_text(json.dumps(meta))
        self.patched()
        report = self.doctor(expected=0)
        self.assertEqual(self.check(report, 'disk')['status'], 'warn')
        self.assertEqual(self.check(report, 'memory')['status'], 'warn')
        self.assertEqual(self.check(self.doctor('--require', 'proofs'), 'disk')['status'], 'ok')

    def test_missing_metadata_fails_closed(self):
        meta = json.loads((self.repo / 'compatibility.json').read_text())
        meta['resources'].pop('proofs')
        (self.repo / 'compatibility.json').write_text(json.dumps(meta))
        report = self.doctor('--require', 'proofs', expected=1)
        self.assertEqual(self.check(report, 'metadata')['status'], 'fail')
        os.unlink(self.repo / 'compatibility.json')
        report = self.doctor('--require', 'proofs', expected=1)
        self.assertEqual(self.check(report, 'metadata')['status'], 'fail')

    def test_text_output_and_usage(self):
        def run(args, **env):
            return subprocess.run(['bash', str(self.repo / 'scripts/doctor.sh')] + args,
                                  env=dict(self.env, **env), universal_newlines=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        result = run([])
        self.assertEqual(result.returncode, 1)
        self.assertIn('Ready for committed proofs', result.stdout)
        self.assertIn('hint: from the repository, run zig-patch/build.sh 0.16.0', result.stdout)
        self.assertIn('Ready for proofs only', result.stdout)
        for args, code in ((['--help'], 0), (['--typo'], 2), (['--require', 'all'], 2), (['--zig-air'], 2)):
            result = run(args)
            self.assertEqual(result.returncode, code, args)
            self.assertIn('Usage:', result.stdout)
        result = run([], AIR2LEAN_PYTHON='no-such-python')
        self.assertEqual(result.returncode, 1)
        self.assertIn('needs python3', result.stdout)


class HostRules(unittest.TestCase):
    """In-process checks for host-dependent rules a subprocess cannot fake."""

    def setUp(self):
        spec = importlib.util.spec_from_file_location('doctor', ROOT / 'scripts/doctor.py')
        self.mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.mod)

    def selection(self, host, version):
        args = self.mod.parse(['--zig-version', version], {})
        doctor = self.mod.Doctor(ROOT, ROOT, args, {})
        self.assertTrue(doctor.metadata())
        doctor.host_id = host
        return doctor.zig_selection(), doctor.checks[-1]

    def test_linux_only_version(self):
        ok, check = self.selection('aarch64-macos', '0.14.1')
        self.assertFalse(ok)
        self.assertIn('x86_64-linux only', check['message'])
        self.assertIn('0.16.0', check['hint'])
        self.assertTrue(self.selection('x86_64-linux', '0.14.1')[0])
        self.assertTrue(self.selection('aarch64-macos', '0.15.2')[0])

    def test_in_qualification_version_is_noted(self):
        ok, check = self.selection('x86_64-linux', '0.17.0')
        self.assertTrue(ok)
        self.assertEqual((check['id'], check['status']), ('zig-version-status', 'note'))
        self.assertIn('0.16.0', check['hint'])
        ok, check = self.selection('x86_64-linux', '0.16.0')
        self.assertEqual(check['id'], 'zig-version')

    def test_lock_wrapper_matches_lock_sh_output(self):
        with tempfile.TemporaryDirectory() as temp:
            write_tool(Path(temp) / 'bin/zig')
            subprocess.run(['bash', str(ROOT / 'zig-patch/lock.sh'), temp], check=True, stderr=subprocess.DEVNULL)
            self.assertEqual((Path(temp) / 'bin/zig').read_text(), self.mod.lock_wrapper(ROOT))


if __name__ == '__main__':
    unittest.main(verbosity=2)
