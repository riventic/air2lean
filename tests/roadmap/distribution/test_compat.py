#!/usr/bin/env python3
"""Release compatibility metadata regressions (scripts/compat.py). Files only; no tools."""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('compat', ROOT / 'scripts/compat.py')
compat = importlib.util.module_from_spec(spec)
spec.loader.exec_module(compat)
FILES = ('compatibility.json', 'lean-toolchain', 'tests/diff/lean-toolchain', 'lakefile.toml',
         'lake-manifest.json', 'zig-patch/versions.toml', 'zig-patch/toml-get.sh', 'zig-patch/build.sh',
         'zig-patch/lock.sh', 'zig-patch/air-json/json.zig', 'zig-patch/air-json/pointer-offset.zig',
         'scripts/workflow-common.sh', 'scripts/translate.sh', 'scripts/local-ci.sh',
         'scripts/clean-env.sh', '.github/workflows/ci.yml', 'Air2Lean/Air/Profile.lean',
         'Dockerfile.clean-env', 'tutorials/first-proof/Main.lean')
# Every listed version's hook; a hook another track has not merged yet is left for check() to report.
META = json.loads((ROOT / 'compatibility.json').read_text())
HOOKS = tuple('zig-patch/' + e['hook'] for e in META['zig']['versions'])


def entry(data, version):
    return next(e for e in data['zig']['versions'] if e['version'] == version)


class Compat(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for rel in FILES + HOOKS:
            if rel in HOOKS and not (ROOT / rel).exists():
                continue
            (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / rel, self.root / rel)

    def edit(self, rel, old, new):
        path = self.root / rel
        text = path.read_text()
        self.assertIn(old, text, rel)
        path.write_text(text.replace(old, new, 1))

    def meta(self, change):
        path = self.root / 'compatibility.json'
        data = json.loads(path.read_text())
        change(data)
        path.write_text(json.dumps(data))

    def assertDrift(self, needle):
        errors = compat.check(self.root)
        self.assertTrue(any(needle in e for e in errors), errors)

    def test_committed_metadata_is_consistent(self):
        self.assertEqual(compat.check(ROOT), [])
        self.assertEqual(compat.check(self.root), [])
        result = subprocess.run([sys.executable, str(ROOT / 'scripts/compat.py'), 'check', '--json'],
                                stdout=subprocess.PIPE, universal_newlines=True)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(json.loads(result.stdout)['consistent'], True)

    def test_checksum_and_url_drift(self):
        sha = entry(META, '0.16.0')['source']['sha256']
        self.edit('zig-patch/versions.toml', sha, '0' * 64)
        self.assertDrift('zig 0.16.0 source.sha256')
        self.setUp()
        self.meta(lambda d: entry(d, '0.15.2')['ci_host_zig'].update(sha256='A' * 64))
        self.assertDrift('0.15.2 ci_host_zig.sha256')
        self.assertDrift('not a lowercase sha256')
        self.setUp()
        self.meta(lambda d: d['lean']['elan'].update(url='https://example.invalid/elan.tar.gz'))
        self.assertDrift('lean.elan.url')

    def test_toolchain_drift(self):
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.99.0\n')
        self.assertDrift('lean-toolchain')
        self.setUp()
        (self.root / 'tests/diff/lean-toolchain').write_text('leanprover/lean4:v4.99.0\n')
        self.assertDrift('tests/diff/lean-toolchain')

    def test_new_zig_version_must_be_listed_everywhere(self):
        with open(self.root / 'zig-patch/versions.toml', 'a') as f:
            f.write('\n["0.99.0"]\nurl = "u"\nsha256 = "%s"\nhook = "0.16.0/hook.patch"\nllvm = "99"\n' % ('1' * 64))
        self.assertDrift('zig.versions')
        self.setUp()
        self.edit('scripts/workflow-common.sh', ' | 0.14.1)', ')')
        self.assertDrift('scripts/workflow-common.sh')
        self.setUp()
        self.edit('scripts/local-ci.sh', '|0.14.1)', ')')
        self.assertDrift('scripts/local-ci.sh')
        self.setUp()
        self.edit('.github/workflows/ci.yml', '- zig: "0.14.1"', '- zig: "0.13.0"')
        self.assertDrift('ci.yml matrix')

    def test_hosts_default_and_linux_only_rule(self):
        self.meta(lambda d: entry(d, '0.14.1')['hosts'].append('aarch64-macos'))
        self.assertDrift('Linux-only zig versions')
        self.setUp()
        self.meta(lambda d: entry(d, '0.16.0')['hosts'].append('riscv64-linux'))
        self.assertDrift('hosts must be')
        self.setUp()
        self.meta(lambda d: d['zig'].update(default='0.15.2'))
        self.assertDrift('scripts/translate.sh')

    def test_qualification_status(self):
        self.meta(lambda d: entry(d, '0.16.0').pop('status'))
        self.assertDrift('zig 0.16.0 status must be')
        self.setUp()
        self.meta(lambda d: entry(d, '0.16.0').update(status='in-qualification'))
        self.assertDrift("zig.default '0.16.0' is not a qualified version")

    def test_translator_constants(self):
        self.edit('Air2Lean/Air/Profile.lean', 'schema ≤ 12 do', 'schema ≤ 13 do')
        self.assertDrift('air_json_schemas')
        self.setUp()
        self.edit('Air2Lean/Air/Profile.lean', '"abi64-le-v1"', '"abi64-le-v2"')
        self.assertDrift('profiles')
        self.setUp()
        self.edit('scripts/translate.sh', 'x86_64-linux -mcpu=baseline "$input"', 'x86_64-linux -mcpu=native "$input"')
        self.assertDrift('no longer exports with')

    def test_lock_and_recipe_metadata(self):
        self.meta(lambda d: d['air_only_lock'].update(marker='other-lock'))
        self.assertDrift('air_only_lock.marker')
        self.setUp()
        self.meta(lambda d: d['air_only_lock'].update(allowed=['version']))
        self.assertDrift('lacks build-obj')
        self.setUp()
        (self.root / 'scripts/clean-env.sh').unlink()
        self.assertDrift('clean_environment.recipe')
        self.setUp()
        self.edit('Dockerfile.clean-env', 'FROM ubuntu:24.04', 'FROM ubuntu:22.04')
        self.assertDrift('clean_environment.image')
        self.setUp()
        self.meta(lambda d: d['resources'].pop('proofs'))
        self.assertDrift('resources.proofs')

    def test_malformed_inputs_fail_closed(self):
        (self.root / 'compatibility.json').write_text('{')
        self.assertDrift('not JSON')
        self.setUp()
        with open(self.root / 'zig-patch/versions.toml', 'a') as f:
            f.write('broken line\n')
        self.assertDrift('versions.toml unreadable')
        self.setUp()
        self.meta(lambda d: d.update(schema='air2lean-compatibility/0'))
        self.assertDrift('schema')

    def test_release_manifest_checksums(self):
        out = self.root / 'release.json'
        result = subprocess.run([sys.executable, str(ROOT / 'scripts/compat.py'), 'release',
                                 '--root', str(self.root), '--out', str(out)])
        self.assertEqual(result.returncode, 0)
        manifest = json.loads(out.read_text())
        self.assertEqual(manifest['compatibility'], json.loads((self.root / 'compatibility.json').read_text()))
        for rel in ('zig-patch/air-json/json.zig', 'zig-patch/0.14.1/hook.patch', 'lean-toolchain'):
            self.assertEqual(manifest['checksums'][rel], hashlib.sha256((self.root / rel).read_bytes()).hexdigest())
        # Same key scripts/local-ci.sh uses for its compiler cache (without the per-version hook).
        key = hashlib.sha256(b''.join((self.root / rel).read_bytes() for rel in compat.EXPORTER_FILES))
        self.assertEqual(manifest['exporter_fingerprint'], key.hexdigest())
        (self.root / 'lean-toolchain').write_text('leanprover/lean4:v4.99.0\n')
        result = subprocess.run([sys.executable, str(ROOT / 'scripts/compat.py'), 'release', '--root',
                                 str(self.root)], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.assertEqual(result.returncode, 1)


if __name__ == '__main__':
    unittest.main(verbosity=2)
