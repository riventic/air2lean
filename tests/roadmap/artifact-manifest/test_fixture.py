#!/usr/bin/env python3
"""I07 edit-one-link regressions on a copy of the committed receipt-chained provenance fixture.

The fixture (assurance/provenance) is a genuine fresh schema-12 export of assurance/provenance/src with
its schema-2 proof receipt and native-binary identity. Each case copies the tracked link inputs,
changes one link and requires exactly the dependent links (and no others) to be reported stale.
No Zig, Lake or Lean runs; `scripts/provenance-evidence.py regenerate` is the heavy counterpart.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ENV = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
ROOT = Path(__file__).resolve().parents[3]
TREES = ('scripts', 'Air2Lean', 'ZigLean', 'zig-patch', 'Proofs/Provenance',
         'assurance/provenance')
FILES = ('Air2Lean.lean', 'ZigLean.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
FIX = 'assurance/provenance/'


def tracked(*paths):
    out = subprocess.run(['git', '-C', str(ROOT), 'ls-files', '-z', '--', *paths], check=True,
                         capture_output=True).stdout.decode()
    return [p for p in out.split('\0') if p]


class FixtureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory()
        cls.template = Path(cls.temporary.name).resolve() / 'template'
        for name in tracked(*TREES, *FILES):
            target = cls.template / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, target, follow_symlinks=False)
        for args in (('init', '-q'), ('config', 'gc.auto', '0'), ('add', '-A'),
                     ('-c', 'user.name=t', '-c', 'user.email=t@t', '-c', 'commit.gpgsign=false',
                      'commit', '-q', '-m', 'copy')):
            subprocess.run(['git', '-C', str(cls.template), *args], check=True, capture_output=True)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def setUp(self):
        self.repo = Path(self.temporary.name).resolve() / self.id().rsplit('.', 1)[-1]
        shutil.copytree(self.template, self.repo, symlinks=True)

    def tearDown(self):
        shutil.rmtree(self.repo, ignore_errors=True)

    def append(self, name, text):
        with open(self.repo / name, 'a') as stream:
            stream.write(text)

    def check(self, *args):
        result = subprocess.run([sys.executable, str(self.repo / 'scripts/provenance-evidence.py'), 'check', *args],
                                capture_output=True, text=True, env=ENV)
        report = json.loads(result.stdout)
        self.assertEqual(result.returncode, 0 if report['status'] == 'current' else 2, result.stderr)
        return report

    def local(self, expected, aged=()):
        report = self.check('--strict')
        self.assertEqual((report['local_stale_links'], report['aged_links']), (list(expected), list(aged)))
        self.assertEqual(report['status'], 'current' if not expected and not aged else 'stale')
        return report

    def test_unmodified_fixture_is_current_and_receipt_is_schema_three(self):
        report = self.local([])
        self.assertEqual(report['problems'], [])
        manifest = json.loads((self.repo / FIX / 'manifest.json').read_text())
        self.assertEqual(manifest['provenance']['status'], 'clean')
        self.assertEqual(json.loads((self.repo / FIX / 'receipt/receipt.json').read_text())['schema'], 3)
        air = json.loads((self.repo / FIX / 'air/provenance.add.json').read_text())
        self.assertEqual(air['schema'], 12)
        self.assertEqual(manifest['links']['profile']['value']['scope'], 'validated-header')
        self.assertEqual([c['link'] for c in manifest['chain']],
                         ['source', 'compiler_patch', 'air', 'profile', 'translator', 'generated', 'runtime',
                          'toolchain', 'proofs', 'theorems', 'receipt', 'native', 'inputs_provenance'])
        names = manifest['links']['theorems']['value']['compiled_audit']['names']
        self.assertIn('add_eq', names)
        self.assertIn('double_eq', names)
        self.assertEqual(manifest['links']['theorems']['value']['source_scan'],
                         ['add_eq', 'double_eq'])

    def test_source(self):
        self.append('assurance/provenance/src/provenance.zig', '// edited\n')
        self.local(['source', 'native'])

    def test_compiler_patch(self):
        self.append('zig-patch/0.16.0/hook.patch', '+ edited\n')
        self.local([], ['compiler_patch'])
        self.assertEqual(self.check()['status'], 'current')  # aged repository-wide drift only fails --strict

    def test_air(self):
        self.append(FIX + 'air/provenance.add.json', '\n')
        self.local(['air'])

    def test_profile(self):
        for name in ('add', 'double'):
            path = self.repo / FIX / ('air/provenance.%s.json' % name)
            air = json.loads(path.read_text())
            air['profile']['build_mode'] = 'ReleaseFast'
            path.write_text(json.dumps(air))
        report = self.check('--strict')
        self.assertEqual(report['local_stale_links'], ['air', 'profile', 'native'])
        self.assertIn('wrong profile', report['links']['profile']['diagnosis'])

    def test_translator(self):
        self.append('Air2Lean.lean', '-- edited\n')
        self.local([], ['translator'])

    def test_generated(self):
        self.append('Proofs/Provenance/Gen.lean', '-- edited\n')
        self.local(['generated'])

    def test_runtime(self):
        self.append('ZigLean/Basic.lean', '-- edited\n')
        self.local([], ['runtime'])

    def test_toolchain(self):
        self.append('lakefile.toml', '# edited\n')
        self.local([], ['toolchain'])

    def test_proofs(self):
        self.append('Proofs/Provenance/Proofs.lean', '-- edited\n')
        self.local(['proofs'])

    def test_theorems(self):
        self.append('Proofs/Provenance/Proofs.lean', '\ntheorem added : True := trivial\n')
        report = self.local(['proofs', 'theorems'])
        self.assertEqual(report['links']['theorems']['theorems_added'], ['added'])

    def test_receipt_and_audit(self):
        self.append(FIX + 'receipt/receipt.json', '\n')
        self.local(['receipt'])

    def test_audit_names_are_chained_to_theorems(self):
        self.append(FIX + 'receipt/audit.json', '\n')
        self.local(['theorems', 'receipt'])

    def test_after_json_may_be_omitted_but_not_forged(self):
        self.assertFalse((self.repo / FIX / 'receipt/after.json').exists())
        (self.repo / FIX / 'receipt/after.json').write_text('{}\n')
        self.local(['receipt'])

    def test_native_binary(self):
        manifest = json.loads((self.repo / FIX / 'manifest.json').read_text())
        self.assertEqual(manifest['links']['native']['value']['target'], 'x86_64-linux')
        other = Path(self.temporary.name).resolve() / 'other-binary'
        other.write_bytes(b'not the diff-tested build\n')
        report = self.check('--native-binary', str(other))
        self.assertEqual(report['local_stale_links'], ['native'])
        self.assertIn('not the manifest', ' '.join(report['problems']))

    def test_manifest_and_pins_cannot_be_edited(self):
        path = self.repo / FIX / 'manifest.json'
        manifest = json.loads(path.read_text())
        manifest['links']['native']['value']['binary_sha256'] = '0' * 64
        path.write_text(json.dumps(manifest))
        self.assertEqual(self.check()['status'], 'invalid')
        path.write_text(json.dumps(dict(manifest, manifest_sha256='0' * 64)))
        self.assertEqual(self.check()['status'], 'invalid')

    def test_pin_mismatch(self):
        path = self.repo / FIX / 'pins.json'
        pins = json.loads(path.read_text())
        pins['profile_sha256'] = '0' * 64
        path.write_text(json.dumps(pins))
        report = self.check()
        self.assertEqual(report['status'], 'stale')
        self.assertIn('proof is for another profile', ' '.join(report['problems']))


if __name__ == '__main__':
    unittest.main()
