#!/usr/bin/env python3
"""I07 edit-one-link and receipt-replay regressions on copies of the committed provenance fixtures.

Each fixture (assurance/provenance on x86_64-linux, assurance/provenance-gap on aarch64-macos) is a
genuine fresh schema-12 export of its source with a schema-3 proof receipt and native-binary identity.
Each case copies the tracked link inputs, changes one link and requires exactly the dependent links
(and no others) to be reported stale; the replay cases change one input of the committed receipt and
require the replay verdict (current, aged for shared Lean/toolchain drift, stale for the fixture's own
files or a tampered audit). No Zig, Lake or Lean runs; `scripts/provenance-evidence.py regenerate` is
the heavy counterpart.
"""
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
ENV = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
ROOT = Path(__file__).resolve().parents[3]
TREES = ('scripts', 'Air2Lean', 'ZigLean', 'zig-patch', 'Proofs/Provenance', 'Proofs/ProvenanceGap',
         'assurance/provenance', 'assurance/provenance-gap')
FILES = ('Air2Lean.lean', 'ZigLean.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
POLICY = ('assurance/policy.json', 'tools/Assurance.lean')
TEMPORARY = None
TEMPLATE = None


def tracked(*paths):
    out = subprocess.run(['git', '-C', str(ROOT), 'ls-files', '-z', '--', *paths], check=True,
                         capture_output=True).stdout.decode()
    return [p for p in out.split('\0') if p]


def setUpModule():
    global TEMPORARY, TEMPLATE
    TEMPORARY = tempfile.TemporaryDirectory()
    TEMPLATE = Path(TEMPORARY.name).resolve() / 'template'
    for name in tracked(*TREES, *FILES, *POLICY):
        target = TEMPLATE / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / name, target, follow_symlinks=False)
    for args in (('init', '-q'), ('config', 'gc.auto', '0'), ('add', '-A'),
                 ('-c', 'user.name=t', '-c', 'user.email=t@t', '-c', 'commit.gpgsign=false',
                  'commit', '-q', '-m', 'copy')):
        subprocess.run(['git', '-C', str(TEMPLATE), *args], check=True, capture_output=True)


def tearDownModule():
    TEMPORARY.cleanup()


class FixtureCases:
    """Tests shared by every committed fixture; a subclass names the fixture's files."""
    NAME = FIX = SOURCE = GEN = PROOFS = TARGET = None
    AIR = THEOREMS = ()

    def setUp(self):
        self.repo = Path(TEMPORARY.name).resolve() / (self.NAME + '-' + self.id().rsplit('.', 1)[-1])
        shutil.copytree(TEMPLATE, self.repo, symlinks=True)

    def tearDown(self):
        shutil.rmtree(self.repo, ignore_errors=True)

    def append(self, name, text):
        with open(self.repo / name, 'a') as stream:
            stream.write(text)

    def run_script(self, *args):
        result = subprocess.run([sys.executable, str(self.repo / 'scripts/provenance-evidence.py'),
                                 '--fixture', self.NAME, *args], capture_output=True, text=True, env=ENV)
        return result, json.loads(result.stdout)

    def check(self, *args):
        result, report = self.run_script('check', *args)
        self.assertEqual(result.returncode, 0 if report['status'] == 'current' else 2, result.stderr)
        return report

    def local(self, expected, aged=()):
        report = self.check('--strict')
        self.assertEqual((report['local_stale_links'], report['aged_links']), (list(expected), list(aged)))
        self.assertEqual(report['status'], 'current' if not expected and not aged else 'stale')
        return report

    def replay(self, *args):
        result, report = self.run_script('replay', *args)
        self.assertEqual(result.returncode, 0 if report['status'] in ('current', 'aged') else 2, result.stderr)
        return report

    def test_unmodified_fixture_is_current_and_receipt_is_schema_three(self):
        report = self.local([])
        self.assertEqual(report['problems'], [])
        manifest = json.loads((self.repo / self.FIX / 'manifest.json').read_text())
        self.assertEqual(manifest['provenance']['status'], 'clean')
        self.assertEqual(json.loads((self.repo / self.FIX / 'receipt/receipt.json').read_text())['schema'], 3)
        air = json.loads((self.repo / self.FIX / 'air' / self.AIR[0]).read_text())
        self.assertEqual(air['schema'], 12)
        self.assertEqual(manifest['links']['profile']['value']['scope'], 'validated-header')
        self.assertEqual([c['link'] for c in manifest['chain']],
                         ['source', 'compiler_patch', 'air', 'profile', 'translator', 'generated', 'runtime',
                          'toolchain', 'proofs', 'theorems', 'receipt', 'native', 'inputs_provenance'])
        self.assertEqual(manifest['links']['native']['value']['target'], self.TARGET)
        names = manifest['links']['theorems']['value']['compiled_audit']['names']
        for theorem in self.THEOREMS:
            self.assertIn(theorem, names)
        self.assertEqual(manifest['links']['theorems']['value']['source_scan'], list(self.THEOREMS))

    def test_source(self):
        self.append(self.SOURCE, '// edited\n')
        self.local(['source', 'native'])

    def test_compiler_patch(self):
        self.append('zig-patch/0.16.0/hook.patch', '+ edited\n')
        self.local([], ['compiler_patch'])
        self.assertEqual(self.check()['status'], 'current')  # aged repository-wide drift only fails --strict

    def test_air(self):
        self.append(self.FIX + 'air/' + self.AIR[0], '\n')
        self.local(['air'])

    def test_profile(self):
        for name in self.AIR:
            path = self.repo / self.FIX / 'air' / name
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
        self.append(self.GEN, '-- edited\n')
        self.local(['generated'])

    def test_runtime(self):
        self.append('ZigLean/Basic.lean', '-- edited\n')
        self.local([], ['runtime'])

    def test_toolchain(self):
        self.append('lakefile.toml', '# edited\n')
        self.local([], ['toolchain'])

    def test_proofs(self):
        self.append(self.PROOFS, '-- edited\n')
        self.local(['proofs'])

    def test_theorems(self):
        self.append(self.PROOFS, '\ntheorem added : True := trivial\n')
        report = self.local(['proofs', 'theorems'])
        self.assertEqual(report['links']['theorems']['theorems_added'], ['added'])

    def test_receipt_and_audit(self):
        self.append(self.FIX + 'receipt/receipt.json', '\n')
        self.local(['receipt'])

    def test_audit_names_are_chained_to_theorems(self):
        self.append(self.FIX + 'receipt/audit.json', '\n')
        self.local(['theorems', 'receipt'])

    def test_after_json_may_be_omitted_but_not_forged(self):
        self.assertFalse((self.repo / self.FIX / 'receipt/after.json').exists())
        (self.repo / self.FIX / 'receipt/after.json').write_text('{}\n')
        self.local(['receipt'])

    def test_native_binary(self):
        other = Path(TEMPORARY.name).resolve() / 'other-binary'
        other.write_bytes(b'not the diff-tested build\n')
        report = self.check('--native-binary', str(other))
        self.assertEqual(report['local_stale_links'], ['native'])
        self.assertIn('not the manifest', ' '.join(report['problems']))

    def test_manifest_and_pins_cannot_be_edited(self):
        path = self.repo / self.FIX / 'manifest.json'
        manifest = json.loads(path.read_text())
        manifest['links']['native']['value']['binary_sha256'] = '0' * 64
        path.write_text(json.dumps(manifest))
        self.assertEqual(self.check()['status'], 'invalid')
        path.write_text(json.dumps(dict(manifest, manifest_sha256='0' * 64)))
        self.assertEqual(self.check()['status'], 'invalid')

    def test_pin_mismatch(self):
        path = self.repo / self.FIX / 'pins.json'
        pins = json.loads(path.read_text())
        pins['profile_sha256'] = '0' * 64
        path.write_text(json.dumps(pins))
        report = self.check()
        self.assertEqual(report['status'], 'stale')
        self.assertIn('proof is for another profile', ' '.join(report['problems']))

    # --- replay of the committed receipt: offline, without its revision or attempt directory

    def test_replay_does_not_need_the_recorded_revision(self):
        report = self.replay('--strict')
        self.assertEqual((report['status'], report['problems']), ('current', []))
        self.assertEqual(report['closure']['changed_local'] + report['closure']['changed_shared'], [])
        self.assertEqual(report['theorems'], list(self.THEOREMS))
        # The copy is a fresh repository: the revision the receipt was produced at does not exist in it.
        self.assertFalse(report['revision']['available'])
        self.assertFalse(report['revision']['needed'])
        self.assertGreater(report['closure']['files'], 10)
        self.assertIn(self.PROOFS.removesuffix('.lean').replace('/', '.'), report['closure']['modules'])
        self.assertIn(self.GEN.removesuffix('.lean').replace('/', '.'), report['closure']['modules'])
        self.assertIn('ZigLean.Basic', report['closure']['modules'])

    def test_replay_own_files_are_stale(self):
        for name in (self.GEN, self.PROOFS):
            with self.subTest(name=name):
                self.append(name, '-- edited\n')
                report = self.replay()
                self.assertEqual((report['status'], report['closure']['changed_local']), ('stale', [name]))
                shutil.copy2(TEMPLATE / name, self.repo / name)

    def test_replay_shared_closure_and_environment_drift_is_aged(self):
        for name in ('ZigLean/Basic.lean', 'lakefile.toml', 'tools/Assurance.lean'):
            with self.subTest(name=name):
                self.append(name, '-- edited\n')
                report = self.replay()
                self.assertEqual((report['status'], report['closure']['changed_shared']), ('aged', [name]))
                self.assertEqual(self.run_script('replay', '--strict')[0].returncode, 2)
                shutil.copy2(TEMPLATE / name, self.repo / name)

    def test_replay_ignores_files_outside_the_import_closure(self):
        self.append('Air2Lean.lean', '-- edited\n')
        self.append('scripts/translate.sh', '# edited\n')
        report = self.replay()
        # Air2Lean.lean and the scripts are not imported by the proofs; replay does not depend on them.
        self.assertNotIn('Air2Lean.lean', report['closure']['changed_shared'])
        self.assertNotIn('scripts/translate.sh', report['closure']['changed_shared'])

    def test_replay_rejects_a_tampered_or_failing_audit(self):
        path = self.repo / self.FIX / 'receipt/audit.json'
        audit = json.loads(path.read_text())
        audit['theorems'][0]['allowed'] = False
        path.write_text(json.dumps(audit))
        report = self.replay()
        self.assertEqual(report['status'], 'stale')
        self.assertTrue(any('violate the policy' in p for p in report['problems']), report['problems'])
        audit['theorems'][0]['allowed'] = True
        audit['status'] = 'fail'
        path.write_text(json.dumps(audit))
        self.assertTrue(any('did not pass' in p for p in self.replay()['problems']))

    def test_replay_rejects_host_local_paths(self):
        path = self.repo / self.FIX / 'receipt/plan.json'
        plan = json.loads(path.read_text())
        plan['lock'] = '/Users/someone/.cache/air2lean/build.lock'
        path.write_text(json.dumps(plan))
        report = self.replay()
        self.assertEqual(report['status'], 'stale')
        self.assertTrue(any('host-local path' in p for p in report['problems']), report['problems'])

    def test_replay_rejects_a_receipt_for_another_module(self):
        path = self.repo / self.FIX / 'receipt/plan.json'
        plan = json.loads(path.read_text())
        plan['modules'] = ['Proofs.Basic.Proofs']
        path.write_text(json.dumps(plan))
        self.assertEqual(self.replay()['status'], 'stale')


class ProvenanceTests(FixtureCases, unittest.TestCase):
    NAME = 'provenance'
    FIX = 'assurance/provenance/'
    SOURCE = 'assurance/provenance/src/provenance.zig'
    GEN, PROOFS = 'Proofs/Provenance/Gen.lean', 'Proofs/Provenance/Proofs.lean'
    TARGET = 'x86_64-linux'
    AIR = ('provenance.add.json', 'provenance.double.json')
    THEOREMS = ('add_eq', 'double_eq', 'double_refl')

    def test_both_fixtures_check_and_replay_together(self):
        for action in ('check', 'replay'):
            result = subprocess.run([sys.executable, str(self.repo / 'scripts/provenance-evidence.py'),
                                     '--fixture', 'all', action], capture_output=True, text=True, env=ENV)
            self.assertEqual(result.returncode, 0, result.stderr)
            reports = json.loads(result.stdout)
            self.assertEqual({n: r['status'] for n, r in reports.items()}, {'gap': 'current', 'provenance': 'current'})


class GapTests(FixtureCases, unittest.TestCase):
    NAME = 'gap'
    FIX = 'assurance/provenance-gap/'
    SOURCE = 'assurance/provenance-gap/src/gap.zig'
    GEN, PROOFS = 'Proofs/ProvenanceGap/Gen.lean', 'Proofs/ProvenanceGap/Proofs.lean'
    TARGET = 'aarch64-macos'
    AIR = ('gap.gap.json', 'gap.within.json')
    THEOREMS = ('gap_eq', 'within_eq')


class ClosureTests(unittest.TestCase):
    def test_imports_after_a_block_comment_and_comments_on_the_line_are_followed(self):
        spec = importlib.util.spec_from_file_location('provenance_evidence', ROOT / 'scripts/provenance-evidence.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'A.lean').write_text('/-! header\nimport Hidden\n-/\n-- note\nimport B -- trailing\nimport Lean.Elab\n\ntheorem t : True := trivial\n')
            (root / 'B.lean').write_text('/- one line -/\nimport C D\ndef b := 1\n')
            (root / 'C.lean').write_text('def c := 1\n')
            (root / 'D.lean').write_text('import A\n')  # an import cycle is tolerated
            files, external = module.lean_closure(root, 'A')
        self.assertEqual(sorted(files), ['A', 'B', 'C', 'D'])
        self.assertEqual(external, ['Lean.Elab'])


if __name__ == '__main__':
    unittest.main()
