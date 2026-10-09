#!/usr/bin/env python3
"""I07 artifact-manifest regressions on tiny fixture repositories. No Zig, Lake or Lean runs."""
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
spec = importlib.util.spec_from_file_location('artifact_manifest', ROOT / 'scripts/artifact-manifest.py')
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)

PROFILE = {'name': 'abi64-le-v1', 'target_triple': 'x86_64-linux-gnu', 'pointer_bits': 64, 'endian': 'little',
           'abi': 'gnu', 'zig_version': '0.16.0', 'backend': 'stage2_llvm', 'cpu': 'x86_64',
           'features': ['sse', 'sse2'], 'build_mode': 'ReleaseSafe', 'float_mode': 'per-instruction',
           'error_set_bits': 16, 'error_layout': 'type-table', 'error_tracing': False,
           'export_stage': 'analyzed-air'}
PROOFS = """import Proofs.Demo.Gen

/-! theorem not_a_theorem : True := trivial -/
namespace Demo
theorem add_spec : True := trivial
-- theorem commented_out : True := trivial
@[simp] private theorem helper_eq : 1 = 1 := rfl
end Demo

theorem _root_.Top.rooted : True := trivial
theorem toplevel : True := trivial
"""


def air(name, build_mode='ReleaseSafe'):
    return json.dumps({'schema': 12, 'zig_version': '0.16.0', 'target_endian': 'little', 'name': name,
                       'profile': dict(PROFILE, build_mode=build_mode), 'params': [], 'body': []}) + '\n'


def generated(build_mode='ReleaseSafe', body='def add := 1\n'):
    header = {'correspondence': 'model', 'float_semantics': 'ieee',
              'profile': dict(PROFILE, build_mode=build_mode, schema=12)}
    return ('-- air2lean-profile: ' + json.dumps(header, sort_keys=True, separators=(',', ':')) +
            '\nimport ZigLean\n\nnamespace Demo\n' + body + 'end Demo\n')


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.base = Path(self.temporary.name).resolve()
        self.repo = self.base / 'repo'
        files = {
            'scripts/proof-receipt.py': (ROOT / 'scripts/proof-receipt.py').read_text(),
            'scripts/artifact-manifest.py': (ROOT / 'scripts/artifact-manifest.py').read_text(),
            'scripts/normalize-generated.py': (ROOT / 'scripts/normalize-generated.py').read_text(),
            'scripts/normalize-air.py': '# normalizer\n', 'scripts/check.sh': '# check\n',
            'scripts/translate.sh': '# translate\n',
            'Air2Lean.lean': 'import Air2Lean.Emit\n', 'Air2Lean/Emit.lean': '-- emitter\n',
            'examples/demo/demo.zig': 'export fn add(a: u32, b: u32) u32 { return a +% b; }\n',
            'tests/golden/0.16.0/demo/air/demo.add.json': air('demo.add'),
            'tests/golden/0.16.0/demo/air/demo.sub.json': air('demo.sub'),
            'Proofs/Demo/Gen.lean': generated(), 'Proofs/Demo/Proofs.lean': PROOFS,
            'ZigLean.lean': 'import ZigLean.Basic\n', 'ZigLean/Basic.lean': 'def Zig.Result := Id\n',
            'zig-patch/versions.toml': '["0.16.0"]\nurl = "https://example.invalid/zig.tar.xz"\n'
                                       'sha256 = "%s"\nhook = "0.16.0/hook.patch"\nllvm = "21"\n' % ('ab' * 32),
            'zig-patch/0.16.0/hook.patch': '+ hook\n', 'zig-patch/air-json/json.zig': '// exporter\n',
            'zig-patch/build.sh': '# build\n', 'zig-patch/lock.sh': '# lock\n',
            'lean-toolchain': 'leanprover/lean4:v4.34.0\n', 'lakefile.toml': 'name = "demo"\n',
            'lake-manifest.json': '{"packages": [], "version": 7}\n',
        }
        for name, text in files.items():
            path = self.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        self.git('init', '-q')
        # No detached auto-gc/maintenance: it can still be writing objects/ when tearDown removes the repo.
        for key, value in (('gc.auto', '0'), ('maintenance.auto', 'false'), ('core.fsmonitor', 'false')):
            self.git('config', key, value)
        self.commit('fixture')
        self.manifest = self.base / 'manifest.json'

    def tearDown(self):
        self.temporary.cleanup()

    def git(self, *args):
        return subprocess.run(['git', '-C', str(self.repo), '-c', 'user.name=t', '-c', 'user.email=t@t',
                               '-c', 'commit.gpgsign=false', *args], check=True, capture_output=True).stdout

    def commit(self, message):
        self.git('add', '-A')
        self.git('commit', '-q', '-m', message)

    def write(self, name, text, commit=True):
        (self.repo / name).parent.mkdir(parents=True, exist_ok=True)
        (self.repo / name).write_text(text)
        if commit:
            self.commit('edit ' + name)

    def tool(self, *args):
        result = subprocess.run([sys.executable, str(self.repo / 'scripts/proof-receipt.py'), *args],
                                capture_output=True, text=True, cwd=self.base,
                                env=ENV)
        return result.returncode, result.stdout, result.stderr

    def record(self, *extra, path=None):
        code, out, err = self.tool('manifest', str(path or self.manifest), '--example', 'demo',
                                   '--zig-version', '0.16.0', *extra)
        self.assertEqual(code, 0, err)
        return json.loads(out)

    def check(self, *extra, path=None):
        code, out, err = self.tool('check-manifest', str(path or self.manifest), *extra)
        report = json.loads(out)
        self.assertEqual(code, 0 if report['status'] == 'current' else 2, err)
        return report

    def assert_only_stale(self, report, *links):
        self.assertEqual(report['status'], 'stale')
        self.assertEqual(report['stale_links'], list(links))
        return report['links']

    def test_fresh_manifest_is_current_and_chains_every_link(self):
        summary = self.record()
        self.assertEqual(summary['provenance'], 'clean')
        manifest = json.loads(self.manifest.read_text())
        self.assertEqual(manifest['format'], 'air2lean-artifact-manifest-v1')
        self.assertEqual([c['link'] for c in manifest['chain']],
                         ['source', 'compiler_patch', 'air', 'profile', 'translator', 'generated', 'runtime',
                          'toolchain', 'proofs', 'theorems', 'inputs_provenance'])
        self.assertEqual(manifest['manifest_sha256'], manifest['chain'][-1]['chain_sha256'])
        self.assertEqual(manifest['links']['compiler_patch']['value']['pin']['hook'], '0.16.0/hook.patch')
        profile = manifest['links']['profile']['value']
        self.assertEqual((profile['scope'], profile['profile']['build_mode']), ('validated-header', 'ReleaseSafe'))
        self.assertEqual(manifest['links']['theorems']['value']['source_scan'],
                         ['Demo.add_spec', 'Demo.helper_eq', 'Top.rooted', 'toplevel'])
        self.assertEqual(manifest['provenance']['head'], self.git('rev-parse', 'HEAD').decode().strip())
        report = self.check()
        self.assertEqual((report['status'], report['stale_links'], report['problems']), ('current', [], []))

    def test_wrong_source(self):
        self.record()
        self.write('examples/demo/demo.zig', 'export fn add(a: u32, b: u32) u32 { return a -% b; }\n')
        links = self.assert_only_stale(self.check(), 'source')
        self.assertIn('wrong source', links['source']['diagnosis'])
        self.assertEqual(links['source']['changed'], ['examples/demo/demo.zig'])

    def test_added_source_file_is_stale(self):
        self.record()
        self.write('examples/demo/extra.zig', 'pub const x = 1;\n')
        self.assertEqual(self.assert_only_stale(self.check(), 'source')['source']['added'],
                         ['examples/demo/extra.zig'])

    def test_wrong_profile_consistent_reexport(self):
        self.record()
        for name in ('add', 'sub'):
            (self.repo / ('tests/golden/0.16.0/demo/air/demo.%s.json' % name)).write_text(air('demo.' + name, 'ReleaseFast'))
        self.write('Proofs/Demo/Gen.lean', generated('ReleaseFast'))
        report = self.check()
        links = self.assert_only_stale(report, 'air', 'profile', 'generated')
        self.assertIn('wrong profile', links['profile']['diagnosis'])
        self.assertTrue(links['profile']['value_changed'])

    def test_profile_mismatch_between_air_and_generated(self):
        self.record()
        self.write('tests/golden/0.16.0/demo/air/demo.add.json', air('demo.add', 'ReleaseFast'))
        self.write('tests/golden/0.16.0/demo/air/demo.sub.json', air('demo.sub', 'ReleaseFast'))
        links = self.assert_only_stale(self.check(), 'air', 'profile')
        self.assertIn('Gen.lean profile header differs', links['profile']['error'])

    def test_edited_generated_lean(self):
        self.record()
        self.write('Proofs/Demo/Gen.lean', generated(body='def add := 2\n'))
        links = self.assert_only_stale(self.check(), 'generated')
        self.assertIn('edited or regenerated Gen.lean', links['generated']['diagnosis'])
        self.assertEqual(links['generated']['changed'], ['Proofs/Demo/Gen.lean'])

    def test_changed_runtime_semantics(self):
        self.record()
        self.write('ZigLean/Basic.lean', 'def Zig.Result := Option\n')
        links = self.assert_only_stale(self.check(), 'runtime')
        self.assertIn('changed runtime semantics', links['runtime']['diagnosis'])

    def test_changed_compiler_patch_toolchain_and_translator(self):
        self.record()
        self.write('zig-patch/0.16.0/hook.patch', '+ other hook\n')
        self.assertIn('compiler patch', self.assert_only_stale(self.check(), 'compiler_patch')
                      ['compiler_patch']['diagnosis'])
        self.write('lean-toolchain', 'leanprover/lean4:v4.35.0\n')
        self.write('Air2Lean/Emit.lean', '-- changed emitter\n')
        links = self.assert_only_stale(self.check(), 'compiler_patch', 'translator', 'toolchain')
        self.assertTrue(links['toolchain']['value_changed'])

    def test_changed_theorems(self):
        self.record()
        self.write('Proofs/Demo/Proofs.lean', PROOFS.replace('theorem toplevel', 'theorem renamed'))
        links = self.assert_only_stale(self.check(), 'proofs', 'theorems')
        self.assertEqual((links['theorems']['theorems_added'], links['theorems']['theorems_removed']),
                         (['renamed'], ['toplevel']))

    def test_dirty_tree_provenance(self):
        self.write('Proofs/Demo/Gen.lean', generated(body='def add := 3\n'), commit=False)
        (self.repo / 'examples/demo/scratch.zig').write_text('// untracked\n')
        self.assertEqual(self.record()['provenance'], 'dirty')
        provenance = json.loads(self.manifest.read_text())['provenance']
        self.assertEqual(provenance['modified_link_paths'], ['Proofs/Demo/Gen.lean'])
        self.assertEqual(provenance['untracked_link_paths'], ['examples/demo/scratch.zig'])
        report = self.check()
        self.assertEqual((report['status'], report['stale_links']), ('stale', []))
        self.assertIn('dirty-tree provenance', report['problems'][0])
        self.assertEqual(self.check('--allow-dirty')['status'], 'current')
        self.commit('commit the dirty state')
        current = self.check('--allow-dirty')['provenance']['current']
        self.assertEqual(current['status'], 'clean')

    def test_deleted_link_file_is_dirty(self):
        self.write('examples/demo/extra.zig', 'pub const x = 1;\n')
        (self.repo / 'examples/demo/extra.zig').unlink()
        self.assertEqual(self.record()['provenance'], 'dirty')
        provenance = json.loads(self.manifest.read_text())['provenance']
        self.assertEqual(provenance['modified_link_paths'], ['examples/demo/extra.zig'])

    def test_expected_identities_detect_proof_for_another_source_or_profile(self):
        self.record()
        manifest = json.loads(self.manifest.read_text())
        source = manifest['links']['source']['sha256']
        profile = manifest['links']['profile']['value']['profile_sha256']
        report = self.check('--expect', 'source=' + source, '--expect', 'profile=' + profile,
                            '--expect', 'zig_version=0.16.0')
        self.assertEqual(report['status'], 'current')
        report = self.check('--expect', 'profile=' + '0' * 64, '--expect', 'zig_version=0.15.2')
        self.assertEqual((report['status'], report['stale_links']), ('stale', []))
        self.assertEqual(len(report['problems']), 2)
        self.assertIn('proof is for another profile', report['problems'][0])

    def test_tampered_manifest_is_invalid(self):
        self.record()
        manifest = json.loads(self.manifest.read_text())
        manifest['links']['generated']['files'][0]['sha256'] = '0' * 64
        self.manifest.unlink()
        self.manifest.write_text(json.dumps(manifest))
        report = self.check()
        self.assertEqual(report['status'], 'invalid')
        self.assertIn('generated was edited', report['problems'][0])
        record = manifest['links']['generated']
        record['sha256'] = r.digest_of({'files': record['files'], 'value': record['value']})
        self.manifest.write_text(json.dumps(manifest))
        self.assertIn('chain was edited', self.check()['problems'][0])

    def rewrite(self, edit):
        manifest = json.loads(self.manifest.read_text())
        edit(manifest)
        self.manifest.unlink()
        self.manifest.write_text(json.dumps(manifest))
        return self.check()

    def test_provenance_and_inputs_are_sealed(self):
        self.write('Proofs/Demo/Gen.lean', generated(body='def add := 3\n'), commit=False)
        self.record()
        report = self.rewrite(lambda m: m['provenance'].update(status='clean'))
        self.assertEqual(report['status'], 'invalid')
        self.assertIn('chain was edited', report['problems'][0])
        report = self.rewrite(lambda m: m['inputs'].update(audit='/elsewhere.json'))
        self.assertIn('chain was edited', report['problems'][0])

    def test_dropped_link_is_invalid(self):
        self.record()
        report = self.rewrite(lambda m: m['links'].pop('runtime'))
        self.assertEqual(report['status'], 'invalid')
        self.assertIn('missing manifest link', report['problems'][0])

    def test_no_clobber_and_receipt_schema_is_not_a_manifest(self):
        self.record()
        code, _, err = self.tool('manifest', str(self.manifest), '--example', 'demo', '--zig-version', '0.16.0')
        self.assertEqual(code, 2)
        self.assertIn('File exists', err)
        receipt = self.base / 'receipt.json'
        receipt.write_text(json.dumps({'schema': 1, 'status': 'audited'}))
        report = self.check(path=receipt)
        self.assertEqual(report['status'], 'invalid')
        self.assertIn('proof receipt schema 1', report['problems'][0])

    def test_existing_receipt_cli_still_dispatches(self):
        code, _, err = self.tool('verify', str(self.base / 'missing-attempt'))
        self.assertEqual(code, 2)
        self.assertIn('proof receipt unavailable/stale', err)

    def test_mixed_air_profiles_are_refused(self):
        self.write('tests/golden/0.16.0/demo/air/demo.sub.json', air('demo.sub', 'ReleaseFast'))
        code, _, err = self.tool('manifest', str(self.manifest), '--example', 'demo', '--zig-version', '0.16.0')
        self.assertEqual(code, 2)
        self.assertIn('2 different profiles', err)
        self.assertFalse(self.manifest.exists())

    def test_compiled_audit_theorems_and_external_air(self):
        audit = self.base / 'audit.json'
        audit.write_text(json.dumps({'status': 'pass', 'theorems': [
            {'name': 'Demo.add_spec', 'module': 'Proofs.Demo.Proofs', 'allowed': True},
            {'name': 'Other.thm', 'module': 'Proofs.Other.Proofs', 'allowed': True}]}))
        fresh = self.base / 'fresh-air'
        shutil.copytree(self.repo / 'tests/golden/0.16.0/demo/air', fresh)
        self.record('--audit', str(audit), '--air-dir', str(fresh))
        manifest = json.loads(self.manifest.read_text())
        self.assertEqual(manifest['links']['theorems']['value']['compiled_audit']['names'], ['Demo.add_spec'])
        self.assertEqual(manifest['provenance']['status'], 'clean')
        self.assertEqual(len(manifest['provenance']['external_link_paths']), 3)
        audit.write_text(json.dumps({'status': 'pass', 'theorems': []}))
        self.assert_only_stale(self.check(), 'theorems')
        (fresh / 'demo.add.json').unlink()
        self.assertEqual(self.check()['links']['air']['removed'], [str(fresh / 'demo.add.json')])

    def test_chained_receipt_attempt(self):
        attempt = self.base / 'attempt'
        attempt.mkdir()
        for name in ('receipt.json', 'plan.json', 'after.json'):
            (attempt / name).write_text('{"schema": 1}\n')
        (attempt / 'audit.json').write_text(json.dumps({'status': 'pass', 'theorems': [
            {'name': 'toplevel', 'module': 'Proofs.Demo.Proofs', 'allowed': True}]}))
        self.record('--receipt', str(attempt))
        manifest = json.loads(self.manifest.read_text())
        self.assertEqual(manifest['chain'][-2]['link'], 'receipt')
        self.assertEqual(manifest['links']['theorems']['value']['compiled_audit']['names'], ['toplevel'])
        self.assertEqual(self.check()['status'], 'current')
        report = self.check('--verify-receipt')  # A fake attempt is never a current proof receipt.
        self.assertIn('chained proof receipt is not current', report['problems'][0])
        (attempt / 'receipt.json').write_text('{"schema": 1, "edited": true}\n')
        self.assert_only_stale(self.check(), 'receipt')

    def native(self, binary=b'\x7fELF native build\n', mode='ReleaseSafe', target='x86_64-linux'):
        (self.base / 'stock').mkdir(exist_ok=True)
        compiler, built = self.base / 'stock/zig', self.base / 'demo-native'
        compiler.write_bytes(b'stock zig 0.16.0\n')
        built.write_bytes(binary)
        return built, ['--native-binary', str(built), '--native-compiler', str(compiler),
                       '--native-compiler-version', '0.16.0', '--native-target', target, '--native-mode', mode,
                       '--native-cpu', 'baseline']

    def test_native_binary_identity(self):
        built, flags = self.native()
        self.record(*flags)
        manifest = json.loads(self.manifest.read_text())
        self.assertEqual(manifest['chain'][-2]['link'], 'native')
        value = manifest['links']['native']['value']
        self.assertEqual(value['binary_sha256'], r.fingerprint(built)['sha256'])
        self.assertEqual(value['source_link_sha256'], manifest['links']['source']['sha256'])
        self.assertEqual(value['profile_agreement'], {'target': True, 'mode': True, 'zig_version': True})
        report = self.check()
        self.assertEqual((report['status'], report['native']['binary_checked']), ('current', False))
        self.assertIn('native binary not supplied', self.check('--require-native-binary')['problems'][0])
        report = self.check('--native-binary', str(built), '--native-compiler', str(self.base / 'stock/zig'),
                            '--require-native-binary')
        self.assertEqual((report['status'], report['native']['binary_checked']), ('current', True))

    def test_native_binary_or_compiler_mismatch_is_stale(self):
        built, flags = self.native()
        self.record(*flags)
        other = self.base / 'other-binary'
        other.write_bytes(b'rebuilt elsewhere\n')
        report = self.check('--native-binary', str(other))
        links = self.assert_only_stale(report, 'native')
        self.assertIn('wrong native binary', links['native']['diagnosis'])
        self.assertTrue(links['native']['value_changed'])
        self.assertIn('not the manifest', report['problems'][0])
        built.write_bytes(b'edited in place\n')
        self.assert_only_stale(self.check('--native-binary', str(built)), 'native')
        compiler = self.base / 'stock/zig'
        compiler.write_bytes(b'another zig\n')
        self.assert_only_stale(self.check('--native-compiler', str(compiler)), 'native')

    def test_native_build_of_another_source_or_profile_is_stale(self):
        built, flags = self.native()
        self.record(*flags)
        self.write('examples/demo/demo.zig', 'export fn add(a: u32, b: u32) u32 { return a *% b; }\n')
        self.assert_only_stale(self.check('--native-binary', str(built)), 'source', 'native')

    def test_native_target_mode_disagreement_is_reported(self):
        _, flags = self.native(mode='ReleaseFast', target='aarch64-macos')
        self.record(*flags)
        report = self.check()
        self.assertEqual((report['status'], report['stale_links']), ('stale', []))
        self.assertIn("['mode', 'target']", report['problems'][0])
        self.assertEqual(self.check('--allow-native-mismatch')['status'], 'current')

    def test_native_inputs_are_validated_and_sealed(self):
        built, flags = self.native()
        code, _, err = self.tool('manifest', str(self.manifest), '--example', 'demo', '--zig-version', '0.16.0',
                                 '--native-binary', str(built))
        self.assertEqual(code, 2)
        self.assertIn('--native-compiler', err)
        (self.base / 'stock/zig-unlocked').write_text('air only\n')
        code, _, err = self.tool('manifest', str(self.manifest), '--example', 'demo', '--zig-version', '0.16.0', *flags)
        self.assertEqual(code, 2)
        self.assertIn('not the AIR-only patched compiler', err)
        (self.base / 'stock/zig-unlocked').unlink()
        self.record(*flags)
        report = self.rewrite(lambda m: m['inputs']['native'].update(binary_sha256='0' * 64))
        self.assertEqual(report['status'], 'invalid')
        report = self.rewrite(lambda m: m['links'].pop('native'))
        self.assertIn('missing manifest link', report['problems'][0])

    def test_manifest_without_native_rejects_native_flags(self):
        self.record()
        built, _ = self.native()
        code, _, err = self.tool('check-manifest', str(self.manifest), '--native-binary', str(built))
        self.assertEqual(code, 2)
        self.assertIn('no chained native build', err)

    def test_relocatable_receipt_inside_repository(self):
        for name in ('receipt.json', 'plan.json', 'after.json'):
            self.write('evidence/receipt/' + name, '{"schema": 2}\n')
        self.write('evidence/receipt/audit.json', json.dumps({'status': 'pass', 'theorems': [
            {'name': 'toplevel', 'module': 'Proofs.Demo.Proofs', 'allowed': True}]}))
        self.record('--receipt', str(self.repo / 'evidence/receipt'))
        manifest = json.loads(self.manifest.read_text())
        self.assertEqual(manifest['inputs']['receipt'], 'evidence/receipt')
        self.assertEqual(manifest['provenance']['status'], 'clean')
        moved = self.base / 'moved'
        shutil.copytree(self.repo, moved)
        result = subprocess.run([sys.executable, str(moved / 'scripts/artifact-manifest.py'), 'check-manifest',
                                 str(self.manifest)], capture_output=True, text=True, env=ENV)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.write('evidence/receipt/after.json', '{"schema": 2, "edited": 1}\n')
        self.assert_only_stale(self.check(), 'receipt')

    def test_standalone_entry_point(self):
        self.record()
        result = subprocess.run([sys.executable, str(self.repo / 'scripts/artifact-manifest.py'),
                                 'check-manifest', str(self.manifest)], capture_output=True, text=True,
                                env=ENV)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_theorem_scan_namespaces(self):
        path = self.base / 'Scan.lean'
        path.write_text('namespace A.B\nnoncomputable section\ntheorem x : True := trivial\nend\nmutual\n'
                        'theorem y : True := trivial\nend\nend A.B\nlemma «odd name» : True := trivial\n')
        self.assertEqual(r.scan_theorems(self.base, [path]), ['A.B.x', 'A.B.y', '«odd name»'])


class RepositoryManifestTests(unittest.TestCase):
    """Record and recheck the real basic example; reads only tracked bytes."""
    def test_basic_example_is_current(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory).resolve() / 'basic.json'
            command = [sys.executable, str(ROOT / 'scripts/proof-receipt.py')]
            created = subprocess.run(command + ['manifest', str(path), '--example', 'basic', '--zig-version',
                                                '0.16.0'], capture_output=True, text=True, env=ENV)
            self.assertEqual(created.returncode, 0, created.stderr)
            checked = subprocess.run(command + ['check-manifest', str(path), '--allow-dirty'],
                                     capture_output=True, text=True, env=ENV)
            self.assertEqual(checked.returncode, 0, checked.stderr)
            manifest = json.loads(path.read_text())
            self.assertIn('tardiness_spec', manifest['links']['theorems']['value']['source_scan'])
            self.assertEqual(manifest['links']['profile']['value']['scope'], 'legacy-or-unannotated')


if __name__ == '__main__':
    unittest.main()
