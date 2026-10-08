"""I01 project.py export: root selection, closure fixed point, root reports, flag preservation (stub compiler)."""
import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
STUB_ZIG = HERE / 'stub-zig.py'
STUB_TRANSLATOR = HERE / 'stub-translator.py'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


project = load('project', REPO / 'scripts/project.py')
export = load('project_export', REPO / 'scripts/project-export.py')
SOURCE = 'pub fn root() u32 { return 1; }\npub inline fn ghost(x: anytype) @TypeOf(x) { return x; }\n'
FLAGS = ['-fllvm', '-OReleaseSafe', '-fno-error-tracing', '-target', 'x86_64-linux-musl', '-mcpu=baseline']


class ExportTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.dir = Path(temp.name)
        for name in ('profile.json', 'src/proj.zig', 'lib.zig', 'patch', 'runtime', 'toolchain'):
            (self.dir / name).parent.mkdir(parents=True, exist_ok=True)
            (self.dir / name).write_text('x')
        (self.dir / 'profile.json').write_text(json.dumps({'name': 'legacy-abi64-le', 'zig_version': '0.16.0'}))
        (self.dir / 'src/proj.zig').write_text(SOURCE)
        self.log = self.dir / 'stub.log'
        self.program = self.dir / 'program.json'
        self.env = {'STUB_LOG': str(self.log), 'STUB_PROGRAM': str(self.program)}
        patcher = mock.patch.dict(os.environ, self.env)
        patcher.start()
        self.addCleanup(patcher.stop)

    def manifest(self, roots, **export_fields):
        spec = {'zig_version': '0.16.0', 'flags': FLAGS,
                'modules': [{'name': 'proj', 'path': 'src/proj.zig', 'deps': ['lib']},
                            {'name': 'lib', 'path': 'lib.zig'}]}
        spec.update(export_fields)
        manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee',
                    'source_closure': ['src/proj.zig'],
                    'components': {'compiler_patch': ['patch'], 'runtime': ['runtime'], 'toolchain': ['toolchain']},
                    'allowed_assumptions': [], 'export': spec,
                    'roots': [{'id': f'r{i}', 'function': fn, 'air': [], 'namespace': 'Proj', 'prefix': 'proj.',
                               'contracts': [], 'goals': [], 'assumptions': [], 'exclusions': []}
                              for i, fn in enumerate(roots)]}
        path = self.dir / 'project.json'
        path.write_text(json.dumps(manifest))
        return path

    def run_export(self, path, program, *args, out=None):
        self.program.write_text(json.dumps(program))
        out = out or self.dir / 'out'
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            code = project.main(['export', str(path), '--out', str(out), '--translator', str(STUB_TRANSLATOR),
                                 '--zig-air', str(STUB_ZIG), *args])
        return code, json.loads(stdout.getvalue()) if code in (0, 1) else None, out

    def logged(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def test_fixed_point_reexports_until_closed(self):
        program = {'proj.root': ['proj.mid'], 'proj.mid': ['lib.leaf__anon_7'], 'lib.leaf__anon_7': [],
                   'proj.unused': []}
        code, report, out = self.run_export(self.manifest(['proj.root']), program)
        self.assertEqual(code, 0, report)
        self.assertEqual(report['status'], 'translated')
        self.assertEqual(report['closure_status'], 'closed')
        its = report['iterations']
        self.assertEqual([i['filter'] for i in its], [['proj.root'], ['proj.mid', 'proj.root'],
                                                       ['lib.leaf', 'proj.mid', 'proj.root']])
        self.assertEqual([i['outcome'] for i in its], ['re-export', 're-export', 'fixed_point'])
        self.assertEqual(its[1]['missing'], ['lib.leaf__anon_7'])
        self.assertEqual(report['roots'][0]['air'], ['lib.leaf__anon_7', 'proj.mid', 'proj.root'])
        generated = json.loads((out / 'r0/Gen.lean').read_text()[3:])
        self.assertEqual(generated['functions'], ['lib.leaf__anon_7', 'proj.mid', 'proj.root'])
        self.assertEqual(generated['args'][-2:], ['--profile', 'legacy-abi64-le'])
        self.assertEqual(json.loads((out / 'export.json').read_text())['status'], 'translated')
        self.assertEqual(sorted(p.name for p in (out / 'air').iterdir()),
                         ['lib.leaf__anon_7.json', 'proj.mid.json', 'proj.root.json'])

    def test_unreferenced_roots_are_reported_and_fail(self):
        code, report, out = self.run_export(self.manifest(['proj.root', 'proj.ghost', 'proj.nowhere']),
                                            {'proj.root': []})
        self.assertEqual(code, 1)
        self.assertEqual(report['status'], 'failed')
        reasons = {r['function']: r['reason'] for r in report['unexported_roots']}
        self.assertEqual(reasons, {'proj.ghost': 'inline_only', 'proj.nowhere': 'not_found'})
        ghost = next(r for r in report['unexported_roots'] if r['function'] == 'proj.ghost')
        self.assertEqual(ghost['source_hints'], [{'module': 'proj', 'line': 2, 'inline': True, 'generic': True}])
        self.assertIn('proj.ghost', report['reason'])
        self.assertFalse(out.exists(), 'nothing is published when a requested root has no AIR')

    def test_generic_and_unreferenced_reasons(self):
        (self.dir / 'src/proj.zig').write_text('pub fn gen(comptime T: type) T { return 0; }\npub fn lone() u32 { return 0; }\n')
        code, report, _ = self.run_export(self.manifest(['proj.gen', 'proj.lone']), {'proj.gen__anon_3': []})
        self.assertEqual(code, 1)
        roots = {r['function']: r for r in report['unexported_roots']}
        self.assertEqual(roots['proj.gen']['reason'], 'generic_instances_only')
        self.assertEqual(roots['proj.gen']['instances'], ['proj.gen__anon_3'])
        self.assertEqual(roots['proj.lone']['reason'], 'unreferenced')

    def test_empty_export_fails(self):
        code, report, out = self.run_export(self.manifest(['proj.root']), {})
        self.assertEqual(code, 1)
        self.assertEqual(report['iterations'][0]['exported'], [])
        self.assertEqual([r['function'] for r in report['unexported_roots']], ['proj.root'])
        self.assertFalse(out.exists())

    def test_flags_modules_options_and_references_are_preserved(self):
        path = self.manifest(['proj.root'], references=['proj.root'],
                             options={'module': 'build_options',
                                      'values': {'fast': {'type': 'bool', 'value': False},
                                                 'lanes': {'type': 'u8', 'value': 4},
                                                 'tag': {'type': '[]const u8', 'value': 'a"b'}}})
        spec = json.loads(path.read_text())
        spec['export']['modules'][1]['deps'] = ['build_options']
        path.write_text(json.dumps(spec))
        other = self.dir / 'other-lib.zig'
        other.write_text('y')
        code, report, _ = self.run_export(path, {'proj.root': []}, '-D', 'fast', '-Dlanes=8',
                                          '--module', f'lib={other}')
        self.assertEqual(code, 0, report)
        entries = self.logged()
        argv = entries[0]['argv']
        self.assertEqual(argv[:2 + len(FLAGS)], ['build-obj', '-fno-emit-bin', *FLAGS])
        modules = argv[2 + len(FLAGS):]
        self.assertEqual(modules[:2], ['--dep', 'proj'])
        self.assertTrue(modules[2].startswith('-Mair2lean_roots='))
        self.assertEqual(modules[3:], ['--dep', 'lib', f'-Mproj={(self.dir / "src/proj.zig").resolve()}',
                                       '--dep', 'build_options', f'-Mlib={other.resolve()}',
                                       modules[-1]])
        self.assertTrue(modules[-1].startswith('-Mbuild_options='))
        texts = {e['module']: e['text'] for e in entries if 'module' in e}
        self.assertIn('_ = &@import("proj").root;', texts['air2lean_roots'])
        self.assertIn('pub const fast: bool = true;', texts['build_options'])
        self.assertIn('pub const lanes: u8 = 8;', texts['build_options'])
        self.assertIn('pub const tag: []const u8 = "a\\"b";', texts['build_options'])
        self.assertEqual(report['flags'], FLAGS)
        self.assertEqual(report['options'], {'fast': True, 'lanes': 8, 'tag': 'a"b'})
        self.assertEqual(entries[0]['cwd'], str(self.dir.resolve()))

    def test_stalled_closure_fails(self):
        code, report, out = self.run_export(self.manifest(['proj.root']), {'proj.root': ['proj.rootHelper']})
        self.assertEqual(code, 1)
        self.assertEqual(report['iterations'][-1]['outcome'], 'stalled')
        self.assertEqual(len(report['iterations']), 1, 'proj.root already covers proj.rootHelper')
        self.assertFalse(out.exists())

    def test_iteration_bound(self):
        program = {'proj.root': ['proj.a'], 'proj.a': ['proj.b'], 'proj.b': []}
        code, report, _ = self.run_export(self.manifest(['proj.root'], max_iterations=2), program)
        self.assertEqual(code, 1)
        self.assertIn('after 2 export iterations', report['reason'])

    def test_compiler_and_translator_failures_publish_nothing(self):
        path = self.manifest(['proj.root'])
        with mock.patch.dict(os.environ, {'STUB_EXIT': '3'}):
            code, report, out = self.run_export(path, {'proj.root': []})
        self.assertEqual((code, report['reason']), (1, 'AIR export failed'))
        self.assertIn('stub compiler failure', report['iterations'][0]['stderr'])
        with mock.patch.dict(os.environ, {'STUB_WARN': '1'}):
            code, report, _ = self.run_export(path, {'proj.root': []})
        self.assertIn('exporter warning', report['reason'])
        for mode in ('fail', 'empty'):
            with mock.patch.dict(os.environ, {'STUB_TRANSLATE': mode}):
                code, report, out = self.run_export(path, {'proj.root': []})
            self.assertEqual((code, report['reason']), (1, 'translation failed'))
            self.assertFalse(out.exists())

    def test_profile_and_version_checks(self):
        profile = json.loads((REPO / 'case-studies/profile-x86_64-linux-musl-releasesafe.json').read_text())
        (self.dir / 'profile.json').write_text(json.dumps(profile))
        path = self.manifest(['proj.root'])
        with mock.patch.dict(os.environ, {'STUB_PROFILE': json.dumps(dict(profile, build_mode='Debug'))}):
            code, report, _ = self.run_export(path, {'proj.root': []})
        self.assertEqual(code, 1)
        self.assertIn('profile differs from the manifest profile', report['reason'])
        with mock.patch.dict(os.environ, {'STUB_PROFILE': json.dumps(profile)}):
            self.assertEqual(self.run_export(path, {'proj.root': []})[0], 0)
        with mock.patch.dict(os.environ, {'STUB_ZIG_VERSION': '0.15.2'}):
            with self.assertRaisesRegex(ValueError, 'reports version'):
                export.run_export(project, path, STUB_ZIG, STUB_TRANSLATOR, self.dir / 'o2')

    def test_source_pins(self):
        path = self.manifest(['proj.root'])
        spec = json.loads(path.read_text())
        spec['export']['modules'][0]['sha256'] = hashlib.sha256(SOURCE.encode()).hexdigest()
        path.write_text(json.dumps(spec))
        self.assertEqual(self.run_export(path, {'proj.root': []})[0], 0)
        (self.dir / 'src/proj.zig').write_text(SOURCE + '// changed\n')
        with self.assertRaisesRegex(ValueError, 'manifest pins'):
            export.run_export(project, path, STUB_ZIG, STUB_TRANSLATOR, self.dir / 'o3')
        self.assertEqual(project.main(['export', str(path), '--out', str(self.dir / 'o4'), '--translator',
                                       str(STUB_TRANSLATOR), '--zig-air', str(STUB_ZIG)]), 2)

    def test_manifest_validation(self):
        bad = [dict(flags=['@args.rsp']), dict(flags=['-femit-bin=x']), dict(flags=['extra.zig']),
               dict(flags=['-Mx=y']), dict(zig_version='0.13.0'), dict(references=['nomodule.f']),
               dict(references=['proj']), dict(max_iterations=0),
               dict(options={'module': 'proj', 'values': {}}),
               dict(options={'module': 'opts', 'values': {'x': {'type': 'f32', 'value': 1}}}),
               dict(options={'module': 'opts', 'values': {'x': {'type': 'bool', 'value': 1}}}),
               dict(modules=[{'name': 'a', 'path': 'a.zig', 'deps': ['missing']}]),
               dict(modules=[{'name': 'a', 'path': 'a.zig', 'sha256': 'XYZ'}])]
        for fields in bad:
            with self.subTest(fields=fields), self.assertRaises(ValueError):
                project.load_manifest(self.manifest(['proj.root'], **fields))
        manifest = json.loads(self.manifest(['proj.root']).read_text())
        del manifest['export']
        (self.dir / 'project.json').write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, 'at least one entry'):
            project.load_manifest(self.dir / 'project.json')

    def test_out_must_be_fresh_or_empty(self):
        out = self.dir / 'out'
        out.mkdir()
        self.assertEqual(self.run_export(self.manifest(['proj.root']), {'proj.root': []}, out=out)[0], 0)
        self.assertEqual(self.run_export(self.manifest(['proj.root']), {'proj.root': []}, out=out)[0], 2)
        code, report, _ = self.run_export(self.manifest(['proj.root']), {'proj.root': ['proj.rootX']}, '--replace', out=out)
        self.assertEqual(code, 1)
        self.assertEqual(json.loads((out / 'r0/Gen.lean').read_text()[3:])['functions'], ['proj.root'],
                         'a failed export keeps the previous artifact')
        program = {'proj.root': ['lib.x'], 'lib.x': []}
        self.assertEqual(self.run_export(self.manifest(['proj.root']), program, '--replace', out=out)[0], 0)
        self.assertEqual(json.loads((out / 'r0/Gen.lean').read_text()[3:])['functions'], ['lib.x', 'proj.root'])
        (out / 'export.json').unlink()
        self.assertEqual(self.run_export(self.manifest(['proj.root']), program, '--replace', out=out)[0], 2)

    def test_committed_manifests_validate(self):
        for name in ('flow-time-project.json', 'pcg64-project.json'):
            manifest = project.load_manifest(REPO / name)[0]
            self.assertTrue(all('sha256' in m for m in manifest['export']['modules'] if m['path'].startswith('/')))


@unittest.skipUnless(os.environ.get('AIR2LEAN_ZIG_AIR') and os.environ.get('AIR2LEAN_TRANSLATOR'),
                     'needs AIR2LEAN_ZIG_AIR (patched Zig 0.16.0) and AIR2LEAN_TRANSLATOR')
class RealCompilerTest(unittest.TestCase):
    """The real patched compiler on an in-repo source: the closure needs two re-exports."""

    def test_examples_basic_closure(self):
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp)
            for name in ('patch', 'runtime', 'toolchain', 'src.zig'):
                (base / name).write_text('x')
            (base / 'profile.json').write_bytes(
                (REPO / 'case-studies/profile-x86_64-linux-musl-releasesafe.json').read_bytes())
            manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee', 'source_closure': ['src.zig'],
                        'components': {'compiler_patch': ['patch'], 'runtime': ['runtime'], 'toolchain': ['toolchain']},
                        'allowed_assumptions': [],
                        'export': {'zig_version': '0.16.0', 'flags': FLAGS,
                                   'modules': [{'name': 'basic', 'path': str(REPO / 'examples/basic/basic.zig')}]},
                        'roots': [{'id': 'total', 'function': 'basic.totalWeightedTardiness', 'air': [],
                                   'namespace': 'Basic', 'prefix': 'basic.', 'contracts': [], 'goals': [],
                                   'assumptions': [], 'exclusions': []}]}
            (base / 'project.json').write_text(json.dumps(manifest))
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                code = project.main(['export', str(base / 'project.json'), '--out', str(base / 'out'),
                                     '--translator', os.environ['AIR2LEAN_TRANSLATOR']])
            report = json.loads(stdout.getvalue())
            self.assertEqual(code, 0, report)
            self.assertEqual([i['outcome'] for i in report['iterations']], ['re-export', 're-export', 'fixed_point'])
            self.assertEqual(report['roots'][0]['air'],
                             ['basic.tardiness', 'basic.totalWeightedTardiness', 'basic.weightedTardiness'])
            self.assertIn('def totalWeightedTardiness', (base / 'out/total/Gen.lean').read_text())


if __name__ == '__main__':
    unittest.main()
