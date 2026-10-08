"""I02 dependency closure: synthetic AIR fixtures for every class, plus the committed goldens."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
REPO = Path(__file__).resolve().parents[3]
SCRIPTS = REPO / 'scripts'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


closure = load('dependency_closure', SCRIPTS / 'dependency-closure.py')
project = load('project', SCRIPTS / 'project.py')

FN_PTR, U32, FN, NORET = 0, 1, 2, 3
TYPES = [{'k': 'ptr', 'size': 'one', 'const': True, 'child': 2}, {'k': 'int', 'signed': False, 'bits': 32},
         {'k': 'other', 'name': 'fn (u32) u32'}, {'k': 'noreturn'}]


def call(iid, func, noreturn=False, worker=None):
    callee = {'ty': FN_PTR, 'func': func, 'noreturn': noreturn}
    if worker:
        callee['comptime_fn'] = worker
    return {'id': iid, 'tag': 'call', 'ty': U32, 'callee': callee, 'args': []}


def air(name, body, globals_=None, version='0.16.0'):
    result = {'schema': 11, 'zig_version': version, 'name': name, 'params': [], 'ret': U32,
              'body': [{'id': 0, 'tag': 'arg', 'ty': FN_PTR, 'param': 0}] + body, 'types': TYPES}
    if globals_ is not None:
        result['globals'] = globals_
    return result


def fn_global(func):
    return {'name': func, 'ty': FN, 'const': True, 'threadlocal': False, 'extern': False,
            'init': {'ty': FN, 'func': func, 'noreturn': False}}


def run(functions, roots, version='0.16.0', registry=()):
    index = {f['name']: closure.scan(f) for f in functions}
    c = closure.Closure(index, version, None, registry).run(roots)
    return closure.report(c, roots, ['proj.'], source='src/proj.zig')


def node(result, name):
    return next(n for n in result['functions'] if n['name'] == name)


class ClassTests(unittest.TestCase):
    def test_missing_transitive_callee_reports_exact_fqn_chain_and_filter(self):
        result = run([air('proj.root', [call(1, 'proj.mid')]), air('proj.mid', [call(2, 'lib.deep.leaf')])],
                     ['proj.root'])
        self.assertEqual(result['status'], 'incomplete')
        self.assertEqual(result['missing'], [{'fqn': 'lib.deep.leaf', 'filter_prefix': 'lib.deep.leaf',
            'chain': ['proj.root', 'proj.mid', 'lib.deep.leaf'],
            'references': [{'from': 'proj.mid', 'edge': 'direct_call', 'instruction': 2}]}])
        self.assertEqual(result['filter']['prefixes'], ['lib.deep.leaf', 'proj.'])
        self.assertIn("ZIG_AIR_JSON_FILTER=lib.deep.leaf,proj.", result['reexport'])
        self.assertIn('zig-air-0.16.0/bin/zig build-obj', result['reexport'])

    def test_generic_instance_and_spawn_worker(self):
        result = run([air('proj.root', [call(1, 'proj.gen__anon_77'),
                                        call(2, 'Thread.spawn__anon_9', worker='proj.worker')])], ['proj.root'])
        self.assertEqual(node(result, 'Thread.spawn__anon_9')['kind'], 'std_model')
        missing = {m['fqn']: m for m in result['missing']}
        self.assertEqual(missing['proj.gen__anon_77']['filter_prefix'], 'proj.gen')
        self.assertEqual(missing['proj.worker']['references'][0]['edge'], 'comptime_function_argument')
        self.assertEqual(missing['proj.worker']['chain'], ['proj.root', 'proj.worker'])

    def test_model_boundaries(self):
        extern = {'name': 'proj.device', 'ty': U32, 'const': False, 'threadlocal': False, 'extern': True}
        result = run([air('proj.root', [call(1, 'mem.Allocator.create__anon_3'), call(2, 'ext.hash'),
                                        call(3, "debug.FullPanic((function 'defaultPanic')).outOfBounds", True),
                                        {'id': 4, 'tag': 'load', 'ty': U32, 'args': [{'ty': FN_PTR, 'ptr': {'global': 0, 'off': 0}}]}],
                          [extern])], ['proj.root'], registry=['ext.hash'])
        self.assertEqual(result['status'], 'closed')
        self.assertEqual(sorted((b['name'], b['kind']) for b in result['model_boundaries']), [
            ("debug.FullPanic((function 'defaultPanic')).outOfBounds", 'panic_handler'),
            ('ext.hash', 'registry_binding'), ('mem.Allocator.create__anon_3', 'std_model'),
            ('proj.device', 'extern_initial_state')])

    def test_qualified_indirect_targets(self):
        indirect = {'id': 5, 'tag': 'call', 'ty': U32, 'callee': {'inst': 0}, 'args': []}
        result = run([air('proj.root', [call(1, 'proj.apply')], [fn_global('proj.double')]),
                      air('proj.apply', [indirect]), air('proj.double', [])], ['proj.root'])
        self.assertEqual(result['status'], 'closed')
        self.assertEqual(result['indirect_calls'], [{'function': 'proj.apply', 'instruction': 5, 'fn_type': 'fn (u32) u32',
            'targets': [{'name': 'proj.double', 'class': 'exported'}], 'class': 'qualified'}])
        # The same global target without AIR is a missing qualified target.
        result = run([air('proj.root', [call(1, 'proj.apply')], [fn_global('proj.double')]),
                      air('proj.apply', [indirect])], ['proj.root'])
        self.assertEqual([m['fqn'] for m in result['missing']], ['proj.double'])
        self.assertEqual(result['missing'][0]['references'][0]['edge'], 'global_function_reference')

    def test_unresolvable_boundaries(self):
        indirect = {'id': 5, 'tag': 'call', 'ty': U32, 'callee': {'inst': 0}, 'args': []}
        not_fn = {'id': 6, 'tag': 'call', 'ty': U32, 'callee': {'inst': 7}, 'args': []}
        tls = {'name': 'proj.tls', 'ty': U32, 'const': False, 'threadlocal': True, 'extern': True}
        local = {'name': 'proj.local', 'ty': U32, 'const': False, 'threadlocal': True, 'extern': False,
                 'init': {'ty': U32, 'val': '0'}}
        body = [{'id': 7, 'tag': 'add', 'ty': U32, 'args': [{'inst': 0}, {'inst': 0}]}, indirect, not_fn,
                call(1, 'Io.futexWaitTimeout'), call(2, 'process.exit', True), call(3, 'mem.Allocator.allocSentinel__anon_4'),
                call(4, 'Thread.detach'),
                {'id': 8, 'tag': 'load', 'ty': U32, 'args': [{'ty': FN_PTR, 'ptr': {'global': 0, 'off': 0}}]},
                {'id': 9, 'tag': 'load', 'ty': U32, 'args': [{'ty': FN_PTR, 'ptr': {'global': 1, 'off': 0}}]}]
        result = run([air('proj.root', body, [tls, local], '0.15.2')], ['proj.root'], '0.15.2')
        kinds = sorted((b['kind'], b['target'], b['instruction']) for b in result['unresolvable'])
        self.assertEqual(kinds, [('non_function_pointer_callee', None, 6),
            ('rejected_std_model', 'Io.futexWaitTimeout', None),
            ('runtime_function_pointer', 'fn (u32) u32', 5),
            ('std_model_not_qualified', 'Thread.detach', None),
            ('std_model_not_qualified', 'mem.Allocator.allocSentinel__anon_4', None),
            ('threadlocal_global', 'proj.tls', None),
            ('unmodelled_noreturn_callee', 'process.exit', 2)])
        # C02: defined thread-local storage is embedded like any other global.
        self.assertEqual(next(g for g in result['globals'] if g['name'] == 'proj.local')['kind'], 'embedded_in_air')
        self.assertTrue(all(b['chain'] == ['proj.root'] for b in result['unresolvable']))
        self.assertEqual(result['status'], 'incomplete')

    def test_absent_root_and_model_conflict_and_collisions(self):
        result = run([air('mem.Allocator.create__anon_1', [])], ['proj.root', 'mem.Allocator.create__anon_1'])
        self.assertEqual(node(result, 'proj.root')['class'], 'missing')
        self.assertEqual(node(result, 'mem.Allocator.create__anon_1')['kind'], 'std_model_air_conflict')
        prefixes, collisions = closure.filter_prefixes(['proj.a'], ['mem.'], closure.std_models())
        self.assertEqual(prefixes, ['mem.', 'proj.a'])
        self.assertIn('mem.', collisions)

    def test_panic_handler_air_is_not_traversed_and_identity_keys(self):
        handler = "debug.FullPanic((function 'defaultPanic')).outOfBounds"
        result = run([air('proj.root', [call(1, handler, True)]), air(handler, [call(2, 'debug.dump')])], ['proj.root'])
        self.assertEqual((result['status'], node(result, handler)['kind']), ('closed', 'panic_handler'))
        # Golden mode keys identities by normalized name, including qualified indirect targets.
        indirect = {'id': 5, 'tag': 'call', 'ty': U32, 'callee': {'inst': 0}, 'args': []}
        functions = {closure.normalized(f['name']): closure.scan(f) for f in
                     [air('proj.root', [indirect], [fn_global('proj.cb__anon_41')]), air('proj.cb__anon_N', [])]}
        c = closure.Closure(functions, '0.16.0', None, (), closure.normalized).run(['proj.root'])
        self.assertEqual(c.indirect[0]['targets'], [{'name': 'proj.cb__anon_N', 'class': 'exported'}])
        self.assertEqual(closure.filter_prefix('array_list.Aligned(T__enum_N,null).append'), 'array_list.Aligned(T')

    def test_std_model_reader_matches_table(self):
        models = closure.std_models()
        coverage = load('coverage_script', SCRIPTS / 'coverage.py')
        names = {e['name'] for e in coverage.model_inventory((REPO / 'Air2Lean/StdModels.lean').read_text())}
        # coverage.py lists only mem.Allocator/Thread/Io/time rows; this reader reads every row.
        self.assertLessEqual(names, set(models))
        self.assertIn('atomic.spinLoopHint', models)
        self.assertEqual(models['mem.Allocator.allocSentinel'][:2], ('modelled', ('0.16.0',)))
        self.assertEqual(models['Thread.detach'][:2], ('modelled', ('0.16.0',)))
        self.assertEqual(models['Io.futexWaitTimeout'][0], 'rejected')
        self.assertEqual(models['Io.concurrent'][0], 'rejected')
        self.assertIn('is not a qualified async API', models['Io.concurrent'][2])
        with self.assertRaises(ValueError):
            closure.std_models('def stdModels : Array StdModel := #[\n  allocModel weird,\n  allocModel "a.b" .x #[]]')


class ProjectTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='air2lean-closure-')
        self.addCleanup(temporary.cleanup)
        self.base = Path(temporary.name)
        (self.base / 'profile.json').write_text(json.dumps({'name': 'legacy-abi64-le', 'zig_version': '0.16.0'}))
        for name in ('src.zig', 'patch', 'runtime', 'toolchain', 'contract'):
            (self.base / name).write_text('evidence')
        files = {'root.json': air('proj.root', [call(1, 'proj.mid')]),
                 'mid.json': air('proj.mid', [call(2, 'lib.deep.leaf__anon_5')])}
        for name, content in files.items():
            (self.base / name).write_text(json.dumps(content))
        root = dict(id='first', function='proj.root', air=sorted(files), namespace='Proj', prefix='proj.',
                    contracts=['contract'], goals=[], assumptions=[], exclusions=[])
        self.manifest = self.base / 'project.json'
        self.manifest.write_text(json.dumps(dict(schema=1, profile='profile.json', float_semantics='ieee',
            source_closure=['src.zig'], components=dict(compiler_patch=['patch'], runtime=['runtime'],
            toolchain=['toolchain']), allowed_assumptions=[], roots=[root])))

    def test_project_closure_reports_missing_transitive_callee(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = project.main(['closure', str(self.manifest)])
        self.assertEqual(code, 1)
        result = json.loads(out.getvalue())
        root = result['roots'][0]
        self.assertEqual((result['status'], root['id'], root['input_errors']), ('incomplete', 'first', []))
        self.assertEqual([(m['fqn'], m['filter_prefix'], m['chain']) for m in root['missing']],
                         [('lib.deep.leaf__anon_5', 'lib.deep.leaf', ['proj.root', 'proj.mid', 'lib.deep.leaf__anon_5'])])
        self.assertEqual(root['filter']['value'], 'lib.deep.leaf,proj.')
        self.assertIn("src.zig", root['reexport'])

    def test_project_closure_with_registry_and_text(self):
        registry = self.base / 'models.json'
        registry.write_text(json.dumps({'schema': 1, 'models': [{'symbol': 'lib.deep.leaf__anon_5'}]}))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = closure.main(['manifest', str(self.manifest), '--model-registry', str(registry), '--format', 'text'])
        self.assertEqual(code, 0, out.getvalue())
        self.assertIn('first: closed exported=2 modelled=1 missing=0 unresolvable=0', out.getvalue())

    def test_malformed_air_is_an_input_error(self):
        (self.base / 'mid.json').write_text('{')
        result = closure.manifest_closure(self.manifest)
        self.assertEqual(result['status'], 'incomplete')
        self.assertEqual(result['roots'][0]['input_errors'][0]['path'], 'mid.json')
        self.assertEqual(result['roots'][0]['missing'][0]['fqn'], 'proj.mid')


class GoldenTests(unittest.TestCase):
    def test_overlay_and_filter_file_coverage(self):
        with tempfile.TemporaryDirectory(prefix='air2lean-closure-golden-') as temporary:
            base = Path(temporary)
            (base / 'Air2Lean').mkdir()
            (base / 'Air2Lean/StdModels.lean').write_text((REPO / 'Air2Lean/StdModels.lean').read_text())
            (base / 'examples/ex').mkdir(parents=True)
            (base / 'examples/ex/zig-versions').write_text('0.16.0\n')
            shared = base / 'tests/golden/ex/air'
            linux = base / 'tests/golden/0.16.0/ex/air-linux'
            shared.mkdir(parents=True)
            linux.mkdir(parents=True)
            (shared / 'ex.main.json').write_text(json.dumps(air('ex.main', [call(1, 'util.helper__anon_12')])))
            (shared / 'util.helper__anon_N.json').write_text(json.dumps(air('util.helper__anon_N', [])))
            # The Linux overlay replaces ex.main with one that also calls an unexported function.
            (linux / 'ex.main.json').write_text(json.dumps(air('ex.main', [call(1, 'util.helper__anon_99'),
                                                                          call(2, 'util.other')])))
            result = closure.golden_closure(['ex'], base)
            by_os = {r['host_os']: r for r in result['examples']}
            self.assertEqual(set(by_os), {'other', 'linux'})
            self.assertEqual(by_os['other']['status'], 'closed')
            self.assertEqual(by_os['other']['filter']['existing_uncovered'], ['util.helper__anon_N'])
            self.assertEqual([m['fqn'] for m in by_os['linux']['missing']], ['util.other'])
            self.assertEqual(result['status'], 'incomplete')
            (base / 'examples/ex/filter').write_text('util.helper\n')
            self.assertEqual(closure.golden_closure(['ex'], base)['examples'][0]['filter']['existing_uncovered'], [])

    def test_committed_goldens_are_closed(self):
        result = closure.golden_closure()
        problems = [(r['example'], r['zig_version'], r['host_os'], r['missing'], r['unresolvable'],
                     r['filter']['existing_uncovered'], r['filter']['std_model_collisions'])
                    for r in result['examples'] if r['status'] != 'closed' or r['filter']['existing_uncovered']
                    or r['filter']['std_model_collisions']]
        self.assertEqual(problems, [])
        self.assertEqual(result['status'], 'closed')
        layout = next(r for r in result['examples'] if r['example'] == 'layout' and r['zig_version'] == '0.16.0')
        self.assertTrue(layout['indirect_calls'])
        self.assertTrue(all(site['class'] == 'qualified' for site in layout['indirect_calls']))


if __name__ == '__main__':
    unittest.main()
