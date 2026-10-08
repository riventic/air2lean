"""Offline I03 project check regressions: stub translator, Lake and audit; real guard and claims."""
import copy
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import unittest

SCRIPT = Path(__file__).resolve().parents[3] / 'scripts' / 'project.py'
GENERATED = 'namespace Example\ndef root := 0\nend Example\n'
LAKE = '''import json, os, pathlib, sys
with open(os.environ['STUB_LOG'], 'a') as log:
    log.write(json.dumps(['lake', *sys.argv[1:]]) + '\\n')
sys.exit(int(os.environ.get('STUB_LAKE_EXIT', '0')))
'''
AUDIT = '''import json, os, pathlib, sys
args = sys.argv[1:]
assert '--no-build' in args, args
fixture = json.loads(pathlib.Path(os.environ['STUB_AUDIT']).read_text())
modules = sorted(args[i + 1] for i, a in enumerate(args) if a == '--module')
fixture.setdefault('modules', modules)
pathlib.Path(args[args.index('--output') + 1]).write_text(json.dumps(fixture))
sys.exit(1 if fixture.get('status') == 'fail' else 0)
'''


class CheckTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name).resolve() / 'project'
        (self.base / 'Proofs/Example').mkdir(parents=True)
        for name in ('source.zig', 'patch.zig', 'runtime.lean', 'Proofs/Example/Contract.lean'):
            (self.base / name).write_text(name + '\n')
        (self.base / 'lean-toolchain').write_text('leanprover/lean4:v4.34.0\n')
        (self.base / 'Proofs/Example/Gen.lean').write_text(GENERATED)
        (self.base / 'profile.json').write_text(json.dumps({'name': 'legacy-abi64-le', 'zig_version': '0.16.0'}))
        (self.base / 'air.json').write_text(json.dumps({'schema': 11, 'name': 'example.root', 'zig_version': '0.16.0', 'body': []}))
        self.manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee', 'source_closure': ['source.zig'],
                         'components': {'compiler_patch': ['patch.zig'], 'runtime': ['runtime.lean'], 'toolchain': ['lean-toolchain']},
                         'allowed_assumptions': ['allocator-policy'],
                         'check': {'build_timeout_seconds': 60, 'audit_timeout_seconds': 60, 'rss_mib': 4096},
                         'roots': [{'id': 'root', 'function': 'example.root', 'air': ['air.json'],
                                    'namespace': 'Example', 'prefix': 'example.', 'generated': 'Proofs/Example/Gen.lean',
                                    'contracts': ['Proofs/Example/Contract.lean'],
                                    'goals': [{'theorem': 'root_spec', 'strength': 'total_correctness', 'domain': 'all inputs'}],
                                    'assumptions': ['allocator-policy'], 'exclusions': ['backend correspondence unqualified']}]}
        self.path = self.base / 'project.json'
        self.save()
        tools = Path(self.temp.name).resolve() / 'tools'
        (tools / 'bin').mkdir(parents=True)
        self.translator = tools / 'translator'
        self.write_tool(self.translator, "import pathlib,sys\npathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_text(%r)\n" % GENERATED)
        self.write_tool(tools / 'bin/lake', LAKE)
        self.audit_script = tools / 'assumptions.py'
        self.audit_script.write_text(AUDIT)
        self.log = tools / 'calls.log'
        self.fixture = tools / 'audit.json'
        self.env = dict(os.environ, PATH=f'{tools / "bin"}{os.pathsep}{os.environ["PATH"]}', STUB_LOG=str(self.log),
                        STUB_AUDIT=str(self.fixture), PYTHONDONTWRITEBYTECODE='1')
        self.lock = tools / 'build.lock'
        self.out = Path(self.temp.name).resolve() / 'records'
        self.nodes = [{'name': 'Example.root', 'module': 'Proofs.Example.Gen', 'kind': 'definition', 'dependencies': [],
                       'trust_class': 'kernel-declaration'},
                      {'name': 'root_spec', 'module': 'Proofs.Example.Contract', 'kind': 'theorem',
                       'dependencies': ['Example.root', 'propext'], 'trust_class': 'kernel-declaration'},
                      {'name': 'propext', 'module': 'Init.Core', 'kind': 'axiom', 'dependencies': [],
                       'trust_class': 'standard-logical-axiom'}]
        self.theorems = [self.theorem('root_spec')]
        self.write_audit()

    def save(self):
        self.path.write_text(json.dumps(self.manifest))

    @staticmethod
    def write_tool(path, code):
        path.write_text('#!' + sys.executable + '\n' + code)
        path.chmod(0o755)

    @staticmethod
    def theorem(name, head='Zig.TotalTriple', **extra):
        return dict({'name': name, 'module': 'Proofs.Example.Contract', 'axioms': ['propext'], 'opaque_dependencies': [],
                     'extern_dependencies': [], 'compiler_redirections': [], 'violations': [], 'allowed': True,
                     'statement_dependencies': ['Example.root'], 'conclusion_dependencies': ['Example.root'],
                     'conclusion': {'head': head, 'args': []}}, **extra)

    def write_audit(self, status='pass'):
        self.fixture.write_text(json.dumps({'schema_version': 1, 'status': status, 'theorems': self.theorems,
                                            'nodes': self.nodes, 'theorem_count': len(self.theorems), 'violations': [],
                                            'policy_sha256': '0' * 64, 'lean_toolchain': 'leanprover/lean4:v4.34.0'}))

    def run_check(self, name='a', *extra):
        result = subprocess.run([sys.executable, str(SCRIPT), 'check', str(self.path), '--translator', str(self.translator),
                                 '--out', str(self.out / name), '--lock', str(self.lock),
                                 '--assumptions-script', str(self.audit_script), *extra],
                                capture_output=True, text=True, timeout=120, env=self.env)
        record = json.loads(result.stdout) if result.returncode in (0, 1) else None
        return result, record

    def calls(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()] if self.log.exists() else []

    def compare(self, left, right):
        return subprocess.run([sys.executable, str(SCRIPT), 'compare-records', str(left), str(right)],
                              capture_output=True, text=True, timeout=30, env=self.env)

    def test_reproduced_record_and_comparison(self):
        result, record = self.run_check()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(record['status'], 'reproduced', record['failures'])
        stages = record['reproducible']['stages']
        for name in ('translate', 'reproduce', 'build', 'audit', 'inputs_stable'):
            self.assertEqual(stages[name]['status'], 'passed', name)
        self.assertEqual(stages['claims']['status'], 'pass')
        self.assertEqual(stages['claims']['goals']['root/root_spec']['derived_strength'], 'total_correctness')
        goal = record['reproducible']['roots'][0]['goals'][0]
        self.assertEqual((goal['status'], goal['standard_assumptions'], goal['project_assumptions']),
                         ('allowed', ['propext'], []))
        self.assertTrue(goal['references_root'])
        self.assertEqual(self.calls(), [['lake', 'build', 'Proofs.Example.Contract']])
        published = self.out / 'a'
        for name in ('record.json', 'build-guard.json', 'build.log', 'audit-guard.json', 'assumptions.json',
                     'claims.json', 'artifact/report.json', 'artifact/root/Gen.lean'):
            self.assertTrue((published / name).is_file(), name)
        self.assertEqual(json.loads((published / 'record.json').read_text()), record)
        guard = json.loads((published / 'build-guard.json').read_text())
        self.assertEqual((guard['outcome'], guard['phase'], guard['budget']['rss_mib']), ('success', 'proof', 4096))
        self.assertIn('input/Proofs/Example/Gen.lean', record['reproducible']['inputs'])
        self.assertEqual(record['host']['translator']['path'], str(self.translator))
        # A second run is equivalent; host-only differences are ignored by the comparison.
        self.assertEqual(self.run_check('b')[0].returncode, 0)
        second = self.out / 'b/record.json'
        data = json.loads(second.read_text())
        data['host'] = {'platform': {'system': 'Other'}, 'translator': {'sha256': 'f' * 64}}
        second.write_text(json.dumps(data))
        compared = self.compare(published / 'record.json', second)
        self.assertEqual(compared.returncode, 0, compared.stdout)
        self.assertEqual(json.loads(compared.stdout)['status'], 'reproduced')
        # Any reproducible difference is reported with its path.
        data['reproducible']['inputs']['input/source.zig']['sha256'] = '0' * 64
        data['reproducible']['lean_toolchain'] = 'leanprover/lean4:v4.0.0'
        second.write_text(json.dumps(data))
        compared = self.compare(published / 'record.json', second)
        self.assertEqual(compared.returncode, 1)
        paths = [d['path'] for d in json.loads(compared.stdout)['differences']]
        self.assertEqual(paths, ['reproducible.inputs.input/source.zig.sha256', 'reproducible.lean_toolchain'])

    def test_failed_records_do_not_compare_as_reproduced(self):
        self.manifest['roots'][0]['goals'][0]['theorem'] = 'absent_spec'
        self.save()
        self.assertEqual(self.run_check('a')[0].returncode, 1)
        self.assertEqual(self.run_check('b')[0].returncode, 1)
        compared = self.compare(self.out / 'a/record.json', self.out / 'b/record.json')
        self.assertEqual(compared.returncode, 1)
        result = json.loads(compared.stdout)
        self.assertEqual((result['status'], result['differences']), ('not_reproduced', []))

    def test_committed_generated_module_must_match_translation(self):
        (self.base / 'Proofs/Example/Gen.lean').write_text(GENERATED + '-- stale\n')
        result, record = self.run_check()
        self.assertEqual(result.returncode, 1)
        stages = record['reproducible']['stages']
        self.assertEqual((stages['translate']['status'], stages['reproduce']['status']), ('passed', 'failed'))
        self.assertEqual(stages['build']['status'], 'not_run')
        self.assertEqual(self.calls(), [])

    def header(self, zig_version='0.16.0', float_semantics='ieee'):
        profile = dict(name='legacy-abi64-le', schema=11, zig_version=zig_version, target_triple='unverified',
                       pointer_bits=64, endian='little', abi='unverified', backend='unverified', cpu='unverified',
                       features=[], build_mode='unverified', float_mode='unverified', error_set_bits=16,
                       error_layout='reference-model', error_tracing=None, export_stage='unverified')
        record = {'correspondence': 'model', 'float_semantics': float_semantics, 'profile': profile}
        return '-- air2lean-profile: ' + json.dumps(record, sort_keys=True, separators=(',', ':')) + '\n'

    def translate_with_header(self, header):
        self.write_tool(self.translator, "import pathlib,sys\npathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_text(%r)\n"
                        % (header + GENERATED))

    def test_profile_header_with_and_without_committed_header(self):
        self.translate_with_header(self.header())
        result, record = self.run_check('absent')
        self.assertEqual(result.returncode, 0, record['failures'])
        root = record['reproducible']['stages']['reproduce']['roots']['root']
        self.assertEqual((root['header_profile']['name'], root['header_profile']['zig_version'], root['committed_header']),
                         ('legacy-abi64-le', '0.16.0', False))
        self.assertEqual(root['body_sha256'], hashlib.sha256(GENERATED.encode()).hexdigest())
        (self.base / 'Proofs/Example/Gen.lean').write_text(self.header() + GENERATED)
        result, record = self.run_check('present')
        self.assertEqual(result.returncode, 0, record['failures'])
        self.assertTrue(record['reproducible']['stages']['reproduce']['roots']['root']['committed_header'])
        # A committed header that differs from the fresh one is not a reproduction.
        (self.base / 'Proofs/Example/Gen.lean').write_text(self.header(float_semantics='compiler-rt') + GENERATED)
        result, record = self.run_check('different')
        self.assertEqual(record['reproducible']['stages']['reproduce']['status'], 'failed')

    def test_profile_header_must_match_manifest(self):
        for name, header in (('version', self.header(zig_version='0.15.2')),
                             ('float', self.header(float_semantics='compiler-rt'))):
            self.translate_with_header(header)
            result, record = self.run_check(name)
            self.assertEqual(result.returncode, 1)
            stage = record['reproducible']['stages']['reproduce']
            self.assertEqual((stage['status'], stage['mismatched_roots']), ('failed', ['root']))
            self.assertIn('manifest', stage['roots']['root']['reason'])
        self.assertEqual(self.calls(), [])

    def test_translation_failure_stops_before_lake(self):
        self.write_tool(self.translator, 'import sys\nprint("unsupported")\nsys.exit(3)\n')
        result, record = self.run_check()
        self.assertEqual(result.returncode, 1)
        self.assertEqual(record['reproducible']['stages']['translate']['codes'], ['TRANSLATION_FAILED'])
        self.assertFalse((self.out / 'a/artifact').exists())
        self.assertEqual(self.calls(), [])

    def test_lake_failure_fails_build_and_skips_audit(self):
        self.env['STUB_LAKE_EXIT'] = '1'
        result, record = self.run_check()
        self.assertEqual(result.returncode, 1)
        stages = record['reproducible']['stages']
        self.assertEqual((stages['build']['status'], stages['build']['outcome']), ('failed', 'child_failed'))
        self.assertEqual(stages['audit']['status'], 'not_run')
        self.assertFalse((self.out / 'a/assumptions.json').exists())

    def test_project_assumption_must_be_allowed(self):
        self.nodes.append({'name': 'Example.trustMe', 'module': 'Proofs.Example.Model', 'kind': 'axiom',
                           'dependencies': [], 'trust_class': 'allowed-project-axiom'})
        self.theorems[0]['axioms'] = ['Example.trustMe', 'propext']
        self.write_audit()
        result, record = self.run_check('a')
        self.assertEqual(result.returncode, 1)
        goal = record['reproducible']['roots'][0]['goals'][0]
        self.assertEqual((goal['status'], goal['unallowed']), ('unallowed_assumption', ['Example.trustMe']))
        # Either the Lean name or the policy key may be allowed (and must be in the allowlist).
        for name in ('Example.trustMe', 'Proofs.Example.Model::Example.trustMe'):
            self.manifest['allowed_assumptions'] = ['allocator-policy', name]
            self.manifest['roots'][0]['assumptions'] = ['allocator-policy', name]
            self.save()
            result, record = self.run_check(name)
            self.assertEqual(result.returncode, 0, record['failures'])
            self.assertEqual(record['reproducible']['roots'][0]['goals'][0]['project_assumptions'][0]['classes'],
                             ['allowed-project-axiom'])

    def test_unknown_or_project_opaque_dependencies_are_not_standard(self):
        self.nodes.append({'name': 'Example.model', 'module': 'Proofs.Example.Model', 'kind': 'opaque',
                           'dependencies': [], 'trust_class': 'allowed-project-opaque'})
        self.nodes.append({'name': 'IO.RealWorld', 'module': 'Init.System.IO', 'kind': 'opaque',
                           'dependencies': [], 'trust_class': 'standard-library-opaque'})
        self.theorems[0]['opaque_dependencies'] = ['Example.model', 'IO.RealWorld', 'Example.vanished']
        self.write_audit()
        result, record = self.run_check()
        self.assertEqual(result.returncode, 1)
        goal = record['reproducible']['roots'][0]['goals'][0]
        self.assertEqual(goal['unallowed'], ['Example.model', 'Example.vanished'])
        self.assertEqual(goal['standard_assumptions'], ['IO.RealWorld', 'propext'])

    def test_declared_strength_above_type_is_rejected(self):
        self.theorems[0]['conclusion'] = {'head': 'Zig.Triple', 'args': []}
        self.write_audit()
        result, record = self.run_check()
        self.assertEqual(result.returncode, 1)
        claims = record['reproducible']['stages']['claims']
        self.assertEqual((claims['status'], claims['goals']['root/root_spec']['derived_strength']), ('fail', 'partial_correctness'))
        self.assertIn('claim strength check: fail', record['failures'])

    def test_audit_is_restricted_to_goal_theorems(self):
        self.nodes.append({'name': 'helper_bad', 'module': 'Proofs.Example.Contract', 'kind': 'theorem',
                           'dependencies': ['sorryAx'], 'trust_class': 'kernel-declaration'})
        self.theorems.append(self.theorem('helper_bad', violations=['sorryAx'], allowed=False))
        self.write_audit('fail')
        result, record = self.run_check('a')
        self.assertEqual(result.returncode, 0, record['failures'])
        self.assertEqual(record['reproducible']['stages']['audit']['audit_status'], 'fail')
        # The same violation on the goal theorem fails the check.
        self.theorems[0].update(violations=['sorryAx'], allowed=False)
        self.write_audit('fail')
        result, record = self.run_check('b')
        self.assertEqual(result.returncode, 1)
        self.assertEqual(record['reproducible']['roots'][0]['goals'][0]['status'], 'policy_violation')

    def test_goal_must_live_in_contract_and_bind_generated_root(self):
        self.theorems[0]['module'] = 'Proofs.Example.Other'
        self.write_audit()
        result, record = self.run_check('a')
        self.assertEqual(record['reproducible']['roots'][0]['goals'][0]['status'], 'outside_contracts')
        self.theorems[0]['module'] = 'Proofs.Example.Contract'
        self.nodes[0]['module'] = 'Proofs.Example.Model'
        self.write_audit()
        result, record = self.run_check('b')
        self.assertEqual(result.returncode, 1)
        self.assertEqual(record['reproducible']['roots'][0]['goals'][0]['status'], 'unbound_generated')

    def test_goal_conclusion_must_reference_root(self):
        # A wrapper statement whose proof (but not conclusion) mentions the root does not bind.
        self.theorems[0]['conclusion_dependencies'] = ['Example.wrapper']
        self.write_audit()
        result, record = self.run_check('a')
        self.assertEqual(result.returncode, 1)
        goal = record['reproducible']['roots'][0]['goals'][0]
        self.assertEqual((goal['status'], goal['references_root']), ('wrapper_or_unrelated', False))
        # Audits from extractors without statement dependencies fail closed.
        for key in ('statement_dependencies', 'conclusion_dependencies'):
            self.theorems[0].pop(key, None)
        self.write_audit()
        result, record = self.run_check('b')
        self.assertEqual(result.returncode, 1)
        self.assertEqual(record['reproducible']['roots'][0]['goals'][0]['status'], 'unbound')

    def test_audit_scope_must_match_contracts(self):
        fixture = json.loads(self.fixture.read_text())
        fixture['modules'] = ['Proofs.Example.Other']
        self.fixture.write_text(json.dumps(fixture))
        result, record = self.run_check()
        self.assertEqual(result.returncode, 1)
        self.assertEqual(record['reproducible']['stages']['audit']['status'], 'failed')
        self.assertIn('scope', record['reproducible']['stages']['audit']['reason'])

    def test_invalid_configuration_and_existing_output(self):
        original = copy.deepcopy(self.manifest)
        for mutate in (lambda m: m['roots'][0].pop('generated'),
                       lambda m: m['check'].update(rss_mib=0),
                       lambda m: m['check'].update(unknown=1),
                       lambda m: m['roots'][0].update(generated='not-a-module.lean')):
            self.manifest = copy.deepcopy(original)
            mutate(self.manifest)
            self.save()
            result, _ = self.run_check('invalid')
            self.assertEqual(result.returncode, 2, result.stderr)
            self.assertFalse((self.out / 'invalid').exists())
        self.manifest = original
        self.save()
        (self.out / 'taken').mkdir(parents=True)
        self.assertEqual(self.run_check('taken')[0].returncode, 2)
        self.assertEqual(self.calls(), [])

    def test_busy_lock_fails_unless_waited_for(self):
        self.lock.parent.mkdir(parents=True, exist_ok=True)
        with self.lock.open('a') as held:
            fcntl.flock(held, fcntl.LOCK_EX)
            result, record = self.run_check('busy')
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertEqual(record['reproducible']['stages']['build']['outcome'], 'lock_busy')
            releaser = threading.Timer(1.0, fcntl.flock, (held, fcntl.LOCK_UN))
            releaser.start()
            try:
                result, record = self.run_check('waited', '--lock-wait', '60')
            finally:
                releaser.cancel()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(record['status'], 'reproduced')
        self.assertEqual(self.compare(self.out / 'waited/record.json', self.out / 'waited/record.json').returncode, 0)
        self.assertEqual(self.run_check('negative', '--lock-wait', '-1')[0].returncode, 2)

    def test_compare_rejects_non_records(self):
        other = self.out / 'x.json'
        other.parent.mkdir(parents=True)
        other.write_text(json.dumps({'schema': 1, 'kind': 'air2lean-project-evidence'}))
        self.assertEqual(self.compare(other, other).returncode, 2)


def _load_project():
    import importlib.util
    spec = importlib.util.spec_from_file_location('air2lean_project_check_compare', SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


project = _load_project()


class CompareRecordsTests(unittest.TestCase):
    """`compare_records` in process: equal reproducible sections reproduce only if both runs passed."""

    def write(self, directory, name, status, toolchain='leanprover/lean4:v4.34.0'):
        path = Path(directory) / name
        path.write_text(json.dumps({'schema': project.SCHEMA, 'kind': project.RECORD_KIND, 'status': status,
                                    'reproducible': {'lean_toolchain': toolchain, 'inputs': {}},
                                    'host': {'platform': {'system': name}}}))
        return path

    def test_failed_record_with_equal_sections_is_not_reproduced(self):
        with tempfile.TemporaryDirectory() as directory:
            passed = self.write(directory, 'a.json', 'reproduced')
            self.assertEqual(project.compare_records(passed, self.write(directory, 'b.json', 'reproduced'))['status'],
                             'reproduced')
            result = project.compare_records(passed, self.write(directory, 'c.json', 'failed'))
            self.assertEqual((result['status'], result['differences']), ('not_reproduced', []))
            other = project.compare_records(passed, self.write(directory, 'd.json', 'reproduced', 'v4.0.0'))
            self.assertEqual([d['path'] for d in other['differences']], ['reproducible.lean_toolchain'])


class SecondMachineScriptTests(unittest.TestCase):
    """scripts/second-machine.sh rejects bad arguments before touching Docker or Git."""
    SCRIPT = SCRIPT.with_name('second-machine.sh')

    def run_script(self, *args):
        return subprocess.run(['bash', str(self.SCRIPT), *args], capture_output=True, text=True, timeout=30)

    def test_arguments(self):
        self.assertEqual(self.run_script('--help').returncode, 0)
        for args in (('--bogus',), ('--platform', 'linux/riscv64'), ('--rev',),
                     ('--compare', '/nonexistent/record.json')):
            with self.subTest(args=args):
                self.assertEqual(self.run_script(*args).returncode, 2)

    def test_elan_pins_cover_container_architectures(self):
        toml = SCRIPT.parents[1] / 'zig-patch/toml-get.sh'
        for table in ('[ci.elan]', '[ci.elan-aarch64]'):
            with self.subTest(table=table):
                sha = subprocess.run([str(toml), table, 'sha256'], capture_output=True, text=True, check=True).stdout
                self.assertRegex(sha.strip(), r'^[0-9a-f]{64}$')


if __name__ == '__main__':
    unittest.main()
