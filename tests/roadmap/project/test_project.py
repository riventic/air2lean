import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest

SCRIPT = Path(__file__).resolve().parents[3] / 'scripts' / 'project.py'
spec = importlib.util.spec_from_file_location('project', SCRIPT)
project = importlib.util.module_from_spec(spec)
spec.loader.exec_module(project)


class ProjectTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        for name in ('source.zig', 'patch.zig', 'runtime.lean', 'toolchain', 'contract.lean'):
            (self.base / name).write_text('declared input\n')
        (self.base / 'profile.json').write_text(json.dumps({'name': 'legacy-abi64-le', 'zig_version': '0.16.0'}))
        self.air = {'schema': 11, 'name': 'example.root', 'zig_version': '0.16.0', 'body': []}
        (self.base / 'air.json').write_text(json.dumps(self.air))
        self.manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee', 'source_closure': ['source.zig'],
                         'components': {'compiler_patch': ['patch.zig'], 'runtime': ['runtime.lean'], 'toolchain': ['toolchain']},
                         'allowed_assumptions': ['allocator-policy'],
                         'roots': [{'id': 'root', 'function': 'example.root', 'air': ['air.json'],
                                    'namespace': 'Example', 'prefix': 'example.', 'contracts': ['contract.lean'],
                                    'goals': [{'theorem': 'Example.root_spec', 'strength': 'partial_correctness', 'domain': 'all u32 inputs'}],
                                    'assumptions': ['allocator-policy'], 'exclusions': ['backend correspondence unqualified']}]}
        self.path = self.base / 'project.json'
        self.save()
        self.translator = self.base / 'translator with spaces'
        self.mock("import pathlib,sys\npathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_text('namespace Example\\nend Example\\n')")

    def save(self):
        self.path.write_text(json.dumps(self.manifest))

    def mock(self, code):
        self.translator.write_text('#!' + sys.executable + '\n' + code + '\n')
        self.translator.chmod(0o755)

    def cli(self, command='report', *args):
        return subprocess.run([sys.executable, str(SCRIPT), command, str(self.path), *map(str, args)],
                              capture_output=True, text=True, timeout=15)

    def test_report_is_not_proof_or_export(self):
        result = self.cli()
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        root = report['roots'][0]
        self.assertEqual(root['input_validation']['status'], 'passed')
        self.assertTrue(all(root['stages'][s]['status'] == 'not_run' for s in project.STAGES))
        self.assertEqual(root['outcomes']['exact_match'], 0)
        self.assertEqual(root['outcomes']['proof_exclusion'], 1)

    def test_translation_and_stale_hashes(self):
        artifact = self.base / 'artifact'
        result = self.cli('translate', '--translator', self.translator, '--out', artifact)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((artifact / 'root' / 'Gen.lean').is_file())
        self.assertFalse((artifact / 'root' / 'air').exists())
        self.assertEqual(self.cli('verify', '--artifact', artifact).returncode, 0)
        (self.base / 'source.zig').write_text('edited')
        self.assertEqual(self.cli('verify', '--artifact', artifact).returncode, 2)

    def test_tampered_generated_file(self):
        artifact = self.base / 'artifact'
        self.cli('translate', '--translator', self.translator, '--out', artifact)
        (artifact / 'root' / 'Gen.lean').write_text('changed')
        self.assertEqual(self.cli('verify', '--artifact', artifact).returncode, 2)

    def test_immutable_existing_output(self):
        artifact = self.base / 'artifact'
        artifact.mkdir()
        old = artifact / 'sentinel'
        old.write_text('previous verified result')
        self.assertEqual(self.cli('translate', '--translator', self.translator, '--out', artifact).returncode, 2)
        self.assertEqual(old.read_text(), 'previous verified result')

    def test_failed_translation_never_publishes(self):
        self.mock("import pathlib,sys\npathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_text('partial')\nsys.exit(7)")
        artifact = self.base / 'artifact'
        result = self.cli('translate', '--translator', self.translator, '--out', artifact)
        self.assertEqual(result.returncode, 1)
        self.assertFalse(artifact.exists())
        self.assertFalse(list(self.base.glob('.air2lean-*')))
        self.assertEqual(json.loads(result.stdout)['diagnostics'][0]['code'], 'TRANSLATION_FAILED')

    def test_independent_root_failures_collected(self):
        root = dict(self.manifest['roots'][0], id='second')
        self.manifest['roots'].append(root)
        self.save()
        self.mock("import sys\nprint('subset blocker')\nsys.exit(1)")
        result = self.cli('translate', '--translator', self.translator, '--out', self.base / 'artifact')
        report = json.loads(result.stdout)
        self.assertEqual([d['root'] for d in report['diagnostics']], ['root', 'second'])

    def test_independent_malformed_air(self):
        (self.base / 'bad.json').write_text('{')
        (self.base / 'bad2.json').write_text('{')
        self.manifest['roots'][0]['air'] += ['bad.json', 'bad2.json']
        self.save()
        report = json.loads(self.cli().stdout)
        self.assertEqual([d['path'] for d in report['diagnostics']], ['bad.json', 'bad2.json'])

    def test_timeout_and_no_publication(self):
        self.manifest['limits'] = {'timeout_seconds': 1}
        self.save()
        self.mock('import time\ntime.sleep(5)')
        artifact = self.base / 'artifact'
        result = self.cli('translate', '--translator', self.translator, '--out', artifact)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(json.loads(result.stdout)['diagnostics'][0]['code'], 'TRANSLATION_TIMEOUT')
        self.assertFalse(artifact.exists())

    def test_sigterm_cancels_child(self):
        pidfile = self.base / 'child.pid'
        self.mock(f'import os,pathlib,time\npathlib.Path({str(pidfile)!r}).write_text(str(os.getpid()))\ntime.sleep(10)')
        artifact = self.base / 'artifact'
        child = subprocess.Popen([sys.executable, str(SCRIPT), 'translate', str(self.path),
                                  '--translator', str(self.translator), '--out', str(artifact)],
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.addCleanup(lambda: child.kill() if child.poll() is None else None)
        deadline = time.monotonic() + 5
        while not pidfile.exists() and time.monotonic() < deadline:
            time.sleep(.02)
        self.assertTrue(pidfile.exists())
        child.send_signal(signal.SIGTERM)
        stdout, stderr = child.communicate(timeout=5)
        self.assertEqual(child.returncode, 130, stderr)
        with self.assertRaises(ProcessLookupError):
            os.kill(int(pidfile.read_text()), 0)
        self.assertFalse(artifact.exists())
        self.assertFalse(list(self.base.glob('.air2lean-*')))

    def test_shell_metacharacters_are_literal(self):
        self.manifest['roots'][0]['prefix'] = '$(touch PWNED);`touch PWNED`'
        self.save()
        result = self.cli('translate', '--translator', self.translator, '--out', self.base / 'artifact')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse((self.base / 'PWNED').exists())

    def test_no_clobber_report_and_explicit_overwrite(self):
        out = self.base / 'report.json'
        out.write_text('prior result')
        self.assertEqual(self.cli('report', '--out', out).returncode, 2)
        self.assertEqual(out.read_text(), 'prior result')
        self.assertEqual(self.cli('report', '--out', out, '--overwrite').returncode, 0)
        json.loads(out.read_text())

    def test_duplicate_keys_depth_and_invalid_numbers(self):
        for data in (b'{"a":1,"a":2}', b'[[[[]]]]', b'{"a":NaN}', b'{"a":1e309}'):
            with self.assertRaises((ValueError, project.Invalid)):
                project.bounded_json(data, dict(project.LIMITS, max_json_depth=3))
        self.assertEqual(project.bounded_json(b'{"a":"[[[[[["}', dict(project.LIMITS, max_json_depth=3)), {'a': '[[[[[['})

    def test_unknown_manifest_fields_and_boolean_limits(self):
        for value in ({'unknown': 1}, {'limits': {'max_json_depth': True}}, {'schema': True}):
            original = dict(self.manifest)
            self.manifest.update(value)
            self.save()
            self.assertEqual(self.cli().returncode, 2)
            self.manifest = original

    def test_assumption_allowlist(self):
        self.manifest['roots'][0]['assumptions'] = ['unlisted-axiom']
        self.save()
        self.assertEqual(self.cli().returncode, 2)

    def test_escape_and_symlink_rejected(self):
        for name in ('../elsewhere', '/tmp/source.zig'):
            self.manifest['source_closure'] = [name]
            self.save()
            self.assertEqual(self.cli().returncode, 1)
        outside = Path(self.temp.name).parent / (self.base.name + '-outside')
        outside.write_text('outside')
        self.addCleanup(lambda: outside.unlink(missing_ok=True))
        (self.base / 'linked').symlink_to(outside)
        self.manifest['source_closure'] = ['linked']
        self.save()
        self.assertEqual(self.cli().returncode, 1)

    def test_schema12_cannot_use_legacy_profile(self):
        self.air['schema'] = 12
        (self.base / 'air.json').write_text(json.dumps(self.air))
        self.assertEqual(self.cli().returncode, 1)

    def test_profile_conflicts_and_unsupported_export(self):
        self.air['zig_version'] = '0.15.2'
        self.air['body'] = [{'id': 1, 'tag': 'timer', 'unsupported': True}]
        (self.base / 'air.json').write_text(json.dumps(self.air))
        report = json.loads(self.cli().stdout)
        self.assertEqual([d['code'] for d in report['diagnostics']], ['AIR_EXPORT_UNSUPPORTED', 'AIR_JSON'])
        self.assertEqual(report['diagnostics'][0]['category'], 'unsupported_semantics')

    def test_input_and_output_caps(self):
        self.manifest['limits'] = {'max_output_bytes': 512}
        self.save()
        self.mock("import pathlib,sys\npathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_bytes(b'x'*4096)")
        artifact = self.base / 'artifact'
        self.assertEqual(self.cli('translate', '--translator', self.translator, '--out', artifact).returncode, 1)
        self.assertFalse(artifact.exists())

    def test_nonregular_inputs_fail_without_blocking(self):
        fifo = self.base / 'fifo'
        os.mkfifo(fifo)
        with self.assertRaises(project.Invalid):
            project.read_bounded(fifo, 1024)
        result = self.cli('translate', '--translator', fifo, '--out', self.base / 'artifact')
        self.assertEqual(result.returncode, 2)

    def test_independent_roots_keep_independent_input_status(self):
        self.manifest['roots'].append(dict(self.manifest['roots'][0], id='second'))
        self.manifest['roots'][0]['air'] = ['missing.json']
        self.save()
        report = json.loads(self.cli().stdout)
        self.assertEqual([r['input_validation']['status'] for r in report['roots']], ['failed', 'passed'])

    def test_failed_partial_outputs_removed_between_roots(self):
        self.manifest['roots'].append(dict(self.manifest['roots'][0], id='second'))
        self.save()
        self.mock("import pathlib,sys\noutput=pathlib.Path(sys.argv[sys.argv.index('-o')+1])\nprint('previous-root-present=' + str((output.parent.parent / 'root').exists()))\noutput.write_text('partial')\nsys.exit(1)")
        result = self.cli('translate', '--translator', self.translator, '--out', self.base / 'artifact')
        report = json.loads(result.stdout)
        self.assertIn('previous-root-present=False', report['roots'][1]['stages']['translated']['message'])

    def test_aggregate_generated_budget_preserves_transaction(self):
        self.manifest['limits'] = {'max_total_output_bytes': 8192}
        self.manifest['roots'].append(dict(self.manifest['roots'][0], id='second'))
        self.save()
        self.mock("import pathlib,sys\npathlib.Path(sys.argv[sys.argv.index('-o')+1]).write_bytes(b'x'*5000)")
        artifact = self.base / 'artifact'
        result = self.cli('translate', '--translator', self.translator, '--out', artifact)
        self.assertIn(result.returncode, (1, 2))
        self.assertFalse(artifact.exists())

    def test_file_and_root_counts_bounded(self):
        self.manifest['limits'] = {'max_files': 1}
        self.save()
        self.assertEqual(self.cli().returncode, 2)
        self.manifest['limits'] = {'max_roots': 1}
        self.manifest['roots'].append(dict(self.manifest['roots'][0], id='second'))
        self.save()
        self.assertEqual(self.cli().returncode, 2)

    def test_translator_hash_is_verified(self):
        artifact = self.base / 'artifact'
        self.cli('translate', '--translator', self.translator, '--out', artifact)
        self.mock('import sys\nsys.exit(0)')
        self.assertEqual(self.cli('verify', '--artifact', artifact).returncode, 2)

    def test_strict_profile_shape(self):
        for value in ({'name': 'new-target'}, [1], {'x': 1}):
            (self.base / 'profile.json').write_text(json.dumps(value))
            result = self.cli()
            self.assertEqual(result.returncode, 1, result.stderr)
            report = json.loads(result.stdout)
            self.assertEqual(report['roots'][0]['input_validation']['status'], 'failed')

    def test_invalid_input_cannot_be_overwritten(self):
        source = self.base / 'source.zig'
        source.write_bytes(b'x' * 2048)
        self.manifest['limits'] = {'max_file_bytes': 1024}
        self.save()
        result = self.cli('report', '--out', source, '--overwrite')
        self.assertEqual(result.returncode, 2)
        self.assertEqual(source.read_bytes(), b'x' * 2048)

    def test_unfinished_descendants_fail_and_are_killed(self):
        marker = self.base / 'helper-output'
        code = f"import subprocess,sys\nsubprocess.Popen([sys.executable, '-c', {('import time,pathlib;time.sleep(.5);pathlib.Path(' + repr(str(marker)) + ').write_text(\"late write\")')!r}])\n"
        self.mock(code)
        artifact = self.base / 'artifact'
        result = self.cli('translate', '--translator', self.translator, '--out', artifact)
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertEqual(json.loads(result.stdout)['diagnostics'][0]['code'], 'TRANSLATION_DESCENDANTS')
        time.sleep(.7)
        self.assertFalse(marker.exists())
        self.assertFalse(artifact.exists())

    def test_verify_rejects_malformed_report_and_missing_inventory(self):
        artifact = self.base / 'artifact'
        self.cli('translate', '--translator', self.translator, '--out', artifact)
        reportpath = artifact / 'report.json'
        original = json.loads(reportpath.read_text())
        for malformed in ([], dict(original, schema=True), dict(original, files={k:v for k,v in original['files'].items() if not k.startswith('generated/')})):
            reportpath.write_text(json.dumps(malformed))
            result = self.cli('verify', '--artifact', artifact)
            self.assertEqual(result.returncode, 2)
            json.loads(result.stderr)

    def test_profiled_air_strict_types_and_versioned_targets(self):
        profile = {'name': 'abi64-le-v1', 'target_triple': 'x86_64-linux.4.19...6.1-gnu.2.28',
                   'pointer_bits': 64, 'endian': 'little', 'abi': 'gnu', 'zig_version': '0.16.0',
                   'backend': 'stage2_llvm', 'cpu': 'baseline', 'features': [], 'build_mode': 'ReleaseSafe',
                   'float_mode': 'per-instruction', 'error_set_bits': 16, 'error_layout': 'type-table',
                   'export_stage': 'analyzed-air', 'error_tracing': False}
        for triple, abi in (('x86_64-linux.4.19...6.1-gnu.2.28', 'gnu'), ('aarch64-macos.14.0...15.0-none', 'none')):
            profile.update(target_triple=triple, abi=abi)
            (self.base / 'profile.json').write_text(json.dumps(profile))
            self.air.update(schema=12, profile=profile)
            (self.base / 'air.json').write_text(json.dumps(self.air))
            self.assertEqual(self.cli().returncode, 0)
        self.air['profile'] = dict(profile, error_tracing=0)
        (self.base / 'air.json').write_text(json.dumps(self.air))
        self.assertEqual(self.cli().returncode, 1)



if __name__ == '__main__':
    unittest.main()
