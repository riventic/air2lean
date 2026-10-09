"""Portable contract tests only; successful mocks never qualify a native target."""
import copy
import importlib.util
import json
import subprocess
import tempfile
from unittest.mock import patch
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('abi_probe', ROOT / 'scripts/abi-probe.py')
abi = importlib.util.module_from_spec(spec)
spec.loader.exec_module(abi)


def profile(target='x86_64-linux-gnu', mode='ReleaseSafe', version='0.16.0'):
    directory = ROOT / 'tests/roadmap/abi-probes' / ('' if version == '0.16.0' else version)
    return json.loads((directory / f'{target}-{mode}.json').read_text())


def text(p):
    _, os_tag, abi_tag, _ = abi.NATIVE[p['target_triple']]
    rows = {'meta': {'arch': p['target_triple'].split('-')[0], 'os': os_tag, 'abi': abi_tag,
                    'endian': 'little', 'backend': p['backend'], 'mode': p['build_mode'],
                    'cpu': p['cpu'], 'zig': p['zig_version'], 'pointer_bits': '64',
                    'error_set_bits': '16', 'error_tracing': str(p['error_tracing']).lower()},
            'layout': abi.LAYOUTS, 'offset': abi.OFFSETS, 'value': abi.VALUES,
            'feature': {name: 1 for name in p['features']}}
    return '\n'.join(' '.join(map(str, [kind, name, *(value if isinstance(value, list) else [value])]))
                     for kind, values in rows.items() for name, value in values.items())


def report(target):
    p = profile(target)
    return {'schema': 1, 'kind': 'air2lean-native-abi-fragment', 'profile': p,
            'source_sha256': abi.fingerprints(), 'observations': abi.observations(text(p), p)}


class ContractTests(unittest.TestCase):
    def test_profiles_fail_closed(self):
        for key, value in [('pointer_bits', 32), ('pointer_bits', True), ('endian', 'big'),
                           ('backend', 'stage2_aarch64'), ('build_mode', 'Debug'),
                           ('target_triple', 'wasm32-wasi-musl'), ('zig_version', '0.13.0'),
                           ('features', ['sse2', 'sse']), ('features', ['sse', 'sse2', 'sse2']),
                           ('export_stage', 'shipping-binary'), ('float_mode', 'optimized')]:
            p = profile(); p[key] = value
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                abi.profile_check(p)
        p = profile(); p['extra'] = 1
        with self.assertRaises(ValueError): abi.profile_check(p)

    def test_observations_require_complete_exact_values(self):
        p = profile()
        abi.profile_check(p)
        abi.observations(text(p), p)
        mismatch = copy.deepcopy(p); mismatch['features'] = ['sse']
        with self.assertRaises(ValueError): abi.observations(text(p), mismatch)
        for bad in [text(p).replace('value pointer_load 1234567', 'value pointer_load 1'),
                    text(p).replace('layout vector4 16 16', 'layout vector4 16 8'),
                    text(p).replace('meta backend stage2_llvm', 'meta backend stage2_x86_64'),
                    text(p) + '\nvalue pointer_load 1234567',
                    text(p).replace('offset record_count 4\n', '')]:
            with self.assertRaises(ValueError): abi.observations(bad, p)

    def test_compile_failure_preserves_bounded_cause_without_running_binary(self):
        # A fake compiler file and mocked launch exercise the actual failure path;
        # no compiler/native target executes, on any host operating system.
        cause = b"probe.zig:29: error: builtin has no member error_return_tracing\n" + b"x" * 10000
        with tempfile.TemporaryDirectory() as directory:
            compiler = Path(directory) / 'zig'
            compiler.write_bytes(b'portable fake compiler')
            failure = subprocess.CalledProcessError(1, ['zig'], stderr=cause)
            with patch.object(abi.platform, 'system', return_value='Linux'), \
                    patch.object(abi.subprocess, 'run', side_effect=failure) as launch:
                with self.assertRaisesRegex(ValueError, 'builtin has no member error_return_tracing') as caught:
                    abi.run(compiler, profile())
            self.assertEqual(launch.call_count, 1)  # no attempt to execute the absent binary
            self.assertEqual(launch.call_args.kwargs['timeout'], 300)
            self.assertTrue(launch.call_args.kwargs['check'])
            self.assertIn('compiler stderr truncated after 4096 bytes', str(caught.exception))
            self.assertLess(len(str(caught.exception)), 4300)
            self.assertIs(caught.exception.__cause__, failure)

    def test_macos_profile_binds_its_own_os_abi_and_cpu(self):
        for mode in ('ReleaseSafe', 'ReleaseFast'):
            p = profile('aarch64-macos-none', mode)
            abi.profile_check(p)
            abi.observations(text(p), p)
            linux_meta = text(p).replace('meta os macos', 'meta os linux')
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                abi.observations(linux_meta, p)
        for key, value in [('abi', 'gnu'), ('cpu', 'generic'), ('target_triple', 'aarch64-macos-gnu')]:
            p = profile('aarch64-macos-none'); p[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                abi.profile_check(p)

    def test_macos_profile_never_executes_on_another_system(self):
        with patch.object(abi.platform, 'system', return_value='Linux'), \
                patch.object(abi.subprocess, 'run') as launch:
            with self.assertRaisesRegex(ValueError, 'requires a Darwin execution environment'):
                abi.run('/nonexistent/zig', profile('aarch64-macos-none'))
        launch.assert_not_called()
        with patch.object(abi.platform, 'system', return_value='Darwin'), \
                patch.object(abi.subprocess, 'run') as launch:
            with self.assertRaisesRegex(ValueError, 'requires a Linux execution environment'):
                abi.run('/nonexistent/zig', profile())
        launch.assert_not_called()

    def test_versioned_contracts_bind_their_version(self):
        # Q05: 0.14.1 x86_64-linux and 0.15.2 aarch64-macos target probes (CI test/macos jobs).
        for version, target in (('0.14.1', 'x86_64-linux-gnu'), ('0.15.2', 'aarch64-macos-none')):
            for mode in ('ReleaseSafe', 'ReleaseFast'):
                p = profile(target, mode, version)
                self.assertEqual(p['zig_version'], version)
                abi.profile_check(p)
                abi.observations(text(p), p)
                other = text(p).replace(f'meta zig {version}', 'meta zig 0.16.0')
                with self.subTest(version=version, mode=mode), self.assertRaises(ValueError):
                    abi.observations(other, p)
        # 0.15.2 names the zero-cycle FP/GPR move features differently from 0.16.0.
        newer = text(profile('aarch64-macos-none')).replace('meta zig 0.16.0', 'meta zig 0.15.2')
        with self.assertRaises(ValueError):
            abi.observations(newer, profile('aarch64-macos-none', version='0.15.2'))

    def test_pair_requires_one_zig_version(self):
        left = report(abi.TARGETS[0])
        right = report(abi.TARGETS[1])
        older = copy.deepcopy(left)
        older['profile']['zig_version'] = '0.14.1'
        older['observations'] = abi.observations(text(older['profile']), older['profile'])
        with self.assertRaisesRegex(ValueError, 'Zig versions differ'):
            abi.compare(older, right)

    def test_macos_report_is_outside_the_linux_pair(self):
        with self.assertRaises(ValueError):
            abi.compare(report('x86_64-linux-gnu'), report('aarch64-macos-none'))

    def test_pair_is_only_an_observation_relation(self):
        left, right = report(abi.TARGETS[0]), report(abi.TARGETS[1])
        relation = abi.compare(left, right)
        self.assertTrue(relation['observations_equal'])
        self.assertFalse(relation['native_execution_attested'])
        self.assertFalse(relation['translation_qualified'])
        self.assertFalse(relation['wasm_qualified'])
        wrong_target = report(abi.TARGETS[0])
        with self.assertRaises(ValueError): abi.compare(left, wrong_target)
        stale = copy.deepcopy(right); stale['source_sha256'][abi.SOURCES[0]] = '0' * 64
        with self.assertRaises(ValueError): abi.compare(left, stale)
        other_mode = copy.deepcopy(right); other_mode['profile']['build_mode'] = 'ReleaseFast'
        other_mode['observations'] = abi.observations(text(other_mode['profile']), other_mode['profile'])
        with self.assertRaises(ValueError): abi.compare(left, other_mode)


class VersionContractTests(unittest.TestCase):
    def test_version_contract_differs_only_in_version_and_features(self):
        for path in sorted((ROOT / 'tests/roadmap/abi-probes/0.17.0').glob('*.json')):
            p = json.loads(path.read_text())
            abi.profile_check(p)
            base = json.loads((path.parent.parent / path.name).read_text())
            self.assertEqual(p['zig_version'], '0.17.0')
            self.assertEqual({k: v for k, v in p.items() if k not in ('zig_version', 'features')},
                             {k: v for k, v in base.items() if k not in ('zig_version', 'features')})

    def test_observe_selects_the_compiler_version_contract(self):
        base = ROOT / 'tests/roadmap/abi-probes/aarch64-macos-none-ReleaseSafe.json'
        for version, expected in (('0.17.0', base.parent / '0.17.0' / base.name), ('0.16.0', base),
                                  ('0.18.0', base)):
            done = subprocess.CompletedProcess([], 0, stdout=(version + '\n').encode(), stderr=b'')
            with patch.object(abi.subprocess, 'run', return_value=done):
                self.assertEqual(abi.version_profile('zig', base), expected)

    def test_unknown_contract_version_is_rejected(self):
        p = profile('aarch64-macos-none')
        p['zig_version'] = '0.18.0'
        with self.assertRaisesRegex(ValueError, 'unsupported source profile'):
            abi.profile_check(p)


if __name__ == '__main__':
    unittest.main()
