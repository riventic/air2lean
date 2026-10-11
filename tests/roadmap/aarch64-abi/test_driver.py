"""Portable tests of scripts/aarch64-abi.py; no compiler runs, so nothing here qualifies a profile."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('aarch64_abi', ROOT / 'scripts/aarch64-abi.py')
abi = importlib.util.module_from_spec(spec)
spec.loader.exec_module(abi)
EXPECTED = ROOT / 'tests/roadmap/aarch64-abi/expected/0.16.0'


def main(*args):
    out = io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
        code = abi.main(list(map(str, args)))
    return code, out.getvalue()


class Driver(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.dir = Path(self.temp.name)

    def tearDown(self):
        self.temp.cleanup()

    def observed(self, text):
        path = self.dir / 'observed.txt'
        path.write_text(text)
        return path

    def test_expected_files_are_per_profile_and_differ(self):
        linux = (EXPECTED / 'aarch64-linux-gnu-ReleaseSafe.txt').read_text()
        macos = (EXPECTED / 'aarch64-macos-none-ReleaseSafe.txt').read_text()
        self.assertIn('meta os linux\nmeta abi gnu\n', linux)
        self.assertIn('meta os macos\nmeta abi none\n', macos)
        self.assertIn('float c_longdouble 16 16 128', linux)
        self.assertIn('float c_longdouble 8 8 64', macos)
        for text in (linux, macos):
            self.assertIn('meta zig 0.16.0\n', text)
            self.assertIn('limit atomic_u256 expected_128-bit_integer_type_or_smaller', text)

    def test_every_version_records_every_profile_and_synchronization_row(self):
        limits = {p.stem for p in (ROOT / 'tests/roadmap/aarch64-abi/limits').glob('*.zig')}
        for version in ('0.16.0', '0.15.2', '0.14.1'):
            for triple in ('aarch64-linux-gnu', 'aarch64-macos-none'):
                text = (ROOT / f'tests/roadmap/aarch64-abi/expected/{version}/{triple}-ReleaseSafe.txt').read_text()
                self.assertIn(f'meta zig {version}\n', text)
                kinds = [line.split()[0] for line in text.splitlines()]
                for kind, count in (('rmw', 110), ('order', 4), ('atomic_ext', 5), ('litmus', 3)):
                    self.assertEqual(kinds.count(kind), count, (version, triple, kind))
                self.assertEqual({l.split()[1] for l in text.splitlines() if l.startswith('limit ')}, limits)
                # Forbidden outcomes never occur on a conforming target (nothing to normalize).
                self.assertIn('litmus mp_release_acquire violations 0 ', text)
                self.assertIn('litmus sb_seq_cst both_zero 0 unset 0 ', text)

    def test_older_versions_differ_from_0_16_0_only_in_soft_float_sqrt(self):
        for triple in ('aarch64-linux-gnu', 'aarch64-macos-none'):
            new = (EXPECTED / f'{triple}-ReleaseSafe.txt').read_text().splitlines()
            for version in ('0.15.2', '0.14.1'):
                old = (EXPECTED.parent / version / f'{triple}-ReleaseSafe.txt').read_text().splitlines()
                self.assertEqual(len(old), len(new))
                changed = [a.split(' sqrt(2)')[0] for a, b in zip(old, new) if a != b]
                self.assertEqual(changed, ['meta zig ' + version, 'fop f80', 'fop f128'], (version, triple))

    def test_exact_file_matches(self):
        code, output = main('compare', '--target', 'aarch64-linux-gnu',
                            EXPECTED / 'aarch64-linux-gnu-ReleaseSafe.txt')
        self.assertEqual(code, 0, output)
        self.assertEqual(json.loads(output)['status'], 'match')

    def test_other_profile_or_changed_line_mismatches(self):
        code, output = main('compare', '--target', 'aarch64-linux-gnu',
                            EXPECTED / 'aarch64-macos-none-ReleaseSafe.txt')
        self.assertEqual((code, json.loads(output)['status']), (1, 'mismatch'))
        text = (EXPECTED / 'aarch64-linux-gnu-ReleaseSafe.txt').read_text()
        for bad in (text.replace('sync cache_line 128', 'sync cache_line 64'),
                    text.replace('limit atomic_u256', 'limit atomic_u512'),
                    text + 'extra line\n', text.rsplit('\n', 2)[0] + '\n'):
            code, output = main('compare', '--target', 'aarch64-linux-gnu', self.observed(bad))
            self.assertEqual((code, json.loads(output)['status']), (1, 'mismatch'))

    def test_unrecorded_version_is_an_exclusion_not_a_match(self):
        text = (EXPECTED / 'aarch64-linux-gnu-ReleaseSafe.txt').read_text()
        code, output = main('compare', '--target', 'aarch64-linux-gnu',
                            self.observed(text.replace('meta zig 0.16.0', 'meta zig 0.18.0')))
        self.assertEqual((code, json.loads(output)['status']), (abi.EXCLUDED, 'excluded'))

    def test_foreign_host_is_an_exclusion_and_runs_no_compiler(self):
        for system, machine, target in (('Darwin', 'arm64', 'aarch64-linux-gnu'),
                                        ('Linux', 'x86_64', 'aarch64-linux-gnu'),
                                        ('Linux', 'aarch64', 'aarch64-macos-none')):
            with patch.object(abi.platform, 'system', return_value=system), \
                    patch.object(abi.platform, 'machine', return_value=machine), \
                    patch.object(abi.subprocess, 'run') as launch:
                code, output = main('check', '--zig', '/nonexistent/zig', '--target', target)
            self.assertEqual(code, abi.EXCLUDED, output)
            self.assertEqual(json.loads(output)['status'], 'excluded')
            launch.assert_not_called()

    def test_windows_records_every_version_with_x87_rows(self):
        """x86_64-windows-gnu (docs/windows-target.md): f80 long double, 64-bit atomics, and the
        x87 precision control of the main thread (64 bits from 0.15.2 on) and a spawned one."""
        for version in ('0.17.0', '0.16.0', '0.15.2', '0.14.1'):
            text = (EXPECTED.parent / version / 'x86_64-windows-gnu-ReleaseSafe.txt').read_text()
            self.assertIn('meta arch x86_64\nmeta os windows\nmeta abi gnu\nmeta cpu x86_64\n', text)
            self.assertIn('float c_longdouble 16 16 80', text)
            self.assertIn('feature cx16 0\n', text)
            self.assertIn('limit atomic_u256 expected_64-bit_integer_type_or_smaller', text)
            self.assertNotIn('atomic u128', text)
            main_cw = '027f' if version == '0.14.1' else '037f'
            self.assertIn(f'x87 main cw {main_cw} ', text)
            self.assertIn('x87 thread cw 027f f80_third 3ffdaaaaaaaaaaaaa800\n', text)

    def test_runner_is_labelled_and_skips_the_host_check(self):
        self.assertEqual(abi.execution(()), {'native': True})
        self.assertEqual(abi.execution(('scripts/wine-run.sh',)),
                         {'native': False, 'runner': 'scripts/wine-run.sh'})
        with patch.object(abi.platform, 'system', return_value='Darwin'), \
                patch.object(abi.platform, 'machine', return_value='arm64'), \
                patch.object(abi.subprocess, 'run', side_effect=OSError('no compiler')) as launch:
            code, _ = main('check', '--zig', __file__, '--target', 'x86_64-windows-gnu',
                           '--runner', 'scripts/wine-run.sh')
        self.assertEqual(code, 1)
        launch.assert_called()

    def test_observation_without_version_fails(self):
        code, output = main('compare', '--target', 'aarch64-linux-gnu', self.observed('meta arch aarch64\n'))
        self.assertEqual(code, 1, output)


if __name__ == '__main__':
    unittest.main()
