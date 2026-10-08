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
                            self.observed(text.replace('meta zig 0.16.0', 'meta zig 0.17.0')))
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

    def test_observation_without_version_fails(self):
        code, output = main('compare', '--target', 'aarch64-linux-gnu', self.observed('meta arch aarch64\n'))
        self.assertEqual(code, 1, output)


if __name__ == '__main__':
    unittest.main()
