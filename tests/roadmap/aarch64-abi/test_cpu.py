#!/usr/bin/env python3
"""Tests of the `fma` and `cpu` rows (Model.lean): the recorded files pass; an `@mulAdd` result
that is not the translator's rule for the file's version and CPU, a CPU whose rows are missing, a
row that depends on the CPU without the model stating it, and a wrong count fail. No compiler
runs here, so nothing qualifies a profile. Needs `lake build ZigLean.VecMem
ZigLean.Float.Allowed ZigLean.Mem.Thread Air2Lean.Air.Dialect`."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
VERSIONS = ('0.17.1', '0.16.0', '0.15.2', '0.14.1')
spec = importlib.util.spec_from_file_location('aarch64_abi', ROOT / 'scripts/aarch64-abi.py')
abi = importlib.util.module_from_spec(spec)
spec.loader.exec_module(abi)
TRIPLES = tuple(abi.PROFILES)
# The `f16` operands of the probe, with the result of an `f16` multiply-add (also that of an
# `f64` one rounded to `f16`) and of an `f32` one rounded to `f16`.
F16 = {'c290 c47c 0ffe': ('4b5b', '4b5c'), 'bf80 74e8 154e': ('f899', 'f89a'),
       'ee40 b848 0643': ('6ab1', '6ab0'), '3e00 3c01 8001': ('3e01', '3e02')}


def expected(version, triple):
    return abi.expected_path(version, triple, 'ReleaseSafe').read_text()


def check(triple, text):
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / 'observed.txt'
        path.write_text(text, encoding='utf-8')
        done = subprocess.run(['lake', 'env', 'lean', '--run', 'tests/roadmap/aarch64-abi/Model.lean',
                               triple, str(path)], cwd=ROOT, stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, text=True)
    return done.returncode, done.stdout + done.stderr


def f16_rows(text, prefix='fma f16 '):
    return {line[len(prefix):-5]: line[-4:] for line in text.splitlines() if line.startswith(prefix)}


class Rows(unittest.TestCase):
    def test_every_file_records_the_profile_cpus(self):
        for version in VERSIONS:
            for triple in TRIPLES:
                lines = expected(version, triple).splitlines()
                cpus = [line.split()[1] for line in lines if line.startswith('cpu ')]
                self.assertEqual(tuple(dict.fromkeys(cpus)), abi.CPUS[triple], (version, triple))
                self.assertEqual(sum(line.startswith('fma ') for line in lines), 6, (version, triple))
                # A CPU row is one the baseline has too, and the counts add up.
                probe = [line for line in lines if not line.startswith(('cpu ', 'vector ', 'lane ', 'load ',
                                                                         'pad ', 'limit ', 'f80atomic '))]
                for cpu in abi.CPUS[triple]:
                    rows = [line.split(' ', 2)[2] for line in lines if line.startswith(f'cpu {cpu} ')]
                    self.assertEqual(rows[-1], f'same {len(probe) - len(rows) + 1} of {len(probe)}',
                                     (version, triple, cpu))

    def test_f16_results_follow_version_and_fullfp16(self):
        """The native rule that `Dialect.f16MulAdd` states: the `f16` instruction with `fullfp16`;
        without it, through `f32` up to 0.16.0 and through `f64` (the `f16` result) from 0.17.1."""
        for version in VERSIONS:
            narrow = 0 if version == '0.17.1' else 1
            for triple in TRIPLES:
                text = expected(version, triple)
                fp16 = '\nfeature fullfp16 1\n' in text
                self.assertEqual(fp16, triple == 'aarch64-macos-none')
                base = f16_rows(text)
                self.assertEqual(base, {k: v[0 if fp16 else narrow] for k, v in F16.items()},
                                 (version, triple))
                for cpu in abi.CPUS[triple]:
                    rows = f16_rows(text, f'cpu {cpu} fma f16 ')
                    flipped = f'cpu {cpu} feature fullfp16 ' in text
                    want = {k: v[0 if fp16 != flipped else narrow] for k, v in F16.items()}
                    # Only a differing row is recorded.
                    self.assertEqual(rows, {k: v for k, v in want.items() if base[k] != v},
                                     (version, triple, cpu))

    def test_cpu_rows_of_the_driver(self):
        base = ['meta cpu a', 'feature x 0', 'fma f16 1 2 3 4', 'sync cache_line 128']
        self.assertEqual(abi.cpu_rows('a+x', base, base[:1] + ['feature x 1'] + base[2:]),
                         ['cpu a+x feature x 1', 'cpu a+x same 3 of 4'])
        self.assertEqual(abi.cpu_rows('a', base, base), ['cpu a same 4 of 4'])
        with self.assertRaises(ValueError):
            abi.cpu_rows('a', base, base[:-1])


class Model(unittest.TestCase):
    def assert_fails(self, triple, text, message):
        code, output = check(triple, text)
        self.assertEqual(code, 1, output)
        self.assertIn(message, output)

    def test_recorded_files_pass(self):
        for version in ('0.17.1', '0.16.0'):
            for triple in TRIPLES:
                code, output = check(triple, expected(version, triple))
                self.assertEqual(code, 0, output)
                self.assertIn(f'at {len(abi.CPUS[triple])} other CPUs', output)

    def test_wrong_mul_add_fails(self):
        linux17 = expected('0.17.1', 'aarch64-linux-gnu')
        # Zig 0.17.1 without `fullfp16`: the `f32` rule of the earlier versions is not the result.
        self.assert_fails('aarch64-linux-gnu', linux17.replace('fma f16 c290 c47c 0ffe 4b5b', 'fma f16 c290 c47c 0ffe 4b5c'),
                          'fma f16 c290 c47c 0ffe: the recorded result is not allowed by the model')
        linux16 = expected('0.16.0', 'aarch64-linux-gnu')
        self.assert_fails('aarch64-linux-gnu', linux16.replace('fma f16 c290 c47c 0ffe 4b5c', 'fma f16 c290 c47c 0ffe 4b5b'),
                          'fma f16 c290 c47c 0ffe: the recorded result is not allowed by the model')
        self.assert_fails('aarch64-linux-gnu', linux16.replace('fma f32 3f800001 3f7fffff 28000001 3f800001',
                                                               'fma f32 3f800001 3f7fffff 28000001 3f800000'),
                          'fma f32 3f800001 3f7fffff 28000001: the recorded result is not allowed')
        self.assert_fails('aarch64-linux-gnu', linux16.replace('fma f64 3ff0000000000001 ', 'fma f64 '),
                          'malformed')

    def test_cpu_result_must_be_the_rule_of_its_features(self):
        linux16 = expected('0.16.0', 'aarch64-linux-gnu')
        row = 'cpu generic+fullfp16 fma f16 c290 c47c 0ffe 4b5b\n'
        self.assertIn(row, linux16)
        # A CPU with `fullfp16` that still rounds through `f32` (the row left out: the baseline's).
        self.assert_fails('aarch64-linux-gnu',
                          linux16.replace(row, '').replace('cpu generic+fullfp16 same 299 of 304',
                                                           'cpu generic+fullfp16 same 300 of 304'),
                          "cpu generic+fullfp16: fma f16 c290 c47c 0ffe = 4b5c is not the model's result")
        self.assert_fails('aarch64-linux-gnu', linux16.replace(row, row.replace('4b5b', '4b5d')),
                          "cpu generic+fullfp16: fma f16 c290 c47c 0ffe = 4b5d is not the model's result")
        # macOS without `fullfp16`, up to 0.16.0: through `f32`, not the `f16` instruction.
        macos16 = expected('0.16.0', 'aarch64-macos-none')
        row = 'cpu apple_m1-fullfp16 fma f16 c290 c47c 0ffe 4b5c\n'
        self.assertIn(row, macos16)
        self.assert_fails('aarch64-macos-none',
                          macos16.replace(row, '').replace('cpu apple_m1-fullfp16 same 255 of 260',
                                                           'cpu apple_m1-fullfp16 same 256 of 260'),
                          "cpu apple_m1-fullfp16: fma f16 c290 c47c 0ffe = 4b5b is not the model's result")

    def test_other_cpu_dependence_fails(self):
        linux = expected('0.17.1', 'aarch64-linux-gnu')
        same = 'cpu generic+lse+rcpc same 302 of 304\n'
        self.assertIn(same, linux)
        self.assert_fails('aarch64-linux-gnu',
                          linux.replace(same, 'cpu generic+lse+rcpc sync cache_line 64\n'
                                              'cpu generic+lse+rcpc same 301 of 304\n'),
                          'cpu generic+lse+rcpc: `sync cache_line 64` depends on the CPU')
        # An unpadded atomic result is a claim of the model on every CPU.
        self.assert_fails('aarch64-linux-gnu',
                          linux.replace(same, 'cpu generic+lse+rcpc rmw u64 Max 1 2 1 1\n'
                                              'cpu generic+lse+rcpc same 301 of 304\n'),
                          'cpu generic+lse+rcpc: `rmw u64 Max 1 2 1 1` depends on the CPU')
        self.assert_fails('aarch64-linux-gnu', linux.replace(same, 'cpu generic+lse+rcpc same 303 of 304\n'),
                          'cpu generic+lse+rcpc: `same 303 of 304` with 2 changed rows')
        # A count that adds up, of fewer rows than the probe prints.
        self.assert_fails('aarch64-linux-gnu', linux.replace(same, 'cpu generic+lse+rcpc same 1 of 3\n'),
                          'cpu generic+lse+rcpc: `same 1 of 3`, but the baseline has 304 probe rows')
        self.assert_fails('aarch64-linux-gnu', linux.replace(same, ''),
                          'cpu generic+lse+rcpc: no single `same <k> of <n>` row')
        dropped = '\n'.join(l for l in linux.splitlines() if not l.startswith('cpu generic+lse+rcpc ')) + '\n'
        self.assert_fails('aarch64-linux-gnu', dropped, '`cpu` rows of')
        self.assert_fails('aarch64-linux-gnu', linux + 'cpu cortex_a76 same 304 of 304\n', '`cpu` rows of')

    def test_padded_min_max_at_a_cpu_is_rejected_not_matched(self):
        """Zig 0.14.1 and 0.15.2 with `outline_atomics` order a padded `u40`/`i40` cell with the
        other signedness: an operation the translator rejects on every CPU (`PADDED_ATOMIC`)."""
        for version in ('0.15.2', '0.14.1'):
            text = expected(version, 'aarch64-linux-gnu')
            self.assertIn('cpu generic+outline_atomics rmw u40 Max 7890abcdef 8987654321 7890abcdef 7890abcdef\n', text)
        code, output = check('aarch64-linux-gnu', expected('0.15.2', 'aarch64-linux-gnu'))
        self.assertEqual(code, 0, output)
        self.assertIn('rejected by the translator (PADDED_ATOMIC, not a match) '
                      'cpu generic+outline_atomics rmw u40 Max 7890abcdef', output)


if __name__ == '__main__':
    unittest.main()
