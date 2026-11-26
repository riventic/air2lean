#!/usr/bin/env python3
"""Tests of the futex check (Futex.lean) on the recorded `futex` rows: the recorded files pass; a
value the model's OS rows do not allow, and a missing, repeated, unknown or malformed row, fail;
a call the model refuses is reported as refused, never as a match. No compiler runs here, so
nothing qualifies a profile. Needs `lake build ZigLean.Os ZigLean.Conc.Sched`."""
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
VERSIONS = ('0.17.1', '0.16.0', '0.15.2', '0.14.1')
TRIPLES = ('aarch64-linux-gnu', 'aarch64-macos-none')


def expected(version, triple):
    return ROOT / f'tests/roadmap/aarch64-abi/expected/{version}/{triple}-ReleaseSafe.txt'


def check(triple, path):
    done = subprocess.run(['lake', 'env', 'lean', '--run', 'tests/roadmap/aarch64-abi/Futex.lean',
                           triple, str(path)], cwd=ROOT, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True)
    return done.returncode, done.stdout + done.stderr


def check_text(triple, text):
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / 'observed.txt'
        path.write_text(text, encoding='utf-8')
        return check(triple, path)


def edited(triple, changes, drop=(), extra=()):
    """The 0.17.1 file of `triple` with the value of each case in `changes` replaced, the cases
    in `drop` removed and the lines `extra` appended."""
    lines = []
    for line in expected('0.17.1', triple).read_text(encoding='utf-8').splitlines():
        words = line.split()
        if words[:1] == ['futex'] and words[1] in drop:
            continue
        if words[:1] == ['futex'] and words[1] in changes:
            line = f'futex {words[1]} {changes[words[1]]}'
        lines.append(line)
    return '\n'.join([*lines, *extra]) + '\n'


class Futex(unittest.TestCase):
    def test_every_version_records_the_same_rows_per_profile(self):
        for triple, count in zip(TRIPLES, (79, 35)):
            rows = {version: [line for line in expected(version, triple).read_text().splitlines()
                              if line.startswith('futex ')] for version in VERSIONS}
            self.assertEqual(len(rows['0.17.1']), count, triple)
            for version in VERSIONS:
                self.assertEqual(rows[version], rows['0.17.1'], (version, triple))
            # No threaded case ran into its bound.
            self.assertNotIn('stuck', '\n'.join(rows['0.17.1']))

    def test_recorded_rows_are_model_outcomes(self):
        for triple, matched, refused in zip(TRIPLES, (68, 33), (11, 2)):
            code, out = check(triple, expected('0.17.1', triple))
            self.assertEqual(code, 0, out)
            self.assertIn(f'{matched} native futex results are outcomes of the model', out)
            self.assertEqual(out.count('refused by the model (.illegal, not a match)'), refused, out)

    def test_linux_values_outside_the_model_fail(self):
        changes = {
            'wait_private_mismatch': '0',               # a sleep and wake instead of EAGAIN
            'wait_shared_bad_nsec_kernel': '-14',       # the timeout is validated first
            'wake_private_unaligned': '0',
            'wake3_private_val1': '2,1/0,0,0',          # a wake above its limit
            'wake3_private_val0': '1,1,1/0,0,-110',     # a woken waiter that timed out
            'wake3_private_val7fffffff': 'sum=2,above=0/0,0,0',
            'domain_shared_waiter': '1,0/0',            # a private wake of a shared waiter
            'mutex': '4x20000=79999',                   # a lost increment
        }
        code, out = check_text('aarch64-linux-gnu', edited('aarch64-linux-gnu', changes))
        self.assertEqual(code, 1, out)
        for name, value in changes.items():
            self.assertIn(f'{name}: native `{value}` is not an outcome of the model', out)
        self.assertEqual(out.count('is not an outcome of the model'), len(changes), out)

    def test_macos_values_outside_the_model_fail(self):
        changes = {
            'wait2_timeout': '0',
            'wait_null': '-14',
            'wake_one_null': '-2',
            'wake1_all_wait2': '0/-60',
            'wake3_one': '0,0,0/n,n,-60',
            'mutex': '4x20000=80001',
        }
        code, out = check_text('aarch64-macos-none', edited('aarch64-macos-none', changes))
        self.assertEqual(code, 1, out)
        for name, value in changes.items():
            self.assertIn(f'{name}: native `{value}` is not an outcome of the model', out)
        self.assertEqual(out.count('is not an outcome of the model'), len(changes), out)

    def test_missing_repeated_unknown_and_malformed_rows_fail(self):
        text = edited('aarch64-linux-gnu', {'wait_private_null': 'EFAULT'}, drop=('wake_shared_none',),
                      extra=('futex wake_private_none 0', 'futex wake_private_some 1',
                             'futex wait_private_timeout -110 -4', 'futex mutex'))
        code, out = check_text('aarch64-linux-gnu', text)
        self.assertEqual(code, 1, out)
        for message in ('wake_shared_none: not in the file', 'more than one row for `wake_private_none`',
                        'unknown case `wake_private_some`',
                        'malformed row `futex wait_private_timeout -110 -4`', 'malformed row `futex mutex`',
                        'wait_private_null: `EFAULT` is not a return code'):
            self.assertIn(message, out)

    def test_another_profiles_file_fails(self):
        code, out = check('aarch64-macos-none', expected('0.17.1', 'aarch64-linux-gnu'))
        self.assertEqual(code, 1, out)
        self.assertIn('no `meta os macos` line', out)


if __name__ == '__main__':
    unittest.main()
