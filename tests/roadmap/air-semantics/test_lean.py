"""AIR semantics certificates (V01 slice): Lean-side checks.

Needs `lake build Proofs.<Ex>.AirCert Air2Lean.Main` (every committed certificate) first.
(a) RoundTrip.lean: each certificate's embedded `Func` is the decoded golden AIR.
(b) Mutations: a certificate whose embedded AIR differs from what the generated code does
    (one operator changed) no longer checks, at that function's theorem. The committed
    certificates are not vacuous.
(c) fixtures/caller: a non-recursive caller of a certified function (a path the committed
    examples do not exercise) gets `_complete` and `_eq`, and its fresh certificate checks.
(d) Slices and pointer arithmetic: the Zig 0.15.2 files of tests/golden/slices (the example has
    no committed certificate: its golden mixes versions) certify the expected functions, and the
    fresh certificate checks.
"""
import argparse
import json
import os
import re
import shutil
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]

MUTATIONS = [
    ('Basic', '(.arith .mul .checked (.inst 0) (.inst 2))', '(.arith .mul .wrap (.inst 0) (.inst 2))', 'scale_step'),
    ('Basic', '(.cmp .gt (.inst 0) (.inst 1))', '(.cmp .lt (.inst 0) (.inst 1))', 'absDiff_step'),
    ('Basic', '(.arith .add .sat (.inst 0) (.inst 1))', '(.arith .sub .sat (.inst 0) (.inst 1))', 'clampAdd_step'),
    ('Recursion', '(.div .rem (.inst 0) (.inst 1))', '(.div .divTrunc (.inst 0) (.inst 1))', 'gcd_step'),
    ('Recursion', '(.ret (.bool true))', '(.ret (.bool false))', 'isEven_step'),
    # Memory: a field offset, a store's value, a pointer comparison, a load's address.
    ('Pointers', '(.fieldPtr (.inst 0) 1)', '(.fieldPtr (.inst 0) 2)', 'dueOf_step'),
    ('Pointers', '(.store (.inst 0) (.inst 3))', '(.store (.inst 0) (.inst 2))', 'swap_step'),
    ('Pointers', '(.cmp .eq (.inst 0) (.inst 1))', '(.cmp .ne (.inst 0) (.inst 1))', 'same_step'),
    ('Threads', '(.fieldPtr (.inst 0) 1)', '(.fieldPtr (.inst 0) 0)', 'writeFlag_step'),
    # A loop: the checked increment of the loop counter made wrapping. The loop's AIR also appears
    # in its field and loop lemmas, so the mutation goes everywhere: the iteration lemma breaks.
    ('Pointers', '(.arith .add .checked (.inst 13) (.int 0 (1 : Int)))',
     '(.arith .add .wrap (.inst 13) (.int 0 (1 : Int)))', 'sumTo_loop6_body'),
]


def lean(path):
    return subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, capture_output=True,
                          text=True, timeout=1800)


def check_module(gen, cert, tmp):
    """Compile the generated module `gen` into `tmp`, then kernel-check the certificate `cert`."""
    olean = subprocess.run(['lake', 'env', 'lean', f'--root={tmp}', '-o', str(gen.with_suffix('.olean')), str(gen)],
                           cwd=ROOT, capture_output=True, text=True, timeout=1800)
    assert olean.returncode == 0, olean.stdout + olean.stderr
    check = subprocess.run(['lake', 'env', 'sh', '-c', 'LEAN_PATH="$1:$LEAN_PATH" exec lean "$2"', 'sh',
                            str(tmp), str(cert)], cwd=ROOT, capture_output=True, text=True, timeout=1800)
    assert check.returncode == 0, check.stdout + check.stderr


SLICES_CERTIFIED = ['slices.at', 'slices.bumpAt', 'slices.prevItem', 'slices.second', 'slices.sumZ']


def check_slices(binary, tmp):
    air = tmp / 'slices-0.15.2'
    air.mkdir()
    for path in sorted((ROOT / 'tests/golden/slices/air').glob('*.json')):
        if json.loads(path.read_text())['zig_version'] == '0.15.2':
            shutil.copy(path, air / path.name)
    gen, cert = tmp / 'SlicesGen.lean', tmp / 'SlicesCert.lean'
    result = subprocess.run([str(binary), str(air), '-o', str(gen), '--namespace', 'Slices', '--prefix', 'slices.',
                             '--profile', 'legacy-abi64-le',
                             '--air-certificate', str(cert), '--air-certificate-import', 'SlicesGen'],
                            capture_output=True, text=True, timeout=300)
    assert result.returncode == 0, result.stderr
    certified = re.findall(r'`([^`]+)`', re.search(r'^/-! Certified: (.*)$', cert.read_text(), re.M).group(1))
    assert certified == SLICES_CERTIFIED, certified
    check_module(gen, cert, tmp)
    print(f'slices: {len(certified)} certified functions check')


def check_caller(binary, tmp):
    gen, cert = tmp / 'CallerGen.lean', tmp / 'CallerCert.lean'
    result = subprocess.run([str(binary), str(ROOT / 'tests/roadmap/air-semantics/fixtures/caller'),
                             '-o', str(gen), '--namespace', 'Caller', '--prefix', 'basic.',
                             # The fixture AIR is schema 11: the reference ABI is accepted explicitly.
                             '--profile', 'legacy-abi64-le',
                             '--air-certificate', str(cert), '--air-certificate-import', 'CallerGen'],
                            capture_output=True, text=True, timeout=300)
    assert result.returncode == 0, result.stderr
    text = cert.read_text()
    for name in ('scale_run', 'scaleTwice_sound', 'scaleTwice_complete', 'scaleTwice_eq'):
        assert f'theorem {name} ' in text, name
    check_module(gen, cert, tmp)
    print('caller fixture: scaleTwice_eq checks')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('binary', type=Path)
    args = parser.parse_args()
    result = lean(ROOT / 'tests/roadmap/air-semantics/RoundTrip.lean')
    assert result.returncode == 0, result.stdout + result.stderr
    tables = (ROOT / 'tests/roadmap/air-semantics/RoundTrip.lean').read_text().count('\n#eval checkTable ')
    assert result.stdout.count('certified AIR terms equal the decoded golden files') == tables, result.stdout
    print(result.stdout, end='')
    with tempfile.TemporaryDirectory() as tmp:
        for index, (ex, old, new, theorem) in enumerate(MUTATIONS):
            source = (ROOT / 'Proofs' / ex / 'AirCert.lean').read_text()
            if '_loop' in theorem:
                # A function with loops restates its AIR in its loop lemmas: mutate every copy.
                assert source.count(old) >= 2, (ex, theorem, old)
                mutated = source.replace(old, new)
            else:
                # Mutate the theorem's own function: the AIR def it names.
                fn = theorem.rsplit('_', 1)[0]
                start_def = source.index(f'def air_{fn} : Func :=')
                end_def = source.index('\n\n', start_def)
                block = source[start_def:end_def]
                assert block.count(old) == 1, (ex, fn, old)
                mutated = source[:start_def] + block.replace(old, new) + source[end_def:]
            mutant = Path(tmp) / f'Mutant{index}.lean'
            mutant.write_text(mutated)
            result = lean(mutant)
            output = result.stdout + result.stderr
            assert result.returncode != 0, f'mutant {index} ({theorem}) still checks'
            lines = mutated.splitlines()
            start = next(i for i, l in enumerate(lines) if l.startswith(f'theorem {theorem} '))
            end = next(i for i in range(start + 1, len(lines)) if lines[i] == '')
            errors = [int(l.split(':')[1]) for l in output.splitlines()
                      if l.startswith(str(mutant)) and ': error' in l]
            assert errors and all(start < n <= end + 1 for n in errors[:1]), (theorem, errors, output[:2000])
            print(f'mutant {index}: {theorem} rejected')
        check_caller(args.binary, Path(tmp))
        check_slices(args.binary, Path(tmp))
    print('AIR semantics Lean checks passed')


if __name__ == '__main__':
    main()
