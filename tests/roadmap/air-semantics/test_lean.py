"""AIR semantics certificates (V01 slice): Lean-side checks.

Needs `lake build Proofs.Basic.AirCert Proofs.Recursion.AirCert Air2Lean.Main` first.
(a) RoundTrip.lean: each certificate's embedded `Func` is the decoded golden AIR.
(b) Mutations: a certificate whose embedded AIR differs from what the generated code does
    (one operator changed) no longer checks, at that function's theorem. The committed
    certificates are not vacuous.
(c) fixtures/caller: a non-recursive caller of a certified function (a path the committed
    examples do not exercise) gets `_complete` and `_eq`, and its fresh certificate checks.
"""
import argparse
import os
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
]


def lean(path):
    return subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, capture_output=True,
                          text=True, timeout=1800)


def check_caller(binary, tmp):
    gen, cert = tmp / 'CallerGen.lean', tmp / 'CallerCert.lean'
    result = subprocess.run([str(binary), str(ROOT / 'tests/roadmap/air-semantics/fixtures/caller'),
                             '-o', str(gen), '--namespace', 'Caller', '--prefix', 'basic.',
                             '--air-certificate', str(cert), '--air-certificate-import', 'CallerGen'],
                            capture_output=True, text=True, timeout=300)
    assert result.returncode == 0, result.stderr
    text = cert.read_text()
    for name in ('scale_run', 'scaleTwice_sound', 'scaleTwice_complete', 'scaleTwice_eq'):
        assert f'theorem {name} ' in text, name
    olean = subprocess.run(['lake', 'env', 'lean', f'--root={tmp}', '-o', str(tmp / 'CallerGen.olean'), str(gen)],
                           cwd=ROOT, capture_output=True, text=True, timeout=1800)
    assert olean.returncode == 0, olean.stdout + olean.stderr
    check = subprocess.run(['lake', 'env', 'sh', '-c', 'LEAN_PATH="$1:$LEAN_PATH" exec lean "$2"', 'sh',
                            str(tmp), str(cert)], cwd=ROOT, capture_output=True, text=True, timeout=1800)
    assert check.returncode == 0, check.stdout + check.stderr
    print('caller fixture: scaleTwice_eq checks')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('binary', type=Path)
    args = parser.parse_args()
    result = lean(ROOT / 'tests/roadmap/air-semantics/RoundTrip.lean')
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.count('certified AIR terms equal the decoded golden files') == 2, result.stdout
    print(result.stdout, end='')
    with tempfile.TemporaryDirectory() as tmp:
        for index, (ex, old, new, theorem) in enumerate(MUTATIONS):
            source = (ROOT / 'Proofs' / ex / 'AirCert.lean').read_text()
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
    print('AIR semantics Lean checks passed')


if __name__ == '__main__':
    main()
