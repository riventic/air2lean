"""AIR semantics certificates (V01 slice): translator-side checks, no Lean or Zig.

Runs the built translator on committed golden AIR and checks that
(a) `--air-certificate` leaves the generated Lean byte-identical (and equal to the committed
    Proofs/<Ex>/Gen.lean body);
(b) the certificate equals the committed Proofs/<Ex>/AirCert.lean;
(c) the certified set and the listed exclusions are the expected ones (fail closed);
(d) the flag's argument checks reject incomplete or clashing outputs;
(e) the semantics, the generator and the certificates contain no sorry/admit/native_decide.
`lake build Proofs` kernel-checks the committed certificates; test_lean.py runs the round
trip and mutation checks.
"""
import argparse
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]

EXPECTED = {
    'basic': (['basic.absDiff', 'basic.clampAdd', 'basic.classify', 'basic.scale', 'basic.tardiness'],
              ['basic.sum', 'basic.totalWeightedTardiness', 'basic.weightedTardiness']),
    'recursion': (['recursion.fact', 'recursion.gcd', 'recursion.isEven', 'recursion.isOdd'], []),
}


def run(binary, ex, out, *flags):
    # The shared goldens are schema-11 AIR: translating them needs the explicit legacy profile.
    command = [str(binary), str(ROOT / 'tests/golden' / ex / 'air'), '-o', str(out),
               '--namespace', ex.capitalize(), '--prefix', ex + '.', '--profile', 'legacy-abi64-le', *flags]
    return subprocess.run(command, capture_output=True, text=True, timeout=300)


def certificate_sets(text):
    certified = re.search(r'^/-! Certified: (.*)$', text, re.M).group(1)
    certified = re.findall(r'`([^`]+)`', certified)
    excluded = re.findall(r'^\* `([^`]+)`: ', text, re.M)
    return certified, excluded


def check_example(binary, ex, work):
    plain = work / f'{ex}.lean'
    cert = work / f'{ex}.cert.lean'
    with_cert = work / f'{ex}.with-cert.lean'
    result = run(binary, ex, plain)
    assert result.returncode == 0, result.stderr
    module = f'Proofs.{ex.capitalize()}.Gen'
    result = run(binary, ex, with_cert, '--air-certificate', str(cert), '--air-certificate-import', module)
    assert result.returncode == 0, result.stderr
    assert plain.read_bytes() == with_cert.read_bytes(), f'{ex}: --air-certificate changed generated Lean'
    committed_gen = ROOT / 'Proofs' / ex.capitalize() / 'Gen.lean'
    assert with_cert.read_bytes().split(b'\n', 1)[1] == committed_gen.read_bytes(), f'{ex}: Gen.lean body changed'
    committed = ROOT / 'Proofs' / ex.capitalize() / 'AirCert.lean'
    assert cert.read_bytes() == committed.read_bytes(), \
        f'{ex}: stale {committed.relative_to(ROOT)}; regenerate with --air-certificate'
    text = cert.read_text()
    certified, excluded = certificate_sets(text)
    assert (certified, excluded) == EXPECTED[ex], (ex, certified, excluded)
    for name in certified:
        decl = name.split('.', 1)[1]
        assert re.search(rf'^theorem {decl}_step ', text, re.M), (ex, name)
        assert re.search(rf'^theorem {decl}_(run|eq) ', text, re.M), (ex, name)
    assert re.search(r'^theorem run_le_gen ', text, re.M)


def check_flags(binary, work):
    out = work / 'flags.lean'
    lone = run(binary, 'basic', out, '--air-certificate', str(work / 'c.lean'))
    assert lone.returncode == 1 and 'go together' in lone.stderr, lone
    lone = run(binary, 'basic', out, '--air-certificate-import', 'Proofs.Basic.Gen')
    assert lone.returncode == 1 and 'go together' in lone.stderr, lone
    clash = run(binary, 'basic', out, '--air-certificate', str(out), '--air-certificate-import', 'M')
    assert clash.returncode == 1 and 'another output' in clash.stderr, clash
    twice = run(binary, 'basic', out, '--air-certificate', 'a.lean', '--air-certificate', 'b.lean',
                '--air-certificate-import', 'M')
    assert twice.returncode == 1 and 'duplicate --air-certificate' in twice.stderr, twice


def check_no_escape_hatches():
    paths = [ROOT / 'Air2Lean/Sem.lean', ROOT / 'Air2Lean/SemAttr.lean', ROOT / 'Air2Lean/Certificate.lean',
             *(ROOT / 'Proofs' / ex.capitalize() / 'AirCert.lean' for ex in EXPECTED)]
    for path in paths:
        code = re.sub(r'/-.*?-/|--[^\n]*', '', path.read_text(), flags=re.S)
        for word in ('sorry', 'admit', 'native_decide'):
            assert not re.search(rf'\b{word}\b', code), (path, word)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('binary', type=Path)
    args = parser.parse_args()
    check_no_escape_hatches()
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        for ex in EXPECTED:
            check_example(args.binary, ex, work)
        check_flags(args.binary, work)
    print('AIR semantics certificate checks passed')


if __name__ == '__main__':
    main()
