"""AIR semantics certificates (V01 slice): translator-side checks, no Lean or Zig.

Runs the built translator on the committed golden AIR of every example whose Proofs/<Ex>/Gen.lean
is that AIR's translation, and checks that
(a) `--air-certificate` leaves the generated Lean byte-identical (and equal to the committed
    Proofs/<Ex>/Gen.lean body);
(b) the certificate equals the committed Proofs/<Ex>/AirCert.lean;
(c) the certified set is the expected one, and every other function of the example is listed
    with a reason (fail closed);
(d) the flag's argument checks reject incomplete or clashing outputs;
(e) the semantics, the generator and the certificates contain no sorry/admit/native_decide.
`lake build Proofs` kernel-checks the committed certificates; test_lean.py runs the round
trip and mutation checks.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]

# The examples with a committed certificate: those whose committed Gen.lean is the translation of
# tests/golden/<ex>/air (not layout, threadsync, floatops).
EXAMPLES = ['asm', 'atomics', 'basic', 'errors', 'floatconv', 'floats', 'iogroup', 'options', 'pointers',
            'recursion', 'threads', 'variants', 'vectors']
# The certified functions (none for an example not listed); every other function must be listed
# as excluded.
CERTIFIED = {
    'basic': ['basic.absDiff', 'basic.clampAdd', 'basic.classify', 'basic.scale', 'basic.tardiness'],
    'iogroup': ['debug.assert'],
    'pointers': ['pointers.addTo', 'pointers.delay', 'pointers.dueOf', 'pointers.same', 'pointers.swap'],
    'recursion': ['recursion.fact', 'recursion.gcd', 'recursion.isEven', 'recursion.isOdd'],
    'threads': ['threads.writeFlag'],
    'vectors': ['vectors.sMod', 'vectors.sRem'],
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
    assert certified == CERTIFIED.get(ex, []), (ex, certified)
    golden = (ROOT / 'tests/golden' / ex / 'air').glob('*.json')
    names = sorted(json.loads(path.read_text())['name'] for path in golden)
    assert sorted(certified + excluded) == names, (ex, certified, excluded, names)
    for name in certified:
        # The certificate's stem: the generated name (prefix stripped), other characters as `_`.
        decl = re.sub(r'\W', '_', name.removeprefix(ex + '.'))
        assert re.search(rf'^theorem {decl}_step ', text, re.M), (ex, name)
        assert re.search(rf'^theorem {decl}_(run|eq) ', text, re.M), (ex, name)
    if certified:
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
             *(ROOT / 'Proofs' / ex.capitalize() / 'AirCert.lean' for ex in EXAMPLES)]
    for path in paths:
        code = re.sub(r'/-.*?-/|--[^\n]*', '', path.read_text(), flags=re.S)
        for word in ('sorry', 'admit', 'native_decide'):
            assert not re.search(rf'\b{word}\b', code), (path, word)


def check_coverage():
    """Every example with a committed certificate is checked here, and every certificate that
    certifies a function is in the round trip (RoundTrip.lean)."""
    committed = sorted(p.parent.name.lower() for p in (ROOT / 'Proofs').glob('*/AirCert.lean'))
    assert committed == EXAMPLES, (committed, EXAMPLES)
    round_trip = (ROOT / 'tests/roadmap/air-semantics/RoundTrip.lean').read_text()
    listed = re.findall(r'^#eval checkTable "tests/golden/(\w+)/air" ', round_trip, re.M)
    assert listed == sorted(CERTIFIED), (listed, 'RoundTrip.lean')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('binary', type=Path)
    args = parser.parse_args()
    check_no_escape_hatches()
    check_coverage()
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        for ex in EXAMPLES:
            check_example(args.binary, ex, work)
        check_flags(args.binary, work)
    print('AIR semantics certificate checks passed')


if __name__ == '__main__':
    main()
