#!/usr/bin/env python3
"""F2: the actual False-own and False-fee kernel spikes cannot back allocator claims."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[5]
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('claims', ROOT / 'scripts/claims.py')
claims = importlib.util.module_from_spec(spec)
spec.loader.exec_module(claims)


def main():
    files = {'FeeFalse': Path(__file__).with_name('FeeFalse.lean'),
             'Vacuity': ROOT / 'tests/roadmap/invariant-synthesis/Vacuity.lean',
             'Fixture': ROOT / 'tests/roadmap/claims/Fixture.lean'}
    with tempfile.TemporaryDirectory(prefix='air2lean-allocator-vacuity-') as directory:
        work = Path(directory)
        env = {**os.environ, 'LEAN_PATH': directory + os.pathsep + os.environ.get('LEAN_PATH', '')}
        for module, path in files.items():
            checked = subprocess.run(['lake', 'env', 'lean', '-R', str(path.parent), '-o', str(work / f'{module}.olean'),
                                      str(path)], cwd=ROOT, env=env, capture_output=True, text=True)
            if checked.returncode:
                raise RuntimeError(str(path) + '\n' + checked.stdout + checked.stderr)
            print(f'F2 kernel: {module}: checked')
        audited = {}
        # Fixture deliberately spoofs retired heads. FeeFalse imports the real legacy heads
        # through ZigLean, so these independent controls need separate checked environments.
        for group in (('FeeFalse', 'Vacuity'), ('Fixture',)):
            report_path = work / (group[0] + '-assurance.json')
            modules = [arg for module in group for arg in ('--module', module)]
            result = subprocess.run([sys.executable, '-B', 'scripts/assumptions.py', '--no-build',
                                     *modules, '--output', str(report_path)],
                                    cwd=ROOT, env=env, capture_output=True, text=True)
            if result.returncode not in (0, 1) or not report_path.is_file():
                raise RuntimeError(result.stdout + result.stderr)
            audited.update(claims.audited_theorems(json.loads(report_path.read_text())))
        for theorem, expected in (('Audit1014.FeeFalse.trap_spec', 'mismatch'),
                                  ('InvariantSynthesis.Vacuity.vacuous_spec', 'absent')):
            found = claims.assess(audited[theorem], claims.load_heads(), audited=audited)
            evidence = found['allocator_creation']
            if evidence['status'] != expected or not claims.uncreated(found):
                raise AssertionError((theorem, found))
            assert any(entry['contract'] == theorem for entry in evidence['contracts']), evidence
            print(f'F2 negative: claim gate rejects {theorem}: no verified creation and FAdmit companions')
        family = claims.assess(audited['ClaimAllocator.admissionFamilySpec'], claims.load_heads(), audited=audited)
        if claims.uncreated(family) is None:
            raise AssertionError('F2 OPEN: existential FAdmit authenticates only n=0; visible n=1 is not created '
                                 '(engine ledger #allocator-creation-admissibility)')
        own = next(entry for entry in family['allocator_creation']['contracts']
                   if entry['contract'] == 'ClaimAllocator.admissionFamilySpec')
        assert own['post_status'] == 'verified' and own['admissibility']['status'] == 'verified', own
        assert own['status'] == 'unbound_admissibility', own
        print('F2 negative: gate rejects unbound visible-instance admissibility')


if __name__ == '__main__':
    main()
