#!/usr/bin/env python3
"""Check actual audited theorem outcomes and their declared contracts end to end."""
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('claims', ROOT / 'scripts/claims.py')
claims = importlib.util.module_from_spec(spec)
spec.loader.exec_module(claims)
report = json.loads(Path(sys.argv[1]).read_text())
assert report['status'] == 'pass', report['violations']
theorems = claims.audited_theorems(report)


def outcomes(name):
    return theorems['OutcomeContracts.' + name]['statement']['outcomes']


for name in ('precise', 'optional', 'exact'):
    assert outcomes(name)['status'] == 'computed', (name, outcomes(name))
    assert outcomes(name)['returns'] == ['valid'], (name, outcomes(name))
assert outcomes('erased')['returns'] == ['valid', 'error_return'], outcomes('erased')
for name in ('errorOnly', 'exactError'):
    assert outcomes(name)['returns'] == ['error_return'], (name, outcomes(name))
for name in ('unknown', 'opaquePost'):
    assert outcomes(name)['status'] == 'unsupported', (name, outcomes(name))
for name, kind in (('panic', 'panic'), ('illegal', 'illegal_behavior'), ('unspecified', 'unspecified_behavior'),
                   ('timer', 'unspecified_timer'), ('deadlock', 'deadlock'), ('trap', 'hardware_trap'),
                   ('stack', 'stack_overflow')):
    assert outcomes(name)['unexcluded'] == [kind], (name, outcomes(name))
assert outcomes('conditional')['unexcluded'] == ['divergence', 'stack_overflow'], outcomes('conditional')


def check(name, admits, *, strength='total_correctness', definition='good', domain='all'):
    return claims.check_goal({'theorem': 'OutcomeContracts.' + name, 'strength': strength, 'domain': domain,
                              'outcomes': {'admits': admits}}, theorems,
                             definition='OutcomeContracts.' + definition, nodes=claims.nodes_of(report))


for name, admitted, status in [('erased', ['valid'], 'rejected'),
                              ('erased', ['valid', 'error_return'], 'accepted'),
                              ('precise', ['valid'], 'accepted'),
                              ('precise', ['valid', 'error_return'], 'accepted'),
                              ('unknown', ['valid'], 'rejected'),
                              ('conditional', ['valid'], 'rejected')]:
    result = check(name, admitted, strength='partial_correctness' if name == 'conditional' else 'total_correctness')
    assert result['status'] == status, (name, result)
    contract = result['theorem_outcome_contract']
    assert contract['status'] == ('under_claim' if name == 'precise' and len(admitted) == 2 else
                                   'verified' if status == 'accepted' else 'rejected'), result
print('audited theorem outcome contracts passed')
