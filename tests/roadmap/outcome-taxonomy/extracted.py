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
nodes = claims.nodes_of(report)
heads = claims.load_heads()


def outcomes(name):
    return theorems['OutcomeContracts.' + name]['statement']['outcomes']


for name in ('precise', 'optional', 'exact', 'stateFunction', 'readerFunction', 'readerViaState',
             'stateRunOnReader'):
    assert outcomes(name)['status'] == 'computed', (name, outcomes(name))
    assert outcomes(name)['returns'] == ['valid'], (name, outcomes(name))
assert outcomes('erased')['returns'] == ['valid', 'error_return'], outcomes('erased')
for name in ('errorOnly', 'exactError', 'stateViaReader', 'readerRunOnState',
             'stateRunPrimeOnState', 'exceptRunOnState', 'nestedViaReader', 'nestedPrime', 'readerNestedPrime'):
    assert outcomes(name)['returns'] == ['error_return'], (name, outcomes(name))
for name in ('unknown', 'opaquePost', 'projected', 'plainFunction', 'plainRun',
             'stateRunPrimeOnReader', 'fabricatedProjection'):
    assert outcomes(name)['status'] == 'unsupported', (name, outcomes(name))
for name, kind in (('panic', 'panic'), ('illegal', 'illegal_behavior'), ('unspecified', 'unspecified_behavior'),
                   ('timer', 'unspecified_timer'), ('deadlock', 'deadlock'), ('trap', 'hardware_trap'),
                   ('stack', 'stack_overflow')):
    assert outcomes(name)['unexcluded'] == [kind], (name, outcomes(name))
assert outcomes('conditional')['unexcluded'] == ['divergence', 'stack_overflow'], outcomes('conditional')


def check(name, admits, *, strength='total_correctness', definition='good', domain='all'):
    return claims.check_goal({'theorem': 'OutcomeContracts.' + name, 'strength': strength, 'domain': domain,
                              'outcomes': {'admits': admits}}, theorems,
                             definition='OutcomeContracts.' + definition, nodes=nodes, heads=heads)


for name, admitted, status in [('erased', ['valid'], 'rejected'),
                              ('erased', ['valid', 'error_return'], 'accepted'),
                              ('precise', ['valid'], 'accepted'),
                              ('precise', ['valid', 'error_return'], 'accepted'),
                              ('unknown', ['valid'], 'rejected'),
                              ('conditional', ['valid'], 'rejected')]:
    result = check(name, admitted, strength='partial_correctness' if name == 'conditional' else 'total_correctness',
                   domain='scoped: arbitrary predicate assumption' if name == 'unknown' else 'all')
    assert result['status'] == status, (name, result)
    contract = result['theorem_outcome_contract']
    assert contract['status'] == ('under_claim' if name == 'precise' and len(admitted) == 2 else
                                   'verified' if status == 'accepted' else 'rejected'), result
    if name == 'unknown':
        assert 'unsupported' in result['reason'], result
for name, definition in (('optional', 'wrapped'), ('stateFunction', 'good')):
    result = check(name, ['valid'], definition=definition)
    assert result['status'] == 'accepted', result
for admitted, status in ((['valid'], 'rejected'), (['error_return'], 'accepted')):
    result = check('errorOnly', admitted, definition='failed')
    assert result['status'] == status, result
    assert result['theorem_outcome_contract']['theorem_admits'] == ['error_return'], result

for name, definition, permitted, forbidden in (
        ('readerRunOnState', 'failed', 'error_return', 'valid'),
        ('stateRunOnReader', 'readerStatePair', 'valid', 'error_return'),
        ('stateRunPrimeOnState', 'failed', 'error_return', 'valid'),
        ('nestedViaReader', 'nestedFailed', 'error_return', 'valid'),
        ('nestedPrime', 'nestedFailed', 'error_return', 'valid'),
        ('readerNestedPrime', 'readerNestedFailed', 'error_return', 'valid')):
    for admitted, status in ((permitted, 'accepted'), (forbidden, 'rejected')):
        result = check(name, [admitted], definition=definition)
        assert result['status'] == status, (name, result)
        assert result['binding'] == 'direct', (name, result)
for name, definition in (('stateRunPrimeOnReader', 'readerStatePair'), ('plainRun', 'plainPair'),
                         ('fabricatedProjection', 'failed')):
    subject = theorems['OutcomeContracts.' + name]['statement']['args'][1]
    assert subject['fn'] is None and subject['runner_error'], (name, subject)
    for admitted in (['valid'], ['error_return'], None):
        goal = {'theorem': 'OutcomeContracts.' + name, 'strength': 'total_correctness', 'domain': 'all'}
        if admitted is not None:
            goal['outcomes'] = {'admits': admitted}
        result = claims.check_goal(goal, theorems, definition='OutcomeContracts.' + definition,
                                   nodes=nodes, heads=heads)
        assert result['status'] == 'rejected' and result['binding'] != 'direct', (name, result)
        assert result['reason'] == subject['runner_error'], (name, result)
print('audited theorem outcome contracts passed')
