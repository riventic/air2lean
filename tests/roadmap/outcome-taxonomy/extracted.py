#!/usr/bin/env python3
"""Check actual audited theorem outcomes and their declared contracts end to end."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location('claims', ROOT / 'scripts/claims.py')
claims = importlib.util.module_from_spec(spec)
spec.loader.exec_module(claims)
report = json.loads(Path(sys.argv[1]).read_text())
assert report['status'] == 'pass', report['violations']
theorems = claims.audited_theorems(report)
nodes = claims.nodes_of(report)
heads = claims.load_heads()

# The audit graph includes every witness and auxiliary root as well as the program proofs.
legacy_bridges = {'ZigLean.Sep.Full.Strength', 'ZigLean.Sep.Full.AllocBridge'}
bridge_nodes = [node['name'] for node in report['nodes'] if node.get('module') in legacy_bridges]
assert not bridge_nodes, ('full-state claims depend on legacy bridge declarations', bridge_nodes)
framework = json.loads((ROOT / 'assurance/proof-framework.json').read_text())
legacy = {}
for entry in framework['judgments']:
    if entry['status'] == 'legacy-to-retire':
        legacy.setdefault(entry['module'], set()).add(entry['name'])
legacy_nodes = [node['name'] for node in report['nodes']
                if any(node['name'] == name or node['name'].endswith('.' + name)
                       for name in legacy.get(node.get('module'), ()))]
assert not legacy_nodes, ('full-state claims depend on registered legacy judgments', legacy_nodes)


def outcomes(name):
    return theorems['OutcomeContracts.' + name]['statement']['outcomes']


for name in ('precise', 'optional', 'exact', 'stateFunction', 'readerFunction', 'readerViaState',
             'stateRunOnReader', 'statePairOnly', 'directTuple', 'directReader', 'directParameters'):
    assert outcomes(name)['status'] == 'computed', (name, outcomes(name))
    assert outcomes(name)['returns'] == ['valid'], (name, outcomes(name))
assert outcomes('erased')['returns'] == ['valid', 'error_return'], outcomes('erased')
for name in ('stateErased', 'concurrentErased'):
    assert outcomes(name)['status'] == 'computed', (name, outcomes(name))
    assert outcomes(name)['returns'] == ['valid', 'error_return'], (name, outcomes(name))
for name in ('errorOnly', 'exactError', 'stateViaReader', 'readerRunOnState',
             'stateRunPrimeOnState', 'exceptRunOnState', 'nestedViaReader', 'nestedPrime', 'readerNestedPrime',
             'stateErrorOnly', 'concurrentErrorOnly', 'concurrentProjected', 'probeDirectErrorOnly',
             'probeExactDirect', 'probeExactNested', 'probeConcDirect', 'overappliedRun',
             'overappliedProjection', 'dependentHead'):
    assert outcomes(name)['status'] == 'computed', (name, outcomes(name))
    assert outcomes(name)['returns'] == ['error_return'], (name, outcomes(name))
for name in ('unknown', 'opaquePost', 'projected', 'plainFunction', 'plainRun',
             'stateRunPrimeOnReader', 'fabricatedProjection', 'noncanonicalOverappliedProjection'):
    assert outcomes(name)['status'] == 'unsupported', (name, outcomes(name))
for name, kind in (('panic', 'panic'), ('illegal', 'illegal_behavior'), ('unspecified', 'unspecified_behavior'),
                   ('timer', 'unspecified_timer'), ('deadlock', 'deadlock'), ('trap', 'hardware_trap'),
                   ('stack', 'stack_overflow')):
    assert outcomes(name)['unexcluded'] == [kind], (name, outcomes(name))
assert outcomes('conditional')['unexcluded'] == ['divergence', 'stack_overflow'], outcomes('conditional')


def goal(name, admits, strength, domain='all'):
    result = {'theorem': 'OutcomeContracts.' + name, 'strength': strength, 'domain': domain}
    if admits is not None:
        result['outcomes'] = {'admits': admits}
    return result


def check(name, admits, *, strength='total_correctness', definition='good', domain='all'):
    return claims.check_goal(goal(name, admits, strength, domain), theorems,
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

for name in ('concurrentErrorOnly', 'concurrentErased', 'concurrentProjected', 'probeConcDirect'):
    result = check(name, None, definition='concurrentFailed', strength='partial_correctness')
    assert result['status'] == 'accepted' and result['binding'] == 'direct', (name, result)
    assert result['derived_strength'] == 'partial_correctness', (name, result)
    assert outcomes(name)['concurrent'] is True, (name, outcomes(name))
    assert outcomes(name)['unexcluded'] == ['divergence', 'stack_overflow'], (name, outcomes(name))

# Feed the real audited MM/CTriple statements through the manifest parser and production gate.
# Both MM valid-only goals were accepted before state products were interpreted from the source.
cases = [('stateErrorOnly', 'stateFailed', 'total_correctness', ['valid'], 'fail'),
         ('stateErased', 'stateFailed', 'total_correctness', ['valid'], 'fail'),
         ('stateErrorOnly', 'stateFailed', 'total_correctness', ['error_return'], 'pass'),
         ('stateErased', 'stateFailed', 'total_correctness', ['valid', 'error_return'], 'pass'),
         ('statePairOnly', 'statePair', 'total_correctness', ['valid'], 'pass'),
         ('probeDirectErrorOnly', 'stateFailed', 'total_correctness', ['valid'], 'fail'),
         ('probeExactDirect', 'failed', 'total_correctness', ['valid'], 'fail'),
         ('probeExactNested', 'stateFailed', 'total_correctness', ['valid'], 'fail'),
         ('probeDirectErrorOnly', 'stateFailed', 'total_correctness', ['error_return'], 'pass'),
         ('probeExactDirect', 'failed', 'total_correctness', ['error_return'], 'pass'),
         ('probeExactNested', 'stateFailed', 'total_correctness', ['error_return'], 'pass'),
         ('overappliedRun', 'stateFailed', 'total_correctness', ['valid'], 'fail'),
         ('overappliedProjection', 'stateFailed', 'total_correctness', ['valid'], 'fail'),
         ('overappliedRun', 'stateFailed', 'total_correctness', ['error_return'], 'pass'),
         ('overappliedProjection', 'stateFailed', 'total_correctness', ['error_return'], 'pass'),
         ('directTuple', 'statePair', 'total_correctness', ['valid'], 'pass'),
         ('directReader', 'readerPair', 'total_correctness', ['valid'], 'pass'),
         ('directParameters', 'parameterizedState', 'total_correctness', ['valid'], 'pass'),
         ('probeConcDirect', 'concurrentFailed', 'partial_correctness', ['valid'], 'fail'),
         ('concurrentErrorOnly', 'concurrentFailed', 'partial_correctness', ['valid'], 'fail'),
         ('concurrentErased', 'concurrentFailed', 'partial_correctness', ['valid'], 'fail'),
         ('fabricatedPureSuccess', 'disguisedStop', 'total_correctness', None, 'fail'),
         ('ordinaryOptionEquation', 'ordinaryOption', 'total_correctness', None, 'fail'),
         ('partialOptionEquation', 'partialOption', 'total_correctness', None, 'fail'),
         ('concurrentProjected', 'concurrentFailed', 'partial_correctness', None, 'pass')]
with tempfile.TemporaryDirectory() as temporary:
    base = Path(temporary)
    (base / 'profile.json').write_text(json.dumps({'name': 'legacy-abi64-le', 'zig_version': '0.17.0'}))
    for name, definition, strength, admitted, status in cases:
        manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee',
                    'source_closure': ['fixture.zig'],
                    'components': {'compiler_patch': ['fixture'], 'runtime': ['fixture'], 'toolchain': ['fixture']},
                    'allowed_assumptions': [],
                    'roots': [{'id': 'root', 'function': 'fixture.' + definition, 'air': ['fixture.air.json'],
                               'namespace': 'OutcomeContracts', 'prefix': 'fixture.', 'contracts': ['Contracts.lean'],
                               'goals': [goal(name, admitted, strength)], 'assumptions': [], 'exclusions': []}]}
        path = base / 'project.json'
        path.write_text(json.dumps(manifest))
        result = claims.check(path, report)
        assert result['status'] == status, (name, result)
        found = result['roots'][0]['goals'][0]
        if status == 'fail' and admitted is None:
            assert found['derived_strength'] != strength, (name, found)
        else:
            assert found['binding'] == 'direct', (name, found)
        if status == 'fail' and admitted is not None:
            assert found['theorem_outcome_contract']['status'] == 'rejected', (name, found)
            assert 'error_return' in found['theorem_outcome_contract']['missing'], (name, found)

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
                         ('hiddenFunctionEquation', 'hiddenFunction'),
                         ('ordinaryOptionEquation', 'ordinaryOption'),
                         ('partialOptionEquation', 'partialOption'),
                         ('fabricatedProjection', 'failed'), ('plainFunction', 'plainPair'),
                         ('noncanonicalOverappliedProjection', 'stateFailed')):
    subject = theorems['OutcomeContracts.' + name]['statement']['args'][1]
    assert subject['fn'] is None and subject['runner_error'], (name, subject)
    for admitted in (['valid'], ['error_return'], None):
        result = check(name, admitted, definition=definition)
        assert result['status'] == 'rejected' and result['binding'] != 'direct', (name, result)
        assert result['reason'] == subject['runner_error'], (name, result)
print('audited theorem outcome contracts passed')
