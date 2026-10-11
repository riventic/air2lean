#!/usr/bin/env bash
# Extract real statement structures from Fixture.lean, require them to match the checked-in
# fixture report, then check accepted and overstated manifest goals against that report.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
python3 tests/roadmap/claims/test_claims.py
out=.lake/assurance/claims
mkdir -p "$out" .lake/build/lib/lean/tests/roadmap/claims
lake build ZigLean.Sep.Witness ZigLean.Sep.Bounded ZigLean.Conc.Own ZigLean.Conc.Total
lake env lean -o .lake/build/lib/lean/tests/roadmap/claims/Fixture.olean tests/roadmap/claims/Fixture.lean
scripts/assumptions.sh --no-build --module tests.roadmap.claims.Fixture --output "$out/assurance.json"
python3 - "$out" <<'PY'
import json, subprocess, sys
from pathlib import Path
out = Path(sys.argv[1])
actual = json.loads((out / 'assurance.json').read_text())
fixture = json.loads(Path('tests/roadmap/claims/fixture-report.json').read_text())
shape = lambda r: {t['name']: (t['conclusion'], t['statement']) for t in r['theorems']}
assert actual['status'] == 'pass', actual['violations']
assert shape(actual) == shape(fixture), sorted(n for n in shape(actual) if shape(actual)[n] != shape(fixture).get(n))
# Every registered claim head is the declaration the extractor sees (module and fingerprint).
heads = json.loads(Path('assurance/claim-heads.json').read_text())['heads']
seen = {t['statement']['head']['name']: t['statement']['head'] for t in actual['theorems'] if t['statement']['head']}
for name, entry in heads.items():
    assert (seen[name]['module'], seen[name]['fingerprint']) == (entry['module'], entry['fingerprint']), name
(out / 'profile.json').write_text(json.dumps({'name': 'legacy-abi64-le', 'zig_version': '0.16.0'}))
def run(strength, theorem='ClaimFixture.ret_partial', namespace='ClaimFixture', function='ret', domain='all'):
    goals = [{'theorem': theorem, 'strength': strength, 'domain': domain}]
    if function == 'ret':
        goals.insert(0, {'theorem': 'ClaimFixture.ret_total', 'strength': 'total_correctness', 'domain': 'all'})
    manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee', 'source_closure': ['a.zig'],
                'components': {'compiler_patch': ['p'], 'runtime': ['r'], 'toolchain': ['t']},
                'allowed_assumptions': [],
                'roots': [{'id': function, 'function': function, 'air': ['f.json'], 'namespace': namespace,
                           'prefix': '', 'contracts': ['tests/roadmap/claims/Fixture.lean'],
                           'goals': goals, 'assumptions': [], 'exclusions': []}]}
    path = out / f'{theorem.rsplit(".", 1)[1]}-{strength}.json'
    path.write_text(json.dumps(manifest))
    # A regression fixture, not a release claim: CI's selected translation may dirty the tree.
    return subprocess.run([sys.executable, 'scripts/claims.py', 'check', str(path), '--allow-dirty',
                           '--assurance', str(out / 'assurance.json')], capture_output=True, text=True)
accepted, rejected = run('partial_correctness'), run('total_correctness')
assert accepted.returncode == 0, accepted.stderr
assert rejected.returncode == 1, rejected.stderr
goal = json.loads(rejected.stdout)['roots'][0]['goals'][-1]
assert (goal['status'], goal['derived_strength']) == ('rejected', 'partial_correctness'), goal
# Bounded and unconditional concurrent returns meet a total goal about their computation (the
# fixed initial memory scopes the concurrent ones); a premise-dependent return, a diverging
# loop's refutation and a diverging program's refutation do not.
for theorem, namespace, function, domain in (
        ('ClaimFixture.exit_within', 'ClaimFixture', 'exitBody', 'scoped: loop state ()'),
        ('ClaimFixture.countdown_bounded', 'Zig.Conc.Total', 'countdown', 'scoped: initial memory {}'),
        ('ClaimFixture.countdown_eventually', 'Zig.Conc.Total', 'countdown', 'scoped: initial memory {}')):
    accepted = run('total_correctness', theorem, namespace, function, domain)
    assert accepted.returncode == 0, (theorem, accepted.stderr)
for theorem, namespace, function in (('ClaimFixture.countdown_under', 'Zig.Conc.Total', 'countdown'),
                                     ('ClaimFixture.stuck_under_false', 'Zig.Conc.Total', 'stuck'),
                                     ('ClaimFixture.spin_not_within', 'ClaimFixture', 'spinBody')):
    rejected = run('total_correctness', theorem, namespace, function, 'scoped: fixture')
    assert rejected.returncode == 1, (theorem, rejected.stderr)
    goal = json.loads(rejected.stdout)['roots'][0]['goals'][-1]
    assert (goal['status'], goal['derived_strength']) == ('rejected', None), goal
print('claim-strength regressions passed')
PY
