#!/usr/bin/env bash
# Extract real conclusion shapes from Fixture.lean, require them to match the checked-in
# fixture report, then check accepted and overstated manifest goals against that report.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
python3 tests/roadmap/claims/test_claims.py
out=.lake/assurance/claims
mkdir -p "$out" .lake/build/lib/lean/tests/roadmap/claims
lake build ZigLean.Sep.Total ZigLean.Sep.Bounded ZigLean.Conc.Total
lake env lean -o .lake/build/lib/lean/tests/roadmap/claims/Fixture.olean tests/roadmap/claims/Fixture.lean
scripts/assumptions.sh --no-build --module tests.roadmap.claims.Fixture --output "$out/assurance.json"
python3 - "$out" <<'PY'
import json, subprocess, sys
from pathlib import Path
out = Path(sys.argv[1])
actual = json.loads((out / 'assurance.json').read_text())
fixture = json.loads(Path('tests/roadmap/claims/fixture-report.json').read_text())
shape = lambda r: {t['name']: t['conclusion'] for t in r['theorems']}
assert actual['status'] == 'pass', actual['violations']
assert shape(actual) == shape(fixture), (shape(actual), shape(fixture))
(out / 'profile.json').write_text(json.dumps({'name': 'legacy-abi64-le', 'zig_version': '0.16.0'}))
def run(strength, theorem='ClaimFixture.diverge_partial'):
    manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee', 'source_closure': ['a.zig'],
                'components': {'compiler_patch': ['p'], 'runtime': ['r'], 'toolchain': ['t']},
                'allowed_assumptions': [],
                'roots': [{'id': 'diverge', 'function': 'f', 'air': ['f.json'], 'namespace': 'ClaimFixture',
                           'prefix': '', 'contracts': ['tests/roadmap/claims/Fixture.lean'],
                           'goals': [{'theorem': 'ClaimFixture.ret_total', 'strength': 'total_correctness', 'domain': 'all'},
                                     {'theorem': theorem, 'strength': strength, 'domain': 'all'}],
                           'assumptions': [], 'exclusions': []}]}
    path = out / f'{theorem.rsplit(".", 1)[1]}-{strength}.json'
    path.write_text(json.dumps(manifest))
    # A regression fixture, not a release claim: CI's selected translation may dirty the tree.
    return subprocess.run([sys.executable, 'scripts/claims.py', 'check', str(path), '--allow-dirty',
                           '--assurance', str(out / 'assurance.json')], capture_output=True, text=True)
accepted, rejected = run('partial_correctness'), run('total_correctness')
assert accepted.returncode == 0, accepted.stderr
assert rejected.returncode == 1, rejected.stderr
goal = json.loads(rejected.stdout)['roots'][0]['goals'][1]
assert (goal['status'], goal['derived_strength']) == ('rejected', 'partial_correctness'), goal
# Bounded and unconditional concurrent returns meet a total goal; a premise-dependent return,
# a diverging loop's refutation and a diverging program's refutation do not.
for theorem in ('ClaimFixture.exit_within', 'ClaimFixture.countdown_bounded', 'ClaimFixture.countdown_eventually'):
    accepted = run('total_correctness', theorem)
    assert accepted.returncode == 0, (theorem, accepted.stderr)
for theorem in ('ClaimFixture.countdown_under', 'ClaimFixture.stuck_under_false', 'ClaimFixture.spin_not_within'):
    rejected = run('total_correctness', theorem)
    assert rejected.returncode == 1, (theorem, rejected.stderr)
    goal = json.loads(rejected.stdout)['roots'][0]['goals'][1]
    assert (goal['status'], goal['derived_strength']) == ('rejected', None), goal
print('claim-strength regressions passed')
PY
