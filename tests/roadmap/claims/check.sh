#!/usr/bin/env bash
# Extract real statement structures from Fixture.lean, require them to match the checked-in
# fixture report, then check accepted and overstated manifest goals against that report.
# --write (scripts/regen.sh): regenerate fixture-report.json from the extraction instead: the
# committed report's keys, theorem fields and node modules are kept, their values refreshed.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
python3 -B scripts/lean-deps.py --build tests/roadmap/claims
write=0
case "${1:-}" in
  '') ;;
  --write) write=1 ;;
  *) echo "usage: tests/roadmap/claims/check.sh [--write]" >&2; exit 2 ;;
esac
[ "$write" = 1 ] || python3 tests/roadmap/claims/test_claims.py
out=.lake/assurance/claims
mkdir -p "$out" .lake/build/lib/lean/tests/roadmap/claims
lake build ZigLean.Sep.Witness ZigLean.Sep.Bounded ZigLean.Conc.Own ZigLean.Conc.Total ZigLean.Sep.Full.Witness
lake env lean -o .lake/build/lib/lean/tests/roadmap/claims/Fixture.olean tests/roadmap/claims/Fixture.lean
scripts/assumptions.sh --no-build --module tests.roadmap.claims.Fixture --output "$out/assurance.json"
if [ "$write" = 1 ]; then
  python3 - "$out/assurance.json" <<'PY'
import json, sys
from pathlib import Path
path = Path('tests/roadmap/claims/fixture-report.json')
old, new = json.loads(path.read_text()), json.loads(Path(sys.argv[1]).read_text())
fields = set().union(*(t.keys() for t in old['theorems']))
modules = {n['module'] for n in old['nodes']}
nodes = new['nodes'] if isinstance(new['nodes'], list) else [dict(name=n, **v) for n, v in new['nodes'].items()]
report = {key: new[key] for key in old}
report['theorems'] = [{k: v for k, v in t.items() if k in fields} for t in new['theorems']]
report['nodes'] = [{k: n[k] for k in old['nodes'][0]} for n in nodes if n['module'] in modules]
text = json.dumps(report, indent=1) + '\n'
if text != path.read_text():
    path.write_text(text)
    print('wrote', path)
PY
  # Then every check below, as without --write: a failing extraction is not a fixture.
  python3 tests/roadmap/claims/test_claims.py
fi
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
# The library lemmas' companions live in ZigLean/Witnesses/*.lean, which no module imports
# (generated code must not import the witness commands, docs/claim-strength.md): the shipped-scope
# audit imports them because scripts/assumptions.py selects every ZigLean/**.lean module. Build
# them all here, and check that the extractor verifies a library lemma's companion from them.
# shellcheck disable=SC2046
lake build $(find ZigLean/Witnesses -name '*.lean' | sort | sed 's|/|.|g; s|\.lean$||')
scripts/assumptions.sh --no-build --module ZigLean.Bit --module ZigLean.Witnesses.Mem \
  --output "$out/library.json"
python3 - "$out/library.json" <<'PY'
import json, sys
report = json.load(open(sys.argv[1]))
found = {t['name']: t['statement']['witnesses'] for t in report['theorems']}
w = found['Zig.shlExact_of_noOverflow']['nonvacuity']
assert w == {'status': 'verified', 'theorem': 'Zig.shlExact_of_noOverflow.nonvacuous'}, w
print('library witness companions verified')
PY
