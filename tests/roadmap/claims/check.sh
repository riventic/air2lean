#!/usr/bin/env bash
# Extract real statement structures from Fixture.lean, require them to match the checked-in
# fixture report, then check accepted and overstated manifest goals against that report.
# --write (scripts/regen.sh): regenerate fixture-report.json from the extraction instead: the
# committed report's keys, theorem fields and node modules are kept, their values refreshed.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
write=0
case "${1:-}" in
  '') ;;
  --write) write=1 ;;
  *) echo "usage: tests/roadmap/claims/check.sh [--write]" >&2; exit 2 ;;
esac
out=.lake/assurance/claims
mkdir -p "$out"
# The unit tests (Python only) run meanwhile; their result is required below.
tests_pid=
trap '[ -z "$tests_pid" ] || kill "$tests_pid" 2>/dev/null || true' EXIT
if [ "$write" = 0 ]; then
  python3 tests/roadmap/claims/test_claims.py > "$out/test_claims.log" 2>&1 &
  tests_pid=$!
fi
# The fixtures are the library Claims (tests/roadmap/lakefile.toml), built by Lake with what they
# import (scripts/fixtures.py; run this under scripts/build-guard.py). Each audit binds the
# Lake-built outputs it audits (the compiler-owned run binding, theorem_universe).
python3 -B scripts/fixtures.py build Claims
python3 -B scripts/fixtures.py audit Fixture --theorem-roots --output "$out/assurance.json"
python3 -B scripts/fixtures.py audit AllocatorApplications --theorem-roots --output "$out/allocator-applications.json"
python3 -B scripts/fixtures.py audit AllocatorImported --theorem-roots --output "$out/allocator-imported.json"
python3 -B scripts/fixtures.py audit AllocatorImported --output "$out/allocator-imported-all.json"
python3 -B tests/roadmap/claims/test_allocator_applications.py "$out/allocator-applications.json"
python3 -B tests/roadmap/claims/test_allocator_imported.py "$out/allocator-imported.json" "$out/allocator-imported-all.json"
if [ "$write" = 1 ]; then
  python3 - "$out/assurance.json" <<'PY'
import json, sys
from pathlib import Path
path = Path('tests/roadmap/claims/fixture-report.json')
old, new = json.loads(path.read_text()), json.loads(Path(sys.argv[1]).read_text())
fields = set().union(*(t.keys() for t in old['theorems']))
# The selected source is unchanged; its defining module comes from the real Unit plan.
modules = set(new['modules'])
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
def run(strength, theorem='ClaimFixture.fret_partial', namespace='ClaimFixture', function='ret', domain='all'):
    goals = [{'theorem': 'ClaimFixture.fret_total', 'strength': 'total_correctness', 'domain': 'all'},
             {'theorem': theorem, 'strength': strength, 'domain': domain}]
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
spoofs = ('ClaimFixture.spoof_eventually', 'ClaimFixture.spoof_within', 'ClaimFixture.spoof_within_sym',
          'ClaimFixture.spoof_under')
# The runs are independent (one manifest file each): they run at once.
from concurrent.futures import ThreadPoolExecutor
import os
calls = [lambda: run('partial_correctness'), lambda: run('total_correctness'),
         lambda: run('total_correctness', 'ClaimFixture.tret_total'),
         *(lambda t=t: run('safety', t, domain='scoped: fixture') for t in spoofs)]
with ThreadPoolExecutor(int(os.environ.get('AIR2LEAN_JOBS') or min(4, os.cpu_count() or 1))) as pool:
    accepted, rejected, accepted_thread, *rejected_spoofs = pool.map(lambda call: call(), calls)
assert accepted.returncode == 0, accepted.stderr
assert rejected.returncode == 1, rejected.stderr
goal = json.loads(rejected.stdout)['roots'][0]['goals'][-1]
assert (goal['status'], goal['derived_strength']) == ('rejected', 'partial_correctness'), goal
# The total thread triple meets a total goal about the root. The spoofs of reserved head names
# (declared in Fixture.lean, audited without a name clash) meet no goal, not even safety: a
# reserved name supports no claim, whatever its declaration.
assert accepted_thread.returncode == 0, accepted_thread.stderr
for theorem, rejected in zip(spoofs, rejected_spoofs):
    assert rejected.returncode == 1, (theorem, rejected.stderr)
    goal = json.loads(rejected.stdout)['roots'][0]['goals'][-1]
    assert (goal['status'], goal['derived_strength']) == ('rejected', None), goal
    assert 'reserved claim-head name' in goal['reason'], goal
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
if [ -n "$tests_pid" ]; then
  status=0
  wait "$tests_pid" || status=$?
  tests_pid=
  [ "$status" = 0 ] || { cat "$out/test_claims.log" >&2; echo 'test_claims.py failed' >&2; exit 1; }
  tail -3 "$out/test_claims.log"
fi
