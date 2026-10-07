#!/usr/bin/env bash
# Actual Lean environment regressions; run under the same guard as other proof checks.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
python3 tests/roadmap/assurance/test_policy.py
python3 tests/roadmap/assurance/test_tool_cache.py
out=.lake/assurance/regressions
mkdir -p "$out" .lake/build/lib/lean/tests/roadmap/assurance
for fixture in Good HiddenDependency HiddenWrapper ProjectAxiom UnexpectedOpaque CompilerRedirection NativeProof ExternDefinition FloatLabels StatementBinding; do
  lake env lean -o ".lake/build/lib/lean/tests/roadmap/assurance/$fixture.olean" \
    "tests/roadmap/assurance/$fixture.lean"
done
python3 - "$out/policy.json" <<'PY'
import json, sys
from pathlib import Path
policy = json.loads(Path('assurance/policy.json').read_text())
policy['project_opaques']['tests.roadmap.assurance.Good::AssuranceFixture.checkedOpaque'] = 'Regression: opaque with a kernel-checked value, not an axiom.'
policy['project_externs']['tests.roadmap.assurance.ExternDefinition::AssuranceFixture.externalDefinition'] = {'targets': [{'kind': 'standard', 'backend': 'all', 'target': 'air2lean_assurance_fixture'}], 'reason': 'Regression of an explicitly reviewed runtime contract.'}
policy['project_externs']['tests.roadmap.assurance.ExternDefinition::AssuranceFixture.unusedExternalDefinition'] = {'targets': [{'kind': 'standard', 'backend': 'all', 'target': 'air2lean_assurance_unused_fixture'}], 'reason': 'Regression of an unused but explicitly reviewed runtime contract.'}
Path(sys.argv[1]).write_text(json.dumps(policy))
PY
scripts/assumptions.sh --no-build --module tests.roadmap.assurance.Good \
  --policy "$out/policy.json" --output "$out/good.json"
scripts/assumptions.sh --no-build --module tests.roadmap.assurance.ExternDefinition \
  --policy "$out/policy.json" --output "$out/extern-allowed.json"
for fixture in HiddenWrapper ProjectAxiom UnexpectedOpaque CompilerRedirection NativeProof ExternDefinition; do
  status=0
  scripts/assumptions.sh --no-build --module "tests.roadmap.assurance.$fixture" \
    --output "$out/$fixture.json" || status=$?
  [ "$status" = 1 ] || { echo "error: $fixture must fail policy (exit 1), got $status" >&2; exit 1; }
done
# Statement-only dependencies (I06 goal binding): the real extraction must match the
# checked-in entries that tests/roadmap/coverage-report/test_coverage.py binds goals against.
scripts/assumptions.sh --no-build --module tests.roadmap.assurance.StatementBinding \
  --output "$out/statement-binding.json"
python3 - "$out/statement-binding.json" <<'PY'
import json, sys
from pathlib import Path
actual = json.loads(Path(sys.argv[1]).read_text())
expected = json.loads(Path('tests/roadmap/coverage-report/statement-binding.json').read_text())
fields = ('name', 'module', 'dependencies', 'statement_dependencies', 'conclusion_dependencies', 'conclusion')
assert actual['status'] == 'pass', actual['violations']
assert [{k: t[k] for k in fields} for t in actual['theorems']] == expected['theorems'], actual['theorems']
PY
# Float-semantics labels (docs/float-semantics.md): unlabeled, mislabeled and binary claims fail.
python3 - "$out" <<'PY'
import json, sys
from pathlib import Path
registry = json.loads(Path('assurance/float-semantics.json').read_text())
key = 'tests.roadmap.assurance.FloatLabels::AssuranceFixture.float_add_self'
for name, entry in [('ieee', {'semantics': 'ieee', 'correspondence': 'model'}),
                    ('abstract', {'semantics': 'abstract-spec', 'correspondence': 'model'}),
                    ('binary', {'semantics': 'ieee', 'correspondence': 'binary'})]:
    Path(sys.argv[1], 'float-' + name + '.json').write_text(json.dumps(dict(registry, theorems=dict(registry['theorems'], **{key: entry}))))
PY
float_status() {
  local status=0
  scripts/assumptions.sh --no-build --module tests.roadmap.assurance.FloatLabels "$@" || status=$?
  echo "$status"
}
[ "$(float_status --output "$out/float-unlabeled.json")" = 1 ] || { echo 'error: unlabeled float theorem must fail policy' >&2; exit 1; }
[ "$(float_status --float-semantics "$out/float-abstract.json" --output "$out/float-mislabeled.json")" = 1 ] \
  || { echo 'error: abstract-spec label on an IEEE-operation theorem must fail policy' >&2; exit 1; }
[ "$(float_status --float-semantics "$out/float-binary.json" --output "$out/float-binary-report.json")" = 2 ] \
  || { echo 'error: binary-correspondence label must be rejected' >&2; exit 1; }
[ "$(float_status --float-semantics "$out/float-ieee.json" --output "$out/float-labeled.json")" = 0 ] \
  || { echo 'error: labeled float theorem must pass' >&2; exit 1; }
python3 scripts/float-semantics.py check-report --float-semantics "$out/float-ieee.json" "$out/float-labeled.json"
python3 - "$out" <<'PY'
import json, sys
from pathlib import Path
root = Path(sys.argv[1])
unlabeled = json.loads((root/'float-unlabeled.json').read_text())
assert any(v['name'] == 'AssuranceFixture.float_add_self' and v['trust_class'] == 'unlabeled-numerical-theorem'
           for v in unlabeled['violations']), unlabeled['violations']
mislabeled = json.loads((root/'float-mislabeled.json').read_text())
assert any(v['trust_class'] == 'float-semantics-mismatch' for v in mislabeled['violations']), mislabeled['violations']
labeled = json.loads((root/'float-labeled.json').read_text())
records = {t['name']: t.get('float_semantics') for t in labeled['theorems']}
assert records['AssuranceFixture.float_add_self']['label'] == 'ieee', records
assert records['AssuranceFixture.float_add_self']['binary_correspondence'] == 'not_claimed'
assert records['AssuranceFixture.nat_add_self'] is None, records
assert labeled['float_semantics']['labels'] == {'ieee': 1}, labeled['float_semantics']
PY
python3 - "$out" <<'PY'
import json, sys
from pathlib import Path
root = Path(sys.argv[1])
good = json.loads((root/'good.json').read_text())
assert good['status'] == 'pass'
assert {'AssuranceFixture.opaque_reflexive', 'AssuranceFixture.classical_allowed'} <= {t['name'] for t in good['theorems']}
private_names = {n['name'] for n in good['nodes'] if n.get('user_name') == 'AssuranceFixture.private_checked'}
assert private_names and private_names <= {t['name'] for t in good['theorems']}
for name, rejected, trust in [
    ('HiddenWrapper', 'sorryAx', 'sorry'),
    ('ProjectAxiom', 'AssuranceFixture.unexpectedProjectAxiom', 'unexpected-axiom'),
    ('UnexpectedOpaque', 'AssuranceFixture.unexpectedOpaque', 'unexpected-opaque'),
    ('ExternDefinition', 'AssuranceFixture.externalDefinition', 'unexpected-project-extern')]:
    report = json.loads((root/(name+'.json')).read_text())
    assert any(v['name'] == rejected and v['trust_class'] == trust for v in report['violations']), report['violations']
    assert all(not t['allowed'] for t in report['theorems'])
extern = json.loads((root/'extern-allowed.json').read_text())
assert extern['status'] == 'pass'
external_node = next(n for n in extern['nodes'] if n['name'] == 'AssuranceFixture.externalDefinition')
assert external_node['extern'] == [{'kind': 'standard', 'backend': 'all', 'target': 'air2lean_assurance_fixture'}]
assert external_node['extern_trust_class'] == 'allowed-project-extern'
assert extern['extractor']['cache_reused']
for fixture in ['HiddenWrapper', 'ProjectAxiom', 'UnexpectedOpaque', 'CompilerRedirection', 'NativeProof', 'ExternDefinition']:
    assert json.loads((root/(fixture+'.json')).read_text())['extractor']['cache_reused']
extern_rejected = json.loads((root/'ExternDefinition.json').read_text())
assert any(v['name'] == 'AssuranceFixture.unusedExternalDefinition' and v['trust_class'] == 'unexpected-project-extern' for v in extern_rejected['violations'])
assert 'AssuranceFixture.unusedExternalDefinition' not in extern_rejected['theorems'][0]['extern_dependencies']
native = json.loads((root/'NativeProof.json').read_text())
assert any(v['trust_class'] == 'compiler-proof-axiom' and '._native.native_decide.ax_' in v['name'] for v in native['violations'])
assert all(not t['allowed'] for t in native['theorems'])
redirected = json.loads((root/'CompilerRedirection.json').read_text())
assert any(v['name'] == 'AssuranceFixture.logicalDefinition' and v['trust_class'] == 'unexpected-compiler-redirection' for v in redirected['violations'])
print('assurance environment regressions passed')
PY
