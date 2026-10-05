#!/usr/bin/env bash
# Actual Lean environment regressions; run under the same guard as other proof checks.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
python3 tests/roadmap/assurance/test_policy.py
python3 tests/roadmap/assurance/test_tool_cache.py
out=.lake/assurance/regressions
mkdir -p "$out" .lake/build/lib/lean/tests/roadmap/assurance
for fixture in Good HiddenDependency HiddenWrapper ProjectAxiom UnexpectedOpaque CompilerRedirection NativeProof ExternDefinition; do
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
