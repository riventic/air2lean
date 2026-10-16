#!/usr/bin/env bash
# Actual Lean environment regressions; run under the same guard as other proof checks.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
cd "$repo_root"
python3 -B scripts/lean-deps.py --build tests/roadmap/assurance
python3 tests/roadmap/assurance/test_policy.py
python3 tests/roadmap/assurance/test_tool_cache.py
out=.lake/assurance/regressions
fixtures=.lake/assurance/fixtures/lean  # not .lake/build: `lake env` would let tests/ shadow theorem-universe modules
mkdir -p "$out" "$fixtures/tests/roadmap/assurance"
export LEAN_PATH="$PWD/$fixtures${LEAN_PATH:+:$LEAN_PATH}"
for fixture in Good HiddenDependency HiddenWrapper ProjectAxiom UnexpectedOpaque CompilerRedirection NativeProof ExternDefinition FloatLabels StatementBinding MetaCode PartialInTheorem; do
  lake env lean -o "$fixtures/tests/roadmap/assurance/$fixture.olean" \
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
# Engine code (a `partial def` and an `initialize` no theorem reaches) needs no premise; the same
# kind of opaque that a theorem uses does, whatever it is named.
scripts/assumptions.sh --no-build --module tests.roadmap.assurance.MetaCode --output "$out/MetaCode.json"
for fixture in HiddenWrapper ProjectAxiom UnexpectedOpaque PartialInTheorem CompilerRedirection NativeProof ExternDefinition; do
  status=0
  scripts/assumptions.sh --no-build --module "tests.roadmap.assurance.$fixture" \
    --output "$out/$fixture.json" || status=$?
  [ "$status" = 1 ] || { echo "error: $fixture must fail policy (exit 1), got $status" >&2; exit 1; }
done
# Statement-only dependencies (I06 goal binding): the real extraction must match the
# checked-in entries that tests/roadmap/coverage-report/test_coverage.py binds goals against.
scripts/assumptions.sh --no-build --module tests.roadmap.assurance.StatementBinding \
  --output "$out/statement-binding.json"
# Ordinary imports must expose unused private definitions and generated recursors to the
# opt-in all-declaration audit without changing the default theorem/boundary audit.
python3 - "$out" "$fixtures" <<'PY'
import json, subprocess, sys
from pathlib import Path
root, fixtures = map(Path, sys.argv[1:])
module = 'AssuranceAllDeclarations'
fixture = root / (module + '.lean')
fixture.write_text('''namespace AssuranceAllDeclarations
private def unusedHelper : Nat := 41
def unusedValue : Nat := unusedHelper + 1
inductive UnusedTag where | value (payload : Nat)
theorem checked : True := True.intro
end AssuranceAllDeclarations
''')

def lean(*args):
    result = subprocess.run(['lake', 'env', 'lean', *map(str, args)], text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(result.stdout)
    return result.stdout

lean('-R', root, '-o', fixtures / (module + '.olean'), fixture)
driver = root / 'all-declarations.lean'
audit = '#assurance_audit ["' + module + '"]\n'
driver.write_text('import tools.Assurance\nimport ' + module + '\n' + audit +
                  'set_option air2lean.assurance.allDeclarations true\n' + audit)
output = lean(driver)
records = [line.removeprefix('AIR2LEAN_ASSURANCE_JSON:') for line in output.splitlines()
           if line.startswith('AIR2LEAN_ASSURANCE_JSON:')]
assert len(records) == 2, output
default, enabled = map(json.loads, records)
assert 'selected_declaration_roots' not in default
assert set(enabled) == set(default) | {'selected_declaration_roots'}
for field in ('schema_version', 'modules', 'theorems', 'project_declarations'):
    assert default[field] == enabled[field], field
default_nodes = {n['name']: n for n in default['nodes']}
enabled_nodes = {n['name']: n for n in enabled['nodes']}
assert all(enabled_nodes[name] == node for name, node in default_nodes.items())
roots = enabled['selected_declaration_roots']
assert len(roots) == len(set(roots)), roots
assert set(roots) == {n['name'] for n in enabled['nodes'] if n['module'] == module}
assert module + '.unusedValue' in roots and module + '.unusedValue' not in default_nodes
private = [n for n in enabled['nodes'] if n.get('user_name') == module + '.unusedHelper']
assert len(private) == 1 and private[0]['name'] in roots, private
assert private[0]['name'] not in default_nodes, private
assert any(n['name'] == module + '.UnusedTag.rec' and n['kind'] == 'recursor'
           and n['name'] in roots for n in enabled['nodes'])
print('assurance opt-in all-declaration regression passed')
PY
python3 - "$out/statement-binding.json" <<'PY'
import json, sys
from pathlib import Path
actual = json.loads(Path(sys.argv[1]).read_text())
expected = json.loads(Path('tests/roadmap/coverage-report/statement-binding.json').read_text())
fields = ('name', 'module', 'dependencies', 'statement_dependencies', 'conclusion_dependencies', 'conclusion', 'statement')
assert actual['status'] == 'pass', actual['violations']
assert [{k: t[k] for k in fields} for t in actual['theorems']] == expected['theorems'], actual['theorems']
PY
# Float-semantics labels (docs/float-semantics.md): unlabeled, mislabeled and binary claims fail.
python3 - "$out" <<'PY'
import json, sys
from pathlib import Path
registry = json.loads(Path('assurance/float-semantics.json').read_text())
key = 'tests.roadmap.assurance.FloatLabels::AssuranceFixture.float_add_self'
T = ['aarch64-macos', 'x86_64-linux']
for name, entry in [('ieee', {'semantics': 'ieee', 'targets': T, 'correspondence': 'model'}),
                    ('abstract', {'semantics': 'abstract-spec', 'targets': T, 'correspondence': 'model'}),
                    ('binary', {'semantics': 'ieee', 'targets': T, 'correspondence': 'binary'})]:
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
    ('PartialInTheorem', 'AssuranceFixture.wpWalk', 'unexpected-opaque'),
    ('ExternDefinition', 'AssuranceFixture.externalDefinition', 'unexpected-project-extern')]:
    report = json.loads((root/(name+'.json')).read_text())
    assert any(v['name'] == rejected and v['trust_class'] == trust for v in report['violations']), report['violations']
    assert all(not t['allowed'] for t in report['theorems'])
meta = json.loads((root/'MetaCode.json').read_text())
assert meta['status'] == 'pass', meta['violations']
meta_classes = {n['user_name']: n['trust_class'] for n in meta['nodes'] if n['kind'] == 'opaque' and n['module'].startswith('tests.')}
assert meta_classes == {'AssuranceFixture.metaWalk': 'meta-code-opaque', 'AssuranceFixture.metaCache': 'meta-code-opaque'}, meta_classes
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
