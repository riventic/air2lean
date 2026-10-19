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
  flags=()
  case "$fixture" in
    ProjectAxiom|UnexpectedOpaque|CompilerRedirection|ExternDefinition) flags+=(--all-declarations);;
  esac
  scripts/assumptions.sh --no-build --module "tests.roadmap.assurance.$fixture" \
    --output "$out/$fixture.json" "${flags[@]}" || status=$?
  [ "$status" = 1 ] || { echo "error: $fixture must fail policy (exit 1), got $status" >&2; exit 1; }
done
# Statement-only dependencies (I06 goal binding): the real extraction must match the
# checked-in entries that tests/roadmap/coverage-report/test_coverage.py binds goals against.
scripts/assumptions.sh --no-build --module tests.roadmap.assurance.StatementBinding \
  --output "$out/statement-binding.json"
# Ordinary imports must expose unused private definitions and generated recursors to the
# opt-in all-declaration audit without changing the default theorem/boundary audit.
python3 - "$out" "$fixtures" <<'PY'
import contextlib, copy, importlib.util, io, json, subprocess, sys, tempfile
from pathlib import Path
root, fixtures = map(Path, sys.argv[1:])
module = 'AssuranceAllDeclarations'
fixture = root / (module + '.lean')
fixture.write_text('''import ZigLean.Sep.Full.Triple
import ZigLean.Sep.Full.Conc
namespace AssuranceAllDeclarations
private def unusedHelper : Nat := 41
def unusedValue : Nat := unusedHelper + 1
inductive UnusedTag where | value (payload : Nat)
theorem checked : True := True.intro
end AssuranceAllDeclarations
namespace AssuranceProgramControls
open Zig
def noAnswer {α : Type} (c : MemM α) : Prop := ∀ m, (c.run m).run ≠ none
private def hiddenNoAnswer {α : Type} (c : MemM α) : Prop := ∀ m, (c.run m).run ≠ none
abbrev ProgramAlias (α : Type) := MemM α
def aliasNoAnswer (c : ProgramAlias Unit) : Prop := ∀ m, (c.run m).run ≠ none
def higherOrder (c : Nat → MemM Unit) : Prop := ∀ n m, ((c n).run m).run ≠ none
abbrev PredicateAlias := (Nat → MemM Unit) → Prop
def predicateAlias : PredicateAlias := fun c => ∀ n m, ((c n).run m).run ≠ none
def PredicateSort := Prop
def predicateSort (c : MemM Unit) : PredicateSort := ∀ m, (c.run m).run ≠ none
def HiddenProp : Type := Prop
def hiddenPropJudgment (c : MemM Unit) : HiddenProp := ∀ m, (c.run m).run ≠ none
def hiddenProofProposition : HiddenProp := True
def hiddenProofValue : hiddenProofProposition := True.intro
def hiddenForallProof (_ : MemM Unit) : hiddenProofProposition := True.intro
def hiddenLetProof : (let T := MemM Unit; ∀ _ : T, hiddenProofProposition) := fun _ => True.intro
attribute [irreducible] HiddenProp
def programValue : MemM Unit := pure ()
def writtenOut (_ : Zig.Mem → Option (Except Zig.Error (Unit × Zig.Mem))) : Prop := True
def localResult (Result : Type) (x : Result) : Prop := x = x
def proofValue : ∀ (_ : MemM Unit), True := fun _ => True.intro
def bodyOnly : Prop := ∀ (_ : MemM Unit), True
theorem bodyOnlyProof : bodyOnly := fun _ => True.intro
def proofTypeDependency (_ : bodyOnly) : Prop := True
def proofBodyDependency : Prop := bodyOnlyProof = bodyOnlyProof
structure Box (α : Type) where
  payload : α
def ordinaryBox (b : Box Nat) : Prop := b.payload = 0
def programBox (b : Box (MemM Unit)) : Prop := ∀ m, (b.payload.run m).run ≠ none
structure Paused where
  «continue» : Unit → MemM Unit
def pausedProperty (p : Paused) : Prop := ∀ m, ((p.«continue» ()).run m).run ≠ none
structure PlainSpec where
  count : Nat
  values : List Nat
structure ContractSpec where
  action : Unit → MemM Unit
  law : ∀ m, ((action ()).run m).run ≠ none
structure IndexedSpec (c : MemM Unit) : Type where
  law : ∀ m, (c.run m).run ≠ none
structure UnknownSpec (HiddenProof : Type) where
  payload : HiddenProof
structure StringSpec where
  label : String
end AssuranceProgramControls
-- Validate the existing kernel API contract separately from the report: check returns
-- the signature's TYPE (its sort up to kernel equality), including metadata/let wrappers.
run_meta do
  let env ← Lean.getEnv
  for (name, expected) in [(``AssuranceProgramControls.hiddenProofValue, true),
      (``AssuranceProgramControls.hiddenForallProof, true),
      (``AssuranceProgramControls.hiddenLetProof, true),
      (``AssuranceProgramControls.programValue, false),
      (``AssuranceProgramControls.PlainSpec, false)] do
    let info ← Lean.getConstInfo name
    for signature in [info.type, Lean.Expr.mdata {} info.type,
        Lean.Expr.letE `unused (Lean.mkConst ``Nat) (Lean.mkNatLit 0) info.type true] do
      let .ok sort := Lean.Kernel.check env {} signature
        | throwError "kernel signature check failed: {name}"
      let .ok proof := Lean.Kernel.isDefEq env {} sort (Lean.mkSort .zero)
        | throwError "kernel sort check failed: {name}"
      unless proof == expected do
        throwError "kernel check did not return the expected signature sort: {name}"
  match Lean.Kernel.check env {} (Lean.mkConst `AssuranceMissingSignature) with
  | .error _ => pure ()
  | .ok _ => throwError "unknown kernel signature must return an error"
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
assert set(enabled) == set(default) | {'selected_declaration_roots', 'selected_declaration_evidence'}
for field in ('schema_version', 'modules', 'theorems', 'project_declarations'):
    assert default[field] == enabled[field], field
default_nodes = {n['name']: n for n in default['nodes']}
enabled_nodes = {n['name']: n for n in enabled['nodes']}
assert all(enabled_nodes[name] == node for name, node in default_nodes.items())
roots = enabled['selected_declaration_roots']
assert len(roots) == len(set(roots)), roots
assert roots != sorted(roots), 'the fixture must exercise Lean Name.lt rather than string ordering'
assert set(roots) == {n['name'] for n in enabled['nodes'] if n['module'] == module}
assert module + '.unusedValue' in roots and module + '.unusedValue' not in default_nodes
private = [n for n in enabled['nodes'] if n.get('user_name') == module + '.unusedHelper']
assert len(private) == 1 and private[0]['name'] in roots, private
assert private[0]['name'] not in default_nodes, private
assert any(n['name'] == module + '.UnusedTag.rec' and n['kind'] == 'recursor'
           and n['name'] in roots for n in enabled['nodes'])
evidence = enabled['selected_declaration_evidence']
assert [row['name'] for row in evidence] == roots
by_user = {row['user_name']: row for row in evidence}
assert by_user['AssuranceProgramControls.hiddenNoAnswer']['name'] in roots
assert by_user['AssuranceProgramControls.hiddenNoAnswer']['prop_valued'] is True
assert 'Zig.Result' not in by_user['AssuranceProgramControls.localResult']['original_type_constants']
# Exercise the supported policy/kernel-replay consumer, not just the raw extractor.
reports = []
for name, flags in [('default', []), ('all', ['--all-declarations'])]:
    report_path = root / ('all-declarations-' + name + '.json')
    subprocess.run(['scripts/assumptions.sh', '--no-build', '--module', module,
                    '--output', str(report_path), *flags], check=True)
    reports.append(json.loads(report_path.read_text()))
default_report, enabled_report = reports
assert all(report['status'] == 'pass' for report in reports), reports
assert 'selected_declaration_roots' not in default_report
assert 'framework_candidates' not in default_report
assert enabled_report['selected_declaration_roots'] == roots
assert {n['name'] for n in enabled_report['nodes']} == set(enabled_nodes)
assert all(report['kernel_replay']['status'] == 'pass' for report in reports)
framework = enabled_report['framework_candidates']
assert framework['scope'] == 'selected-modules-only' and framework['complete'] is False
assert framework['ordinary_exemptions'] == []
assert [row['name'] for row in framework['declarations']] == roots
classified = {row['user_name']: row for row in framework['declarations']}
for name in ('noAnswer', 'hiddenNoAnswer', 'aliasNoAnswer', 'higherOrder', 'predicateAlias', 'predicateSort', 'hiddenPropJudgment', 'programBox', 'pausedProperty', 'bodyOnly', 'proofTypeDependency', 'proofBodyDependency'):
    row = classified['AssuranceProgramControls.' + name]
    assert row['prop_valued'] is True and row['verdict'] == 'candidate', row
    assert 'Zig.MemM' in row['program_dependencies'], row
for name in ('localResult', 'ordinaryBox', 'writtenOut'):
    row = classified['AssuranceProgramControls.' + name]
    assert row['verdict'] == 'unknown' and row['program_dependencies'] == [], row
assert classified['AssuranceProgramControls.proofValue']['is_proof'] is True
assert classified['AssuranceProgramControls.proofValue']['prop_valued'] is False
assert classified['AssuranceProgramControls.proofValue']['verdict'] == 'unknown'
assert classified['AssuranceProgramControls.hiddenProofValue']['is_proof'] is True
assert classified['AssuranceProgramControls.hiddenProofValue']['prop_valued'] is False
assert classified['AssuranceProgramControls.hiddenProofValue']['verdict'] == 'unknown'
assert classified['AssuranceProgramControls.hiddenProofValue']['original_type_constants'] == ['AssuranceProgramControls.hiddenProofProposition']
assert classified['AssuranceProgramControls.hiddenForallProof']['is_proof'] is True
assert classified['AssuranceProgramControls.hiddenForallProof']['prop_valued'] is False
assert classified['AssuranceProgramControls.hiddenForallProof']['verdict'] == 'unknown'
assert 'AssuranceProgramControls.hiddenProofProposition' in classified['AssuranceProgramControls.hiddenForallProof']['original_type_constants']
assert 'Zig.MemM' in classified['AssuranceProgramControls.hiddenForallProof']['original_type_constants']
assert classified['AssuranceProgramControls.hiddenLetProof']['is_proof'] is True
assert classified['AssuranceProgramControls.hiddenLetProof']['prop_valued'] is False
assert classified['AssuranceProgramControls.hiddenLetProof']['verdict'] == 'unknown'
assert classified['AssuranceProgramControls.programValue']['is_proof'] is False
assert classified['AssuranceProgramControls.programValue']['verdict'] == 'unknown'
assert classified['AssuranceProgramControls.bodyOnly']['original_type_constants'] == []
assert 'Zig.MemM' in classified['AssuranceProgramControls.bodyOnly']['original_body_constants']
assert 'AssuranceProgramControls.bodyOnly' in classified['AssuranceProgramControls.proofTypeDependency']['original_type_constants']
assert 'AssuranceProgramControls.bodyOnlyProof' in classified['AssuranceProgramControls.proofBodyDependency']['original_body_constants']
assert classified['AssuranceProgramControls.bodyOnlyProof']['is_proof'] is True
assert 'AssuranceProgramControls.HiddenProp' in classified['AssuranceProgramControls.hiddenPropJudgment']['original_type_constants']
assert classified['AssuranceProgramControls.writtenOut']['prop_valued'] is True
for name in ('PlainSpec', 'ContractSpec', 'IndexedSpec', 'UnknownSpec', 'StringSpec'):
    row = classified['AssuranceProgramControls.' + name]
    assert row['verdict'] == 'unknown' and row['ordinary_exemption'] is False, row
assert classified['AssuranceProgramControls.IndexedSpec']['prop_valued'] is False
assert 'Zig.MemM' in classified['AssuranceProgramControls.IndexedSpec']['program_dependencies']
# Typed evidence uses the existing artifact freshness binding; changed oleans must reject it.
spec = importlib.util.spec_from_file_location('assumptions', Path('scripts/assumptions.py').resolve())
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
# Malformed evidence must use the normal validation error, not leak re's TypeError.
malformed = copy.deepcopy(enabled)
malformed['selected_declaration_evidence'][0]['kernel_fingerprint'] = 17
try:
    audit.framework_candidates(malformed)
except ValueError as error:
    assert 'kernel fingerprint' in str(error), error
else:
    raise AssertionError('non-string kernel fingerprint must be rejected')
# Resolve every canonical name even when the selected source does not mention it. This
# mutation changes only this Python process's input, not a shared source or tool artifact.
canonical = audit.framework_runtime_types
missing_name = 'Zig.Conc.MissingFrameworkFamily'
audit.framework_runtime_types = lambda: (*canonical()[:-1], missing_name)
try:
    diagnostic = io.StringIO()
    with contextlib.redirect_stderr(diagnostic):
        try:
            audit.extract([module], False, all_declarations=True)
        except RuntimeError as error:
            assert 'command failed' in str(error), error
            assert missing_name in diagnostic.getvalue(), diagnostic.getvalue()
            assert 'unknown' in diagnostic.getvalue().lower(), diagnostic.getvalue()
        else:
            raise AssertionError('a missing canonical family must fail actual Lean extraction')
finally:
    audit.framework_runtime_types = canonical
audit.verify_fresh(enabled_report, allow_dirty=True)
artifact = Path(next(row['olean'] for row in enabled_report['freshness']['artifacts']
                     if row['module'] == module))
assert artifact.resolve() == (fixtures / (module + '.olean')).resolve()
before = audit.file_sha256(artifact)
with tempfile.TemporaryDirectory(dir=root) as scratch:
    original = Path(scratch) / 'original.olean'
    artifact.replace(original)
    try:
        artifact.write_bytes(b'changed fixture artifact')
        mutated = audit.file_sha256(artifact)
        try:
            audit.verify_fresh(enabled_report, allow_dirty=True)
        except ValueError as error:
            assert f'{module} olean changed' in str(error), error
            rejection = str(error)
        else:
            raise AssertionError('changed artifact must invalidate typed evidence')
    finally:
        artifact.unlink(missing_ok=True)
        original.replace(artifact)
audit.verify_fresh(enabled_report, allow_dirty=True)
restored = audit.file_sha256(artifact)
assert restored == before and mutated != before
print('typed freshness control: ' + json.dumps({'before': before, 'mutated': mutated,
                                               'restored': restored, 'rejection': rejection}))
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
# These ACTUAL compiled negative fixtures still fail policy; their independent candidate
# evidence must expose non-definitional boundaries on both the boundary and its dependent.
for fixture, names in {
    'ProjectAxiom': ('unexpectedProjectAxiom', 'axiomWrapper'),
    'UnexpectedOpaque': ('unexpectedOpaque', 'opaqueWrapper'),
    'CompilerRedirection': ('logicalDefinition', 'logicalWrapper'),
    'ExternDefinition': ('externalDefinition', 'unusedExternalDefinition', 'external_spec'),
}.items():
    report = json.loads((root/(fixture+'.json')).read_text())
    summary = report['framework_candidates']
    assert summary['complete'] is False and summary['ordinary_exemptions'] == []
    by_name = {n['user_name']: n for n in summary['declarations']}
    for name in names:
        row = by_name['AssuranceFixture.' + name]
        assert row['unresolved_dependency'] is True and row['ordinary_exemption'] is False, row
print('assurance environment regressions passed')
PY

bash tests/roadmap/assurance/import-metadata.sh "$out/import-metadata.json"
