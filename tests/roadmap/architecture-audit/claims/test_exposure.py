#!/usr/bin/env python3
"""Architecture audit, area 4 (docs/architecture-audit/claims.md): exposure regressions.

Each case feeds kernel-extracted theorem entries (exposure-report.json, regenerated and
compared by check.sh) or a minimal evidence fixture through the shipped claim tooling
(scripts/claims.py, scripts/project.py, scripts/diff-report.py) and records the verdict.

Default mode pins the *current* verdicts: every case is EXPOSED (the tooling reports a claim it
should not). A fix flips its case; update EXPECTED_EXPOSED together with the fix so the
regression then guards the secure verdict. `--require-fixed` fails on any exposure (use it to
gate a hardening branch).
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.dont_write_bytecode = True


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


claims = load('claims', 'claims.py')
project = load('project', 'project.py')
diff_report = load('diff_report', 'diff-report.py')

SNAPSHOT = json.loads((HERE / 'exposure-report.json').read_text())
THEOREMS = {t['name']: t for t in SNAPSHOT['theorems']}
NODES = SNAPSHOT['generated_nodes']

# Lean counterexamples: theorem -> (root definition, declared strength, finding id).
LEAN_CASES = {
    'AuditClaims.unchecked_total': ('AuditClaims.root', 'total_correctness', 'S1'),
    'AuditClaims.spoofed_total': ('AuditClaims.root', 'total_correctness', 'S2'),
    'AuditClaims.hyp_is_claim': ('AuditClaims.root', 'total_correctness', 'S3'),
    'AuditClaims.unsat_pre': ('AuditClaims.root', 'total_correctness', 'S3'),
    'AuditClaims.total_false_pre': ('AuditClaims.spin', 'total_correctness', 'S3'),
    'AuditClaims.ground_instance': ('AuditClaims.root', 'total_correctness', 'S4'),
    'AuditClaims.root_in_post': ('AuditClaims.root', 'total_correctness', 'S5'),
    'AuditClaims.root_ignored': ('AuditClaims.root', 'total_correctness', 'S5'),
    'AuditClaims.spin_partial': ('AuditClaims.spin', 'partial_correctness', 'S6'),
    'AuditClaims.asm_divmod_total': ('Asm.divmod', 'total_correctness', 'S7'),
}
EXPECTED_EXPOSED = set(LEAN_CASES) | {'receipt-schema-skew', 'host-allowlist-masks-panic',
                                      'model-illegal-masks-native-value'}


def coverage_level(theorem_name, definition, strength):
    """Coverage level project.py assigns when this theorem is the root's only goal and every
    non-proof stage (translation, receipt, compile) passed."""
    theorem = THEOREMS[theorem_name]
    namespace, function = definition.split('.')
    generated_sha = hashlib.sha256(b'generated').hexdigest()
    with tempfile.TemporaryDirectory() as temp:
        base = Path(temp).resolve()
        contract = f'AuditClaims/{theorem["module"].split(".")[-1]}.lean'
        generated = NODES[definition]['module'].replace('.', '/')
        lib = str(base / '.lake/build/lib/lean')
        bundle = {'attempt': str(base / 'attempt'), 'root': base,
                  'nodes': NODES, 'theorems': {theorem_name: theorem},
                  'sources': {str(base / contract): 'contract-sha'},
                  'compiled': {f'{lib}/{generated}.olean', f'{lib}/{contract[:-5]}.olean'},
                  'profiles': {f'{generated}.lean': {'sha256': generated_sha}}}
        root = {'id': 'r', 'function': f'example.{function}', 'prefix': 'example.', 'namespace': namespace,
                'contracts': [contract], 'goals': [{'theorem': theorem_name, 'strength': strength, 'domain': 'all inputs'}]}
        compiled, goals = project.bind_receipt(root, base, generated_sha, bundle, {contract: 'contract-sha'})
    passed = {'status': 'passed'}
    record = {'stages': {'translated': passed, 'compiled': compiled, 'tested': {'status': 'not_run'}},
              'goals': goals, 'input_validation': passed, 'absence_claims': project.absence_claims(goals, {})}
    level, _ = project.coverage_level(record)
    return level, goals[0]


def lean_case(name):
    definition, strength, _ = LEAN_CASES[name]
    theorem = THEOREMS[name]
    report = {'schema_version': 1, 'status': 'pass', 'theorems': [theorem]}
    classified = {t['name']: t for t in claims.classify(report)['theorems']}
    goal = claims.check_goal({'theorem': name, 'strength': strength, 'domain': 'all inputs'}, classified)
    level, row = coverage_level(name, definition, strength)
    nonstandard = [a for a in theorem['axioms'] if a not in ('propext', 'Classical.choice', 'Quot.sound')]
    exposed = (theorem['allowed'] and not nonstandard and goal['status'] == 'accepted'
               and row['binding'] == 'direct' and level.startswith('functionally_verified'))
    return exposed, f'claims={goal["status"]}/{goal["derived_strength"]} binding={row["binding"]} level={level}'


def receipt_schema_skew():
    """proof-receipt.py seals schema 2 and its verifier demands 2; project.py coverage demands 1.
    A genuine current receipt therefore never binds: coverage cannot pass `compiled` end to end,
    while its unit tests use a schema-1 fake and a stub verifier."""
    source = (ROOT / 'scripts/proof-receipt.py').read_text()
    sealed_two = "{'schema': 2, 'status': 'audited'" in source and "receipt['schema'] == 2" in source
    with tempfile.TemporaryDirectory() as temp:
        attempt = Path(temp).resolve()
        (attempt / 'receipt.json').write_text(json.dumps({'schema': 2, 'status': 'audited'}))
        (attempt / 'plan.json').write_text(json.dumps({'modules': [], 'root': temp}))
        (attempt / 'audit.json').write_text(json.dumps({'status': 'pass', 'theorems': [], 'nodes': []}))
        (attempt / 'after.json').write_text(json.dumps({'profiles': {}, 'compiled': [], 'context': {'sources': []}}))
        bundle, reason = project.load_receipt(attempt, Path(temp) / 'unused-verifier.py', project.LIMITS)
    return sealed_two and bundle is None and 'schema-1' in (reason or ''), f'sealed schema 2; coverage: {reason}'


def host_allowlist_masks_panic():
    """Off Linux-x86_64 a function listed in tests/diff/<ex>/host.txt turns *any* disagreement,
    including a model panic against a native value, into `host_difference`, not `mismatch`."""
    status = diff_report.classify({'ok': 1}, {'fail': 'Zig.Error.overflow'}, diff_report.Kind.VALUE,
                                  diff_report.Kind.MODEL_PANIC, None, host=True)
    return status == diff_report.Status.HOST, f'native ok / model overflow panic -> {status.value}'


def model_illegal_masks_native_value():
    """A model `illegal`/`unspecified` result is an exclusion whatever the native side returned;
    only the per-function count is pinned, so the input it occurs on is not."""
    status = diff_report.classify({'ok': 7}, {'fail': 'Zig.Error.illegal'}, diff_report.Kind.VALUE,
                                  diff_report.Kind.ILLEGAL, None)
    return status == diff_report.Status.ILLEGAL, f'native ok / model illegal -> {status.value}'


PY_CASES = {'receipt-schema-skew': receipt_schema_skew, 'host-allowlist-masks-panic': host_allowlist_masks_panic,
            'model-illegal-masks-native-value': model_illegal_masks_native_value}


def main(argv):
    require_fixed = '--require-fixed' in argv
    failures = []
    results = {name: lean_case(name) for name in LEAN_CASES}
    results.update({name: case() for name, case in PY_CASES.items()})
    for name, (exposed, detail) in results.items():
        print(f'{"EXPOSED" if exposed else "fixed  "} {name}: {detail}')
        if require_fixed and exposed:
            failures.append(f'{name} is still exposed')
        elif not require_fixed and exposed != (name in EXPECTED_EXPOSED):
            failures.append(f'{name}: exposure changed (now {"exposed" if exposed else "fixed"}); '
                            'update EXPECTED_EXPOSED and docs/architecture-audit/claims.md')
    for failure in failures:
        print('FAIL ' + failure, file=sys.stderr)
    return 1 if failures else 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
