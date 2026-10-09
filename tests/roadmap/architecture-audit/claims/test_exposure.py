#!/usr/bin/env python3
"""Architecture audit, area 4 (docs/architecture-audit/claims.md): exposure regressions.

Each case feeds kernel-extracted theorem entries (exposure-report.json, regenerated and
compared by check.sh) or a minimal evidence fixture through the shipped claim tooling
(scripts/claims.py, scripts/project.py, scripts/diff-report.py) and records the verdict.

Default mode pins the *current* verdicts: a case in EXPECTED_EXPOSED must still be exposed (the
tooling reports a claim it should not), every other case must be fixed. A fix flips its case;
update EXPECTED_EXPOSED together with the fix so the regression then guards the secure verdict.
`--require-fixed` fails on any exposure; `--require-fixed=S2,S3` only on exposures of those
findings (use it to gate a hardening branch); `--finding ID` (repeatable) restricts the run to
those findings' cases.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
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
HEADS = claims.load_heads()

# Lean counterexamples: theorem -> (root definition, declared strength, finding id).
LEAN_CASES = {
    # S1/S7 originals fix a root argument (255, divisor 0): the derived domain (S4) now scopes them.
    'AuditClaims.unchecked_total': ('AuditClaims.root', 'total_correctness', 'S4'),
    'AuditClaims.unchecked_universal': ('AuditClaims.root', 'total_correctness', 'S1'),
    'AuditClaims.spoofed_within': ('AuditClaims.root', 'total_correctness', 'S2'),
    'AuditClaims.hyp_is_claim': ('AuditClaims.root', 'total_correctness', 'S3'),
    'AuditClaims.unsat_pre': ('AuditClaims.root', 'total_correctness', 'S3'),
    'AuditClaims.total_false_pre': ('AuditClaims.spin', 'total_correctness', 'S3'),
    'AuditClaims.ground_instance': ('AuditClaims.root', 'total_correctness', 'S4'),
    'AuditClaims.root_in_post': ('AuditClaims.root', 'total_correctness', 'S5'),
    'AuditClaims.root_ignored': ('AuditClaims.root', 'total_correctness', 'S5'),
    'AuditClaims.spin_partial': ('AuditClaims.spin', 'partial_correctness', 'S6'),
    'AuditClaims.asm_divmod_total': ('Asm.divmod', 'total_correctness', 'S4'),
    'AuditClaims.asm_divmod_universal': ('Asm.divmod', 'total_correctness', 'S7'),
}
FINDINGS = {name: finding for name, (_, _, finding) in LEAN_CASES.items()}
FINDINGS.update({'spoofed-total-head': 'S2', 'spoofed-registered-head': 'S2', 'receipt-schema-skew': 'F1',
                 'host-allowlist-masks-panic': 'F3', 'model-illegal-masks-native-value': 'F3',
                 'indexed-theorems-unaudited': 'F2', 'stale-report-accepted': 'H1'})
# Fixed: S1 (kernel replay rejects AuditClaims.Unchecked), F2, H1 (codex/fix-evidence-integrity),
# S2-S6 (codex/fix-claim-binding). Open: S7 (asm opaques), F1, F3.
EXPECTED_EXPOSED = {'AuditClaims.asm_divmod_universal', 'receipt-schema-skew',
                    'host-allowlist-masks-panic', 'model-illegal-masks-native-value'}


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
                  'nodes': NODES, 'theorems': THEOREMS,
                  'sources': {str(base / contract): 'contract-sha'},
                  'compiled': {f'{lib}/{generated}.olean', f'{lib}/{contract[:-5]}.olean'},
                  'profiles': {f'{generated}.lean': {'sha256': generated_sha}}}
        root = {'id': 'r', 'function': f'example.{function}', 'prefix': 'example.', 'namespace': namespace,
                'contracts': [contract], 'assumptions': [],
                'goals': [{'theorem': theorem_name, 'strength': strength, 'domain': 'all inputs'}]}
        compiled, goals = project.bind_receipt(root, base, generated_sha, bundle, {contract: 'contract-sha'})
    passed = {'status': 'passed'}
    record = {'stages': {'translated': passed, 'compiled': compiled, 'tested': {'status': 'not_run'}},
              'goals': goals, 'input_validation': passed, 'absence_claims': project.absence_claims(goals, {})}
    level, _ = project.coverage_level(record)
    return level, goals[0]


def verdict(name, definition, strength, heads=HEADS):
    theorem = THEOREMS[name]
    module = NODES[definition]['module']
    goal = claims.check_goal({'theorem': name, 'strength': strength, 'domain': 'all inputs'}, THEOREMS,
                             definition=definition, heads=heads,
                             generated=claims.generated_definitions(NODES, {module}), nodes=NODES)
    level, row = coverage_level(name, definition, strength)
    nonstandard = [a for a in theorem['axioms'] if a not in ('propext', 'Classical.choice', 'Quot.sound')]
    exposed = (theorem['allowed'] and not nonstandard and goal['status'] == 'accepted'
               and row['binding'] == 'direct' and level.startswith('functionally_verified'))
    detail = f'claims={goal["status"]}/{goal["derived_strength"]} binding={row["binding"]} level={level}'
    return exposed, detail + ('' if exposed or goal['status'] == 'accepted' else f' ({goal["reason"]})')


def lean_case(name):
    definition, strength, _ = LEAN_CASES[name]
    return verdict(name, definition, strength)


def spoofed_total_head():
    """A contract that defines its own `Zig.TotalTriple := True` cannot be audited next to the
    registered head that the extractor imports: the name clashes and the audit errors."""
    shadow = SNAPSHOT['shadow_audit']
    return shadow['status'] == 'pass', f'Shadow audit status={shadow["status"]} name_clash={shadow["name_clash"]}'


def spoofed_registered_head():
    """Once a head such as `Zig.TotalTripleWithin` is registered (codex/roadmap-batch8), a contract's
    same-named declaration (not imported by the audit, so no clash) is still not the pinned one."""
    heads = dict(HEADS, **{'Zig.TotalTripleWithin': {'module': 'ZigLean.Sep.Bounded', 'fingerprint': '0' * 32,
                                                      'claims': list(claims.CLAIMS), 'program': 3, 'state': []}})
    return verdict('AuditClaims.spoofed_within', 'AuditClaims.root', 'total_correctness', heads)


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


def indexed_theorems_unaudited():
    """F2: every theorem file docs/premise-index.md indexes must be compiled and audited (axioms,
    sorryAx, kernel replay), and a `declaration uses 'sorry'` warning must fail its compilation;
    Lean itself exits 0 on it."""
    if not (ROOT / 'scripts/theorem_universe.py').is_file():
        return True, 'no theorem universe: tutorials and tests/roadmap theorems are checked by exit code only'
    sys.path.insert(0, str(ROOT / 'scripts'))
    import premises
    import theorem_universe as universe
    shipped, units = universe.universe()
    repo = premises.load_repository(ROOT, premises.load_config(ROOT / premises.CONFIG))
    indexed = {f.rel for f in premises.theorem_files(repo)}
    unaudited = indexed - {u.file for u in units} - {m.replace('.', '/') + '.lean' for m in shipped}
    original = universe.run
    universe.run = lambda *a, **k: subprocess.CompletedProcess(a, 0, "F.lean:1:0: warning: declaration uses 'sorry'\n")
    try:
        with tempfile.TemporaryDirectory() as temp:
            sorry = universe.compile_unit('F.lean', '.', Path(temp) / 'F.olean', [], Path(temp) / 'F.log')
    finally:
        universe.run = original
    return bool(unaudited) or sorry is None, f'{len(indexed)} indexed files, {len(unaudited)} unaudited; sorry warning -> {sorry!r}'


def stale_report_accepted():
    """H1: claims.py check must bind an assurance report to the tree: a report whose recorded
    olean changed since the audit is stale, whatever its `status`."""
    with tempfile.TemporaryDirectory() as temp:
        base = Path(temp)
        olean = base / 'Stale.olean'
        olean.write_bytes(b'audited bytes')
        digest = hashlib.sha256(olean.read_bytes()).hexdigest()
        olean.write_bytes(b'bytes compiled after the audit')
        head = subprocess.run(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
        report = {'schema_version': 1, 'status': 'pass', 'theorems': [THEOREMS['AuditClaims.hyp_is_claim']],
                  'freshness': {'revision': {'head': head, 'tracked_dirty': False},
                                'lake_trace_check': {'modules': [], 'status': 'up-to-date'},
                                'artifacts': [{'module': 'Stale', 'olean': str(olean), 'olean_sha256': digest,
                                               'source': None, 'source_sha256': None}]}}
        (base / 'assurance.json').write_text(json.dumps(report))
        (base / 'profile.json').write_text(json.dumps({'name': 'legacy-abi64-le', 'zig_version': '0.16.0'}))
        manifest = {'schema': 1, 'profile': 'profile.json', 'float_semantics': 'ieee', 'source_closure': ['a.zig'],
                    'components': {'compiler_patch': ['p'], 'runtime': ['r'], 'toolchain': ['t']},
                    'allowed_assumptions': [],
                    'roots': [{'id': 'r', 'function': 'f', 'air': ['f.json'], 'namespace': 'AuditClaims', 'prefix': '',
                               'contracts': ['Vacuous.lean'], 'assumptions': [], 'exclusions': [],
                               'goals': [{'theorem': 'AuditClaims.hyp_is_claim', 'strength': 'safety', 'domain': 'all'}]}]}
        (base / 'project.json').write_text(json.dumps(manifest))
        command = [sys.executable, '-B', str(ROOT / 'scripts/claims.py'), 'check', str(base / 'project.json'),
                   '--assurance', str(base / 'assurance.json')]
        usage = subprocess.run(command[:4] + ['--help'], capture_output=True, text=True).stdout
        # A dirty checkout must not be the reason for the refusal: the stale olean must be.
        result = subprocess.run(command + (['--allow-dirty'] if '--allow-dirty' in usage else []),
                                capture_output=True, text=True)
    return 'stale' not in result.stderr, f'claims.py check on a stale report exits {result.returncode}: {result.stderr.strip()[-120:]}'


PY_CASES = {'spoofed-total-head': spoofed_total_head, 'spoofed-registered-head': spoofed_registered_head,
            'receipt-schema-skew': receipt_schema_skew, 'host-allowlist-masks-panic': host_allowlist_masks_panic,
            'model-illegal-masks-native-value': model_illegal_masks_native_value,
            'indexed-theorems-unaudited': indexed_theorems_unaudited, 'stale-report-accepted': stale_report_accepted}


def main(argv):
    required = None
    findings = {argv[i + 1] for i, arg in enumerate(argv) if arg == '--finding'}
    for arg in argv:
        if arg == '--require-fixed':
            required = set(FINDINGS.values())
        elif arg.startswith('--require-fixed='):
            required = set(arg.split('=', 1)[1].split(','))
    selected = lambda name: not findings or FINDINGS[name] in findings
    failures = []
    results = {name: lean_case(name) for name in LEAN_CASES if selected(name)}
    results.update({name: case() for name, case in PY_CASES.items() if selected(name)})
    for name, (exposed, detail) in results.items():
        print(f'{"EXPOSED" if exposed else "fixed  "} [{FINDINGS[name]}] {name}: {detail}')
        if required is not None:
            if exposed and FINDINGS[name] in required:
                failures.append(f'{name} ({FINDINGS[name]}) is still exposed')
        elif exposed != (name in EXPECTED_EXPOSED):
            failures.append(f'{name}: exposure changed (now {"exposed" if exposed else "fixed"}); '
                            'update EXPECTED_EXPOSED and docs/architecture-audit/claims.md')
    for failure in failures:
        print('FAIL ' + failure, file=sys.stderr)
    return 1 if failures else 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
