#!/usr/bin/env python3
"""Audit 2026-10-14, finding S1: a vacuous theorem backs `no-panic: proved`.

`claims.py assess` caps a functional theorem without a non-vacuity witness at `safety` instead of
rejecting it, and `project.py absence_claims` counts every `safety` goal as a proof of
`no-panic` (`outcomes.STRENGTH_ABSENCE['safety']`). The claims-audit fixtures
`AuditClaims.unsat_pre` (premise `x.toNat > 300` for `x : BitVec 8`) and
`AuditClaims.total_false_pre` (`FTotalTriple (fun _ => False) spin Q`) are both vacuous
(`Vacuity.lean`), and `AuditClaims.root 255` panics. Declared as `safety` goals with a scoped
domain, both are accepted, bound `direct`, and give `no-panic: proved`.

Prints `vulnerable` while that holds, `fixed` otherwise; `--require-fixed` exits 1 while
vulnerable. Uses the committed claims-audit report (`../../claims/exposure-report.json`).
"""
import hashlib
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / 'claims'))
require_fixed = '--require-fixed' in sys.argv
sys.argv = sys.argv[:1]
import test_exposure as T  # noqa: E402

project = T.project


def absence(theorem_name: str, strength: str, domain: str) -> dict:
    theorem = T.THEOREMS[theorem_name]
    definition = T.LEAN_CASES[theorem_name][0]
    namespace, function = definition.split('.')
    gsha = hashlib.sha256(b'generated').hexdigest()
    with tempfile.TemporaryDirectory() as temp:
        base = Path(temp).resolve()
        contract = f'AuditClaims/{theorem["module"].split(".")[-1]}.lean'
        generated = T.NODES[definition]['module'].replace('.', '/')
        lib = str(base / '.lake/build/lib/lean')
        bundle = {'attempt': str(base / 'attempt'), 'root': base, 'nodes': T.NODES, 'theorems': T.THEOREMS,
                  'sources': {str(base / contract): 'contract-sha'},
                  'compiled': {f'{lib}/{generated}.olean', f'{lib}/{contract[:-5]}.olean'},
                  'profiles': {f'{generated}.lean': {'sha256': gsha}}}
        root = {'id': 'r', 'function': f'example.{function}', 'prefix': 'example.', 'namespace': namespace,
                'contracts': [contract], 'assumptions': [],
                'goals': [{'theorem': theorem_name, 'strength': strength, 'domain': domain}]}
        compiled, goals = project.bind_receipt(root, base, (gsha, gsha), bundle, {contract: 'contract-sha'})
    claims = project.absence_claims(goals, {})
    return {'binding': goals[0].get('binding'), 'no-panic': claims['no-panic']['status']}


vulnerable = False
for name in ('AuditClaims.unsat_pre', 'AuditClaims.total_false_pre'):
    r = absence(name, 'safety', 'scoped: x.toNat > 300')
    bad = r['binding'] == 'direct' and r['no-panic'] == 'proved'
    vulnerable |= bad
    print(f'{name}: {"vulnerable" if bad else "fixed"} -- {r}')
sys.exit(1 if require_fixed and vulnerable else 0)
