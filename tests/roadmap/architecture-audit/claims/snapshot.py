#!/usr/bin/env python3
"""Trim the build.sh assurance reports to the theorem entries test_exposure.py reads.

`snapshot.py write` regenerates exposure-report.json; `snapshot.py check` (run by check.sh)
fails unless the freshly extracted entries equal the committed ones.
"""
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUT = ROOT / '.lake/architecture-audit/claims'
GENERATED = ('AuditClaims.root', 'AuditClaims.spin', 'Asm.divmod')
SNAPSHOT = HERE / 'exposure-report.json'
FIELDS = ('name', 'module', 'axioms', 'conclusion', 'statement_dependencies', 'conclusion_dependencies',
          'opaque_dependencies', 'extern_dependencies', 'compiler_redirections', 'violations', 'allowed', 'statement')
# The Shadow contracts redefine Zig.TotalTriple and Zig.TotalTripleWithin; the audit
# environment imports the registered ones.
CLASH = "environment already contains 'Zig.TotalTriple"


def extract():
    theorems, nodes = [], {}
    # A report may fail only for its expected reason: kernel replay rejects AuditClaims.Unchecked
    # (S1 fixed), and the policy refuses AuditClaims.Escapes' partial def and compiler redirection (H4).
    expected_failures = {'Vacuous': set(), 'Unchecked': {'kernel-replay-rejected'},
                         'Escapes': {'unexpected-opaque', 'unexpected-compiler-redirection'}}
    for name, expected in expected_failures.items():
        path = OUT / f'assurance-{name}.json'
        report = json.loads(path.read_text())
        violations = report.get('violations') or []
        explained = bool(violations) and all(v['trust_class'] in expected for v in violations)
        if report.get('status') != 'pass' and not (report.get('status') == 'fail' and explained):
            raise SystemExit(f'{path}: assurance audit did not pass: {report.get("violations") or report.get("error")}')
        theorems += [{k: t[k] for k in FIELDS} for t in report['theorems'] if '._proof' not in t['name']]
        nodes.update({n['name']: {'module': n['module'], 'kind': n['kind']} for n in report['nodes']
                      if n['name'] in GENERATED})
    def shadow(name):
        report = json.loads((OUT / f'assurance-{name}.json').read_text())
        return {'status': report.get('status'), 'name_clash': CLASH in (OUT / f'assurance-{name}.stderr').read_text()}
    shadow_audit = shadow('Shadow')
    shadow_within_audit = shadow('ShadowWithin')
    return {'schema_version': 2, 'source': 'tests/roadmap/architecture-audit/claims/build.sh',
            'theorems': sorted(theorems, key=lambda t: t['name']), 'generated_nodes': dict(sorted(nodes.items())),
            'shadow_audit': shadow_audit, 'shadow_within_audit': shadow_within_audit}


def main(argv):
    fresh = extract()
    if argv[1:] == ['write']:
        SNAPSHOT.write_text(json.dumps(fresh, indent=1) + '\n')
        return 0
    if json.loads(SNAPSHOT.read_text()) != fresh:
        print('exposure-report.json differs from the fresh extraction; run snapshot.py write', file=sys.stderr)
        return 1
    print(f'exposure snapshot matches {len(fresh["theorems"])} extracted theorems')
    return 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv))
