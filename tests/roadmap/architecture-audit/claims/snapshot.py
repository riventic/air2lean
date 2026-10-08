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
REPORTS = [ROOT / '.lake/architecture-audit/claims' / f'assurance-{name}.json' for name in ('Vacuous', 'Shadow')]
GENERATED = ('AuditClaims.root', 'AuditClaims.spin', 'Asm.divmod')
SNAPSHOT = HERE / 'exposure-report.json'
FIELDS = ('name', 'module', 'axioms', 'conclusion', 'statement_dependencies', 'conclusion_dependencies',
          'opaque_dependencies', 'extern_dependencies', 'compiler_redirections', 'violations', 'allowed')


def extract():
    theorems, nodes = [], {}
    for path in REPORTS:
        report = json.loads(path.read_text())
        if report.get('status') != 'pass':
            raise SystemExit(f'{path}: assurance audit did not pass: {report.get("violations") or report.get("error")}')
        theorems += [{k: t[k] for k in FIELDS} for t in report['theorems'] if '._proof' not in t['name']]
        nodes.update({n['name']: {'module': n['module'], 'kind': n['kind']} for n in report['nodes']
                      if n['name'] in GENERATED})
    return {'schema_version': 1, 'source': 'tests/roadmap/architecture-audit/claims/build.sh',
            'theorems': sorted(theorems, key=lambda t: t['name']), 'generated_nodes': dict(sorted(nodes.items()))}


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
