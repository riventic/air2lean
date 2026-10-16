#!/usr/bin/env python3
"""Check actual kernel-extracted allocator applications, including their local scope."""
import copy
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
import claims


def check(report):
    assert report['status'] == 'pass', report.get('violations')
    audited = claims.audited_theorems(report)
    heads = claims.load_heads()

    def creation(name):
        found = claims.assess(audited['AllocatorApplications.' + name], heads, audited=audited)
        entries = found['allocator_creation']['contracts']
        assert entries, (name, found)
        return found, entries

    for name in ('exact_parameter', 'checked_let', 'exact_dependent'):
        found, entries = creation(name)
        assert claims.uncreated(found) is None, (name, entries)
        assert all(entry['admission_binding'] == 'checked_client_context' for entry in entries)
        assert all(entry['applications'] and all(use['evidence'] is not None
                   for use in entry['applications']) for entry in entries), (name, entries)

    for name in ('wrong_parameter', 'pure_guard_only', 'wrong_let',
                 'let_scope_does_not_escape', 'false_scope_does_not_escape'):
        found, entries = creation(name)
        assert claims.uncreated(found) is not None, (name, entries)
        assert found['allocator_creation']['status'] == 'unbound_admissibility', (name, entries)
        uses = [use for entry in entries for use in entry['applications']]
        assert uses and any(use['evidence'] is None for use in uses), (name, entries)
        if name.endswith('does_not_escape'):
            assert any(use['evidence'] is not None for use in uses), (name, entries)
            assert len({use['application'] for use in uses}) > 1, (name, entries)

    found, entries = creation('spec')
    assert claims.uncreated(found) is not None, entries
    assert found['allocator_creation']['status'] == 'unbound_admissibility', entries

    found, entries = creation('wrapped_impossible')
    assert claims.uncreated(found) is not None, entries
    assert found['allocator_creation']['status'] == 'unnamed', entries
    assert any('unnamed concrete constructor' in entry.get('application_error', '') for entry in entries), entries

    for field, value in (('admission_binding', None), ('admission_binding', ''),
                         ('applications', None), ('applications', []),
                         ('applications', [{}]), ('applications', [
                             {'application': 'x', 'admission': 'P', 'evidence': None}])):
        altered = copy.deepcopy(audited)
        theorem = altered['AllocatorApplications.exact_parameter']
        theorem['statement']['allocator_creation'][0][field] = value
        found = claims.assess(theorem, heads, audited=altered)
        assert found['allocator_creation']['status'] == 'unbound_admissibility', (field, value, found)
        assert claims.uncreated(found) is not None
    print('allocator admission: exact arguments and complete checked contexts verified')


if __name__ == '__main__':
    check(json.loads(Path(sys.argv[1]).read_text()))
