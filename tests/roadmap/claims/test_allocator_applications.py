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

    for name in ('generic_interface', 'let_interface', 'invariant_alias_interface',
                 'type_only_interface', 'conclusion_only_interface', 'beta_ignored_interface',
                 'polymorphic_interface', 'field_interface'):
        generic = claims.assess(audited['AllocatorApplications.' + name], heads, audited=audited)
        assert generic['allocator_creation']['status'] == 'not_required', (name, generic['allocator_creation'])
        assert claims.uncreated(generic) is None, name

    def creation(name):
        found = claims.assess(audited['AllocatorApplications.' + name], heads, audited=audited)
        entries = found['allocator_creation']['contracts']
        assert entries, (name, found)
        return found, entries

    for name in ('exact_parameter', 'checked_let', 'exact_dependent'):
        found, entries = creation(name)
        assert claims.uncreated(found) is None, (name, entries)
        assert all(entry['admission_binding'] == 'checked_client_context' for entry in entries)
        assert all(entry['applications'] and all(use['evidence'] is not None and use['root_bound'] is True
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

    for name in ('false_scope_only', 'hypothetical_holds_only', 'root_holds_only'):
        found, entries = creation(name)
        assert claims.uncreated(found) is not None, (name, entries)
        assert found['allocator_creation']['status'] == 'unbound_admissibility', (name, entries)
        uses = [use for entry in entries for use in entry['applications']]
        assert uses and any(use['evidence'] is not None and use['root_bound'] is False
                            for use in uses), (name, entries)

    found, entries = creation('spec')
    assert claims.uncreated(found) is not None, entries
    assert found['allocator_creation']['status'] == 'unbound_admissibility', entries

    for name in ('fresh_spec', 'fresh_impossible'):
        found, entries = creation(name)
        assert claims.uncreated(found) is not None, (name, entries)
        assert found['allocator_creation']['status'] == 'unbound_application', (name, entries)
        assert all(entry['post_status'] == 'verified' for entry in entries), (name, entries)

    found, entries = creation('constant_pre_false_arg')
    assert claims.uncreated(found) is not None, entries
    assert found['allocator_creation']['status'] == 'unbound_application', entries
    assert any('arguments are not bound to the root' in entry.get('application_error', '') for entry in entries), entries

    found, entries = creation('named_good')
    assert claims.uncreated(found) is None, entries
    assert found['allocator_creation']['status'] == 'verified', entries
    assert all(entry['admission_binding'] == 'constant_precondition' for entry in entries), entries

    for name in ('named_hidden', 'named_hidden_client', 'named_hidden_generic', 'named_hidden_generic_client'):
        found, entries = creation(name)
        assert claims.uncreated(found) is not None, (name, entries)
        contract = 'AllocatorApplications.named_hidden' + ('_generic' if '_generic' in name else '')
        hidden = next(entry for entry in entries if entry['contract'] == contract)
        assert hidden['status'] == 'unbound_application', (name, entries)
        assert hidden['post_status'] == 'verified', (name, entries)
        assert 'unnamed concrete constructor' in hidden.get('application_error', ''), (name, entries)

    found, entries = creation('named_premise')
    assert claims.uncreated(found) is not None, entries
    premise = next(entry for entry in entries if entry['contract'] == 'AllocatorApplications.named_premise')
    assert premise['status'] == 'unbound_application', entries
    assert 'unbound concrete contract premise' in premise.get('application_error', ''), entries

    for name in ('wrapped_impossible', 'let_alias_impossible', 'invariant_alias_impossible',
                 'type_only_impossible', 'conclusion_only_impossible', 'higher_order_impossible',
                 'beta_ignored_impossible', 'indexed_apply_impossible', 'indexed_result_impossible',
                 'polymorphic_impossible', 'field_impossible'):
        found, entries = creation(name)
        assert claims.uncreated(found) is not None, (name, entries)
        assert found['allocator_creation']['status'] == 'unnamed', (name, entries)
        assert any('unnamed concrete constructor' in entry.get('application_error', '')
                   for entry in entries), (name, entries)

    for name in ('use_producer', 'unknown_forwarder'):
        found, entries = creation(name)
        assert claims.uncreated(found) is not None, (name, entries)
        assert found['allocator_creation']['status'] == 'unnamed', (name, entries)
        assert any('unbound concrete contract application' in entry.get('application_error', '')
                   for entry in entries), (name, entries)

    found, entries = creation('prefixed_apply_impossible')
    assert claims.uncreated(found) is not None, entries
    assert found['allocator_creation']['status'] == 'unnamed', entries
    assert any('checked argument telescope' in entry.get('application_error', '') for entry in entries), entries

    for field, value in (('admission_binding', None), ('admission_binding', ''),
                         ('applications', None), ('applications', []),
                         ('applications', [{}]), ('applications', [
                             {'application': 'x', 'admission': 'P', 'evidence': None}]),
                         ('applications', [
                             {'application': 'x', 'admission': 'P', 'evidence': 'proof', 'root_bound': False}])):
        altered = copy.deepcopy(audited)
        theorem = altered['AllocatorApplications.exact_parameter']
        theorem['statement']['allocator_creation'][0][field] = value
        found = claims.assess(theorem, heads, audited=altered)
        assert found['allocator_creation']['status'] == 'unbound_admissibility', (field, value, found)
        assert claims.uncreated(found) is not None
    print('allocator admission: exact arguments and complete checked contexts verified')


if __name__ == '__main__':
    check(json.loads(Path(sys.argv[1]).read_text()))
