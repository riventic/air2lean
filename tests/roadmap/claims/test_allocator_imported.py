#!/usr/bin/env python3
"""Both audit modes retain imported creation roots and exact selected-module declarations."""
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'scripts'))
import claims


def check(default, enabled):
    module = 'tests.roadmap.claims.AllocatorImported'
    assert 'selected_declaration_roots' not in default
    assert 'selected_declaration_evidence' not in default
    assert 'selected_declaration_roots' in enabled
    assert 'selected_declaration_evidence' in enabled
    for field in ('schema_version', 'modules', 'theorems', 'project_declarations'):
        assert default[field] == enabled[field], field
    selected = enabled['selected_declaration_roots']
    nodes = {node['name']: node for node in enabled['nodes']}
    assert len(selected) == len(set(selected))
    assert set(selected) == {name for name, node in nodes.items() if node['module'] == module}
    evidence = enabled['selected_declaration_evidence']
    assert len(evidence) == len(selected)
    assert {item['name'] for item in evidence} == set(selected)
    assert all(item['module'] == module for item in evidence)
    assert 'AllocatorImported.unusedValue' in selected
    imported = {'AllocatorApplications.spec', 'AllocatorApplications.spec.creation',
                'AllocatorApplications.spec.creation.nonvacuous'}
    assert not imported.intersection(selected)
    heads = claims.load_heads()
    for report in (default, enabled):
        assert report['status'] == report['kernel_replay']['status'] == 'pass'
        graph = {node['name']: node for node in report['nodes']}
        roots = {theorem['name'] for theorem in report['theorems']}
        assert imported <= roots <= graph.keys(), (imported - roots, roots - graph.keys())
        assert all(set(node['dependencies']) <= graph.keys() for node in graph.values())
        audited = claims.audited_theorems(report)
        result = claims.assess(audited['AllocatorImported.client'], heads, audited=audited)
        assert result['allocator_creation']['status'] == 'verified', result
        assert claims.uncreated(result) is None, result
    default_nodes = {node['name']: node for node in default['nodes']}
    assert all(nodes[name] == node for name, node in default_nodes.items())
    print('allocator admission: both modes retain imported companions and exact selected roots')


if __name__ == '__main__':
    check(*(json.loads(Path(path).read_text()) for path in sys.argv[1:]))
