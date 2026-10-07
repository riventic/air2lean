#!/usr/bin/env python3
"""Derive claim strength from checked theorem types and check declared manifest goals.

The input is an assurance report from scripts/assumptions.py. Its extractor records each
theorem's conclusion shape from the kernel type: binders and hypotheses are stripped, no
definition is unfolded, and only an equation's right-hand side is expanded. Theorem names,
comments and manifest labels never contribute to the derived claim.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import sys

NO_PANIC = 'no-panic'
CORRECT_IF_RETURNED = 'correct-if-returned'
GUARANTEED_RETURN = 'guaranteed-return'
CLAIMS = (NO_PANIC, CORRECT_IF_RETURNED, GUARANTEED_RETURN)

# Exact kernel names. A redefinition elsewhere has a different full name.
HEAD_CLAIMS = {
    # A safety error makes the partial triples false; divergence satisfies them.
    'Zig.Triple': {NO_PANIC, CORRECT_IF_RETURNED},
    'Zig.TTriple': {NO_PANIC, CORRECT_IF_RETURNED},
    # An explicit `run = pure` witness: neither divergence nor a panic satisfies these.
    'Zig.TotalTriple': {NO_PANIC, CORRECT_IF_RETURNED, GUARANTEED_RETURN},
    # Result existence only; its postcondition is trivial.
    'Zig.Returns': {NO_PANIC, GUARANTEED_RETURN},
}
# `lhs = pure v` and `lhs = some (.ok v)` state an exact successful result.
EXACT_SUCCESS = {NO_PANIC, CORRECT_IF_RETURNED, GUARANTEED_RETURN}

ORDERED = {'safety': 1, 'partial_correctness': 2, 'total_correctness': 3}
STRENGTHS = (*ORDERED, 'resource_bound', 'correspondence')


def _head(shape) -> str | None:
    if not isinstance(shape, dict):
        return None
    head = shape.get('head')
    return head if isinstance(head, str) else None


def _args(shape) -> list:
    args = shape.get('args', []) if isinstance(shape, dict) else []
    return args if isinstance(args, list) else []


def claims_of(conclusion) -> frozenset[str]:
    """Claims supported by a conclusion shape; unknown shapes support none."""
    head = _head(conclusion)
    if head in HEAD_CLAIMS:
        return frozenset(HEAD_CLAIMS[head])
    if head == 'Eq':
        args = _args(conclusion)
        rhs = args[0] if len(args) == 1 else None
        if _head(rhs) == 'Pure.pure':
            return frozenset(EXACT_SUCCESS)
        inner = _args(rhs)
        if _head(rhs) == 'Option.some' and len(inner) == 1 and _head(inner[0]) == 'Except.ok':
            return frozenset(EXACT_SUCCESS)
    return frozenset()


def claim_class(claims) -> str:
    for claim in reversed(CLAIMS):
        if claim in claims:
            return claim
    return 'unclassified'


def derived_strength(claims) -> str | None:
    if GUARANTEED_RETURN in claims and CORRECT_IF_RETURNED in claims:
        return 'total_correctness'
    if CORRECT_IF_RETURNED in claims:
        return 'partial_correctness'
    if NO_PANIC in claims:
        return 'safety'
    return None


def classify(report: dict) -> dict:
    if not isinstance(report, dict) or report.get('schema_version') != 1:
        raise ValueError('unsupported assurance report schema')
    if report.get('status') not in ('pass', 'fail') or not isinstance(report.get('theorems'), list):
        raise ValueError('assurance report is not a completed audit')
    theorems = []
    for theorem in report['theorems']:
        if not isinstance(theorem, dict) or not isinstance(theorem.get('name'), str):
            raise ValueError('invalid theorem entry in assurance report')
        if 'conclusion' not in theorem:
            raise ValueError(f'assurance report lacks a conclusion shape for {theorem["name"]}; regenerate it')
        claims = claims_of(theorem['conclusion'])
        theorems.append({'name': theorem['name'], 'module': theorem.get('module', ''),
                         'conclusion_head': _head(theorem['conclusion']),
                         'claims': [c for c in CLAIMS if c in claims],
                         'claim_class': claim_class(claims),
                         'derived_strength': derived_strength(claims),
                         'allowed': theorem.get('allowed') is True})
    names = [t['name'] for t in theorems]
    if len(set(names)) != len(names):
        raise ValueError('duplicate theorem in assurance report')
    return {'schema_version': 1, 'theorems': sorted(theorems, key=lambda t: t['name'])}


def check_goal(goal: dict, theorems: dict) -> dict:
    result = {'theorem': goal['theorem'], 'declared_strength': goal['strength'],
              'derived_strength': None, 'claim_class': None, 'domain': goal['domain']}
    theorem = theorems.get(goal['theorem'])
    if theorem is None:
        return {**result, 'status': 'rejected',
                'reason': 'theorem absent from the audited report (names are exact, not namespace-resolved)'}
    result.update(derived_strength=theorem['derived_strength'], claim_class=theorem['claim_class'])
    if not theorem['allowed']:
        return {**result, 'status': 'rejected', 'reason': 'theorem has assurance policy violations'}
    declared = goal['strength']
    if declared not in ORDERED:
        return {**result, 'status': 'rejected', 'reason': f'{declared} is not derivable from a theorem type'}
    derived = theorem['derived_strength']
    if derived is None or ORDERED[derived] < ORDERED[declared]:
        return {**result, 'status': 'rejected',
                'reason': f'declared {declared} exceeds type-derived {derived or "no claim"}'}
    return {**result, 'status': 'accepted', 'reason': None}


def _project():
    spec = importlib.util.spec_from_file_location('project', Path(__file__).resolve().parent / 'project.py')
    module = importlib.util.module_from_spec(spec)
    sys.dont_write_bytecode = True
    spec.loader.exec_module(module)
    return module


def check(manifest_path: Path, report: dict) -> dict:
    manifest = _project().load_manifest(manifest_path)[0]
    theorems = {t['name']: t for t in classify(report)['theorems']}
    roots = []
    for root in manifest['roots']:
        roots.append({'id': root['id'], 'goals': [check_goal(goal, theorems) for goal in root['goals']]})
    rejected = any(g['status'] != 'accepted' for root in roots for g in root['goals'])
    return {'schema_version': 1, 'status': 'fail' if rejected else 'pass', 'roots': roots,
            'scope': 'Strength is derived from conclusion head constants only. Preconditions and '
                     'domains are not checked: an unsatisfiable precondition remains vacuous.'}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    report_cmd = sub.add_parser('report', help='classify every audited theorem')
    check_cmd = sub.add_parser('check', help='reject manifest goals stronger than their theorem types')
    check_cmd.add_argument('manifest', type=Path)
    for cmd in (report_cmd, check_cmd):
        cmd.add_argument('--assurance', type=Path, required=True, help='scripts/assumptions.py report')
        cmd.add_argument('--output', type=Path)
    args = parser.parse_args(argv)
    try:
        report = json.loads(args.assurance.read_text())
        result = classify(report) if args.command == 'report' else check(args.manifest, report)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f'claims error: {error}', file=sys.stderr)
        return 2
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    else:
        sys.stdout.write(text)
    if result.get('status') == 'fail':
        for root in result['roots']:
            for goal in root['goals']:
                if goal['status'] != 'accepted':
                    print(f'  {root["id"]}: {goal["theorem"]}: {goal["reason"]}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
