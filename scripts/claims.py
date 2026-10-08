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
# Return only for schedules satisfying a premise stated in the conclusion. It implies none of
# CLAIMS: it is silent on other schedules and vacuous when the premise is unsatisfiable.
GUARANTEED_RETURN_UNDER_PREMISE = 'guaranteed-return-under-premise'
TOTAL = frozenset(CLAIMS)

# Exact kernel names. A redefinition elsewhere has a different full name.
HEAD_CLAIMS = {
    # A safety error makes the partial triples false; divergence satisfies them.
    'Zig.Triple': {NO_PANIC, CORRECT_IF_RETURNED},
    'Zig.TTriple': {NO_PANIC, CORRECT_IF_RETURNED},
    # An explicit `run = pure` witness: neither divergence nor a panic satisfies these.
    'Zig.TotalTriple': TOTAL,
    # A `LoopRuns` witness with at most the stated number of loop-body runs.
    'Zig.TotalTripleWithin': TOTAL,
    # Result existence only; its postcondition is trivial.
    'Zig.Returns': {NO_PANIC, GUARANTEED_RETURN},
    # Every scheduling oracle (bound inside the definition) gives `some (.ok _)` with the
    # postcondition for every large enough budget, or every budget from the stated bound.
    'Zig.Conc.Total.EventuallyReturns': TOTAL,
    'Zig.Conc.Total.ReturnsWithin': TOTAL,
    'Zig.Conc.Total.EventuallyReturnsUnder': {GUARANTEED_RETURN_UNDER_PREMISE},
}
# Heads whose guaranteed return carries an explicit bound, and the bound's unit.
HEAD_BOUNDS = {
    'Zig.TotalTripleWithin': 'loop_body_runs',
    'Zig.Conc.Total.ReturnsWithin': 'scheduler_turns',
}
# `lhs = pure v` in these monads and `lhs = some (.ok v)` state an exact successful result.
EXACT_SUCCESS = TOTAL
# `pure` in each of these is a success of the `Zig.Result` (`ExceptT Error Option`) layer.
# `pure` in `Option` is `some` and needs an `Except.ok` value; other monads are not classified.
SUCCESS_MONADS = {'Zig.Result', 'Zig.MemM', 'Zig.MM', 'Zig.M'}

ORDERED = {'safety': 1, 'partial_correctness': 2, 'total_correctness': 3}


def _head(shape) -> str | None:
    if not isinstance(shape, dict):
        return None
    head = shape.get('head')
    return head if isinstance(head, str) else None


def _args(shape) -> list:
    args = shape.get('args', []) if isinstance(shape, dict) else []
    return args if isinstance(args, list) else []


def _exact_success(value) -> bool:
    """Whether an equation's right-hand side is a successful result."""
    head, args = _head(value), _args(value)
    if head == 'Pure.pure' and len(args) == 2:
        monad, inner = _head(args[0]), args[1]
        if monad in SUCCESS_MONADS:
            return True
        head, args = ('Option.some', [inner]) if monad == 'Option' else (None, [])
    return head == 'Option.some' and len(args) == 1 and _head(args[0]) == 'Except.ok'


def claims_of(conclusion) -> frozenset[str]:
    """Claims supported by a conclusion shape; unknown shapes support none."""
    head = _head(conclusion)
    if head in HEAD_CLAIMS:
        return frozenset(HEAD_CLAIMS[head])
    args = _args(conclusion)
    if head == 'Eq' and len(args) == 1 and _exact_success(args[0]):
        return frozenset(EXACT_SUCCESS)
    return frozenset()


def claim_class(claims) -> str:
    for claim in reversed(CLAIMS):
        if claim in claims:
            return claim
    return GUARANTEED_RETURN_UNDER_PREMISE if GUARANTEED_RETURN_UNDER_PREMISE in claims else 'unclassified'


def bound_of(conclusion) -> dict | None:
    """The unit of an explicit return bound stated by the conclusion head, or None."""
    unit = HEAD_BOUNDS.get(_head(conclusion))
    return {'unit': unit} if unit else None


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
                         'claims': [c for c in (*CLAIMS, GUARANTEED_RETURN_UNDER_PREMISE) if c in claims],
                         'claim_class': claim_class(claims),
                         'derived_strength': derived_strength(claims),
                         'bound': bound_of(theorem['conclusion']),
                         'allowed': theorem.get('allowed') is True})
    names = [t['name'] for t in theorems]
    if len(set(names)) != len(names):
        raise ValueError('duplicate theorem in assurance report')
    return {'schema_version': 1, 'theorems': sorted(theorems, key=lambda t: t['name'])}


def check_goal(goal: dict, theorems: dict, outcome_counts: dict | None = None) -> dict:
    result = {'theorem': goal['theorem'], 'declared_strength': goal['strength'],
              'derived_strength': None, 'claim_class': None, 'bound': None, 'domain': goal['domain']}
    theorem = theorems.get(goal['theorem'])
    if theorem is None:
        return {**result, 'status': 'rejected',
                'reason': 'theorem absent from the audited report (names are exact, not namespace-resolved)'}
    result.update(derived_strength=theorem['derived_strength'], claim_class=theorem['claim_class'],
                  bound=theorem['bound'])
    if not theorem['allowed']:
        return {**result, 'status': 'rejected', 'reason': 'theorem has assurance policy violations'}
    declared = goal['strength']
    if declared not in ORDERED:
        return {**result, 'status': 'rejected', 'reason': f'{declared} is not derivable from a theorem type'}
    derived = theorem['derived_strength']
    if derived is None and theorem['claim_class'] == GUARANTEED_RETURN_UNDER_PREMISE:
        return {**result, 'status': 'rejected',
                'reason': f'declared {declared} needs an unconditional claim; the conclusion only guarantees '
                          'a return under a schedule premise it states'}
    if derived is None or ORDERED[derived] < ORDERED[declared]:
        return {**result, 'status': 'rejected',
                'reason': f'declared {declared} exceeds type-derived {derived or "no claim"}'}
    # Outcome evidence can only refuse an absence claim the declared strength asserts.
    for claim in OUTCOMES.STRENGTH_ABSENCE[declared] if outcome_counts is not None else ():
        verdict = OUTCOMES.absence(claim, outcome_counts)
        if verdict['status'] == 'refused':
            return {**result, 'status': 'rejected', 'reason': verdict['reason'], 'blocking': verdict['blocking']}
    return {**result, 'status': 'accepted', 'reason': None}


def _sibling(name, filename=None):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).resolve().parent / (filename or f'{name}.py'))
    module = importlib.util.module_from_spec(spec)
    sys.dont_write_bytecode = True
    spec.loader.exec_module(module)
    return module


OUTCOMES = _sibling('outcomes')
REPO = Path(__file__).resolve().parents[1]


def current_evidence(project, path: Path, current: dict) -> None:
    """Refuse a differential summary that is not bound to the current tree.

    Its `runner_runtime_sources` must equal the fingerprints `scripts/diff-report.py` computes
    for this checkout now (runner, harness, ZigLean, Proofs, examples, toolchain pins), and its
    `cases_sha256` must equal the case evidence beside it. `current` is
    `diff-report.py source_hashes` of this checkout. Stale or unbound evidence raises."""
    summary = project.diff_summary(path)
    if summary is None:
        raise ValueError(f'differential summary {path} is incomplete or unsupported')
    recorded = summary.get('runner_runtime_sources')
    if not isinstance(recorded, dict) or not recorded:
        raise ValueError(f'differential summary {path} records no source/runner fingerprints; '
                         'regenerate it with scripts/diff-report.py')
    stale = sorted(name for name in recorded.keys() | current.keys() if recorded.get(name) != current.get(name))
    if stale:
        shown = ', '.join(stale[:5]) + (f' and {len(stale) - 5} more' if len(stale) > 5 else '')
        raise ValueError(f'stale differential evidence {path}: source/runner fingerprints differ from '
                         f'the current tree for {shown}')
    cases = Path(str(path) + '.jsonl')
    digest = summary.get('cases_sha256')
    if not isinstance(digest, str) or project.hash_bounded(cases, 128 * 1024 * 1024)[0] != digest:
        raise ValueError(f'stale differential evidence {path}: case evidence {cases.name} does not '
                         'match the summary cases_sha256')


def root_outcomes(project, root: dict, diffs) -> dict | None:
    """Outcome counts for an `example.function` root from current differential case evidence."""
    if not diffs or '.' not in root['function']:
        return None
    rows = []
    for path in diffs:
        rows += project.diff_cases(path, root['function'])[0]
    return OUTCOMES.count(rows)


def check(manifest_path: Path, report: dict, diffs=()) -> dict:
    project = _sibling('project')
    manifest = project.load_manifest(manifest_path)[0]
    theorems = {t['name']: t for t in classify(report)['theorems']}
    current = _sibling('diff_report', 'diff-report.py').source_hashes(REPO) if diffs else {}
    for path in diffs:
        current_evidence(project, path, current)
    roots = []
    for root in manifest['roots']:
        counts = root_outcomes(project, root, diffs)
        roots.append({'id': root['id'], 'outcomes': counts,
                      'goals': [check_goal(goal, theorems, counts) for goal in root['goals']]})
    rejected = any(g['status'] != 'accepted' for root in roots for g in root['goals'])
    return {'schema_version': 1, 'status': 'fail' if rejected else 'pass', 'roots': roots,
            'scope': 'Strength is derived from conclusion head constants only. Preconditions and '
                     'domains are not checked: an unsatisfiable precondition remains vacuous. '
                     'Differential outcomes (when supplied) can only refuse absence claims: capped, '
                     'fuel-bounded, unsupported, unsupported-timer or unspecified outcomes and observed '
                     'failures reject a goal; error returns do not. Summaries must be bound to the current '
                     'tree (source/runner fingerprints and case hash) or the check fails. outcomes is null '
                     'for roots without evidence.'}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    report_cmd = sub.add_parser('report', help='classify every audited theorem')
    check_cmd = sub.add_parser('check', help='reject manifest goals stronger than their theorem types')
    check_cmd.add_argument('manifest', type=Path)
    check_cmd.add_argument('--diff', type=Path, action='append', default=[],
                           help='diff-report summary JSON bound to the current tree; its outcomes can only '
                                'refuse absence claims')
    for cmd in (report_cmd, check_cmd):
        cmd.add_argument('--assurance', type=Path, required=True, help='scripts/assumptions.py report')
        cmd.add_argument('--output', type=Path)
    args = parser.parse_args(argv)
    try:
        report = json.loads(args.assurance.read_text())
        result = classify(report) if args.command == 'report' else check(args.manifest, report, args.diff)
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
