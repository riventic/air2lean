#!/usr/bin/env python3
"""Derive claim strength from checked theorem types and check declared manifest goals.

The input is an assurance report from scripts/assumptions.py. Its extractor (tools/Assurance.lean)
records each theorem's kernel statement: the binder telescope, the conclusion head as a
declaration (module and fingerprint), the computation each head argument runs, and companion
witness theorems whose statements it recomputes from the theorem's type. No definition is
unfolded for classification. Theorem names, comments and manifest labels never contribute to the
derived claim.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
HEADS_PATH = ROOT / 'assurance/claim-heads.json'

NO_PANIC = 'no-panic'
CORRECT_IF_RETURNED = 'correct-if-returned'
GUARANTEED_RETURN = 'guaranteed-return'
CLAIMS = (NO_PANIC, CORRECT_IF_RETURNED, GUARANTEED_RETURN)
# Return only for schedules satisfying a premise stated in the conclusion. It implies none of
# CLAIMS: it is silent on other schedules and vacuous when the premise is unsatisfiable.
GUARANTEED_RETURN_UNDER_PREMISE = 'guaranteed-return-under-premise'
REGISTRY_CLAIMS = (*CLAIMS, GUARANTEED_RETURN_UNDER_PREMISE)
# Units of an explicit return bound that a registered head can state (`bound` in the registry).
BOUND_UNITS = ('loop_body_runs', 'scheduler_turns')

# Lean's `Eq` (core; a redefinition cannot be imported next to it): the computation is the
# left-hand side.
EQ_HEAD = {'module': 'Init.Prelude', 'program': 1, 'state': []}
# `lhs = pure v` in these monads and `lhs = some (.ok v)` state an exact successful result.
EXACT_SUCCESS = frozenset(CLAIMS)
# `pure` in each of these is a success of the `Zig.Result` (`ExceptT Error Option`) layer.
# `pure` in `Option` is `some` and needs an `Except.ok` value; other monads are not classified.
SUCCESS_MONADS = {'Zig.Result', 'Zig.MemM', 'Zig.MM', 'Zig.M'}

ORDERED = {'safety': 1, 'partial_correctness': 2, 'total_correctness': 3}
FUNCTIONAL = ('partial_correctness', 'total_correctness')
# Witness statuses that establish an inhabited premise telescope (ZigLean/Witness.lean).
NONVACUOUS = ('verified', 'trivial')
FINGERPRINT = re.compile(r'[0-9a-f]{32}')
# An allowlisted inline-asm opaque in a theorem's dependency closure (docs/premises.md ASM-01).
ASM_OPAQUE = re.compile(r'(?:^|\.)airAsm_[0-9]+\Z')
# Claims that the asm entries' fault conditions carry (ASM-04): the model throws `trap` exactly
# when an entry's `AsmFault` holds, so absence of a failure is only as good as that condition.
ABSENCE_CLAIMS = frozenset({NO_PANIC, GUARANTEED_RETURN})


def premises_of(theorem: dict, claims) -> list[str] | None:
    """Premises a theorem's claims rest on that its type does not show (S7): ASM-01 for an asm
    opaque in its closure, and ASM-04 too if it claims no-panic or guaranteed-return over one.
    None if the report lacks the closure (`opaque_dependencies`)."""
    opaques = theorem.get('opaque_dependencies')
    if not isinstance(opaques, list):
        return None
    if not any(isinstance(n, str) and ASM_OPAQUE.search(n) for n in opaques):
        return []
    return ['ASM-01', 'ASM-04'] if ABSENCE_CLAIMS & set(claims) else ['ASM-01']


def load_heads(path: Path = HEADS_PATH) -> dict:
    """The registered claim heads (assurance/claim-heads.json)."""
    data = json.loads(Path(path).read_text())
    if not isinstance(data, dict) or data.get('schema_version') != 1 or not isinstance(data.get('heads'), dict):
        raise ValueError('unsupported claim-head registry schema')
    for name, entry in data['heads'].items():
        valid = (isinstance(entry, dict) and name != 'Eq'
                 and {'module', 'fingerprint', 'claims', 'program', 'state'} <= set(entry)
                 and isinstance(entry['module'], str) and bool(entry['module'])
                 and isinstance(entry['fingerprint'], str) and FINGERPRINT.fullmatch(entry['fingerprint'])
                 and isinstance(entry['claims'], list) and bool(entry['claims'])
                 and set(entry['claims']) <= set(REGISTRY_CLAIMS)
                 and entry.get('bound', None) in (None, *BOUND_UNITS)
                 and type(entry['program']) is int and entry['program'] >= 0
                 and isinstance(entry['state'], list) and all(type(i) is int and i >= 0 for i in entry['state']))
        if not valid:
            raise ValueError(f'invalid claim-head registry entry: {name}')
    return data['heads']


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


def statement_of(theorem) -> dict | None:
    statement = theorem.get('statement') if isinstance(theorem, dict) else None
    return statement if isinstance(statement, dict) else None


def head_entry(theorem, heads, nodes=None):
    """(head name, registry entry or None, identity problem or None).

    A head counts only as the registered declaration: the same defining module and fingerprint
    of its kernel type and value. An unregistered head has neither an entry nor a problem."""
    statement = statement_of(theorem)
    if statement is None:
        return None, None, 'audit lacks the statement structure; regenerate it with the current extractor'
    head = statement.get('head')
    if not isinstance(head, dict) or not isinstance(head.get('name'), str):
        return None, None, None
    name = head['name']
    entry = EQ_HEAD if name == 'Eq' else heads.get(name)
    if entry is None:
        return name, None, None
    expected = (entry['module'], entry.get('fingerprint'))
    found = (head.get('module'), head.get('fingerprint') if name != 'Eq' else None)
    node = (nodes or {}).get(name)
    if found != expected or (node is not None and node.get('module') != entry['module']):
        return name, None, (f'conclusion head {name} is the declaration in {found[0] or "?"} '
                            f'(fingerprint {found[1]}), not the registered one in {expected[0]}')
    return name, entry, None


def claims_of(theorem, heads, nodes=None) -> frozenset[str]:
    """Claims supported by a theorem's conclusion; unknown or unregistered heads support none."""
    name, entry, _ = head_entry(theorem, heads, nodes)
    if entry is None:
        return frozenset()
    if name == 'Eq':
        args = _args(theorem.get('conclusion'))
        return EXACT_SUCCESS if len(args) == 1 and _exact_success(args[0]) else frozenset()
    return frozenset(entry['claims'])


def claim_class(claims) -> str:
    for claim in reversed(CLAIMS):
        if claim in claims:
            return claim
    return GUARANTEED_RETURN_UNDER_PREMISE if GUARANTEED_RETURN_UNDER_PREMISE in claims else 'unclassified'


def bound_of(entry) -> dict | None:
    """The unit of an explicit return bound stated by a registered conclusion head, or None."""
    unit = entry.get('bound') if isinstance(entry, dict) else None
    return {'unit': unit} if unit else None


def derived_strength(claims) -> str | None:
    if GUARANTEED_RETURN in claims and CORRECT_IF_RETURNED in claims:
        return 'total_correctness'
    if CORRECT_IF_RETURNED in claims:
        return 'partial_correctness'
    if NO_PANIC in claims:
        return 'safety'
    return None


def _bvar(atom):
    return atom.get('bvar') if isinstance(atom, dict) and type(atom.get('bvar')) is int else None


def _list(value):
    return value if isinstance(value, list) else []


def _subject(statement, entry):
    """The descriptor of the computation the claim is about, or None."""
    args = _list(statement.get('args'))
    index = entry['program']
    return args[index] if index < len(args) and isinstance(args[index], dict) else None


def _domain(statement, entry, subject):
    """Which root parameters (and initial state) are universally quantified, from the kernel
    type: a fixed or derived argument, a repeated variable, a fixed initial state or any other
    binder over a quantified argument (a hypothesis, also one wrapped in a non-Prop type such as
    `PLift`) makes the domain scoped. `variables` are the telescope indices of the arguments."""
    binders = _list(statement.get('binders'))
    name = lambda i: binders[i].get('name') if 0 <= i < len(binders) and isinstance(binders[i], dict) else f'#{i}'
    kinds, args = _list(subject.get('params')), _list(subject.get('args'))
    rows, used, fixed = [], [], []
    for position, atom in enumerate(args[:len(kinds)]):
        kind, var = kinds[position], _bvar(atom)
        if kind != 'default' and var is None:
            continue  # implicit/instance arguments are types and instances, not inputs
        rows.append({'position': position, 'argument': name(var) if var is not None else 'fixed'})
        (used.append(var) if var is not None else fixed.append(f'parameter {position}'))
    heads_args = _list(statement.get('args'))
    state = _list(subject.get('extra')) + args[len(kinds):] + [
        heads_args[i].get('atom') for i in entry['state'] if i < len(heads_args) and isinstance(heads_args[i], dict)]
    for position, atom in enumerate(state):
        var = _bvar(atom)
        rows.append({'state': position, 'argument': name(var) if var is not None else 'fixed'})
        (used.append(var) if var is not None else fixed.append(f'initial state {position}'))
    repeated = sorted({name(v) for v in used if used.count(v) > 1})
    constrained = [b.get('name') for i, b in enumerate(binders) if isinstance(b, dict) and i not in used
                   and set(_list(b.get('uses'))) & set(used)]
    scoped = bool(fixed or repeated or constrained)
    return {'scope': 'scoped' if scoped else 'universal', 'arguments': rows, 'fixed': fixed,
            'repeated': repeated, 'constrained_by': constrained, 'variables': sorted(set(used))}


def _witness(statement, kind, audited):
    """A companion's status; a verified companion must itself be an allowed audited theorem."""
    witness = (statement.get('witnesses') or {}).get(kind) if isinstance(statement.get('witnesses'), dict) else None
    if not isinstance(witness, dict):
        return 'absent'
    status = witness.get('status')
    if status == 'verified':
        companion = (audited or {}).get(witness.get('theorem'))
        if not isinstance(companion, dict) or companion.get('allowed') is not True:
            return 'unaudited'
    return status if isinstance(status, str) else 'absent'


def assess(theorem, heads, definition=None, *, generated=(), allowed=(), audited=None, nodes=None) -> dict:
    """Everything a goal binding needs, derived from the theorem's kernel statement.

    `definition` is the root's generated definition, `generated` every definition of its
    generated module, `allowed` the root's declared assumptions, `audited` the audit's theorems
    by name. `strength` is the type-derived strength after the caps listed in `caps`."""
    name, entry, problem = head_entry(theorem, heads, nodes)
    found = claims_of(theorem, heads, nodes)
    result = {'head': name, 'head_problem': problem, 'claims': [c for c in REGISTRY_CLAIMS if c in found],
              'claim_class': claim_class(found), 'type_strength': derived_strength(found),
              'bound': bound_of(entry),
              'subject': None, 'binding': None, 'domain': None, 'rejected_hypotheses': [],
              'witnesses': None, 'caps': [], 'strength': None, 'scope': 'scoped'}
    statement = statement_of(theorem)
    if statement is None:
        result['binding'] = 'no_statement'
        result['caps'].append(problem)
        return result
    subject = _subject(statement, entry) if entry is not None else None
    result['subject'] = subject.get('fn') if subject else None
    if definition is None:
        result['binding'] = None
    elif subject is not None and subject.get('fn') == definition:
        result['binding'] = 'direct'
    else:
        mentioned = definition in _list(theorem.get('conclusion_dependencies'))
        result['binding'] = 'mentions' if mentioned else 'unrelated'
    domain = _domain(statement, entry, subject) if subject is not None else None
    variables = set(domain.pop('variables')) if domain else set()
    # Every binder other than the root's own arguments is a premise, whether a Prop or a
    # proposition wrapped in a type (`PLift`, a structure of proofs).
    blocked = set(generated) | set(heads) | ({definition} if definition else set())
    for index, binder in enumerate(_list(statement.get('binders'))):
        if isinstance(binder, dict) and index not in variables:
            bad = sorted(set(_list(binder.get('defs'))) & blocked - set(allowed))
            if bad:
                result['rejected_hypotheses'].append({'hypothesis': binder.get('name'), 'mentions': bad})
    witnesses = {kind: _witness(statement, kind, audited) for kind in ('nonvacuity', 'liveness')}
    result['witnesses'] = witnesses
    strength, caps = result['type_strength'], result['caps']
    if problem:
        caps.append(problem)
    if result['rejected_hypotheses']:
        caps.append('a hypothesis mentions a generated definition or claim head: '
                    + '; '.join(f'{h["hypothesis"]} mentions {", ".join(h["mentions"])}' for h in result['rejected_hypotheses']))
        strength = None
    nonvacuous = witnesses['nonvacuity'] in NONVACUOUS
    if strength in FUNCTIONAL and not nonvacuous:
        caps.append(f'non-vacuity witness {witnesses["nonvacuity"]}: the premises may be unsatisfiable '
                    '(nonvacuity_witness, ZigLean/Witness.lean)')
        strength = 'safety'
    if strength == 'partial_correctness' and witnesses['liveness'] != 'verified':
        caps.append(f'liveness witness {witnesses["liveness"]}: no admissible run is shown to return '
                    '(liveness_witness, ZigLean/Witness.lean)')
        strength = 'safety'
    result['strength'] = strength
    if domain is not None:
        # Unwitnessed premises may be unsatisfiable: the domain may be empty.
        domain['nonvacuity'] = witnesses['nonvacuity']
        if not nonvacuous:
            domain['scope'] = 'scoped'
        result['domain'], result['scope'] = domain, domain['scope']
    return result


def audited_theorems(report: dict) -> dict:
    """The report's theorem entries by name, after validating the report's shape."""
    if not isinstance(report, dict) or report.get('schema_version') != 1:
        raise ValueError('unsupported assurance report schema')
    if report.get('status') not in ('pass', 'fail') or not isinstance(report.get('theorems'), list):
        raise ValueError('assurance report is not a completed audit')
    audited = {}
    for theorem in report['theorems']:
        if not isinstance(theorem, dict) or not isinstance(theorem.get('name'), str):
            raise ValueError('invalid theorem entry in assurance report')
        if 'conclusion' not in theorem or 'statement' not in theorem:
            raise ValueError(f'assurance report lacks a conclusion structure for {theorem["name"]}; regenerate it')
        if theorem['name'] in audited:
            raise ValueError('duplicate theorem in assurance report')
        audited[theorem['name']] = theorem
    return audited


def caller_obligations(report: dict) -> dict:
    """W1: a theorem over a function with a caller-supplied Allocator/Io parameter is about
    callers that pass the model one (docs/premises.md ALC-09, IOM-01); the claim names that
    premise. Theorem name -> premise IDs."""
    return MARKERS.caller_obligations(report, ROOT) if isinstance(report.get('nodes'), list) else {}


def classify(report: dict, heads: dict | None = None) -> dict:
    audited = audited_theorems(report)
    heads = load_heads() if heads is None else heads
    nodes = nodes_of(report)
    obligations = caller_obligations(report)
    theorems = []
    for theorem in audited.values():
        found = assess(theorem, heads, audited=audited, nodes=nodes)
        theorems.append({'name': theorem['name'], 'module': theorem.get('module', ''),
                         'conclusion_head': found['head'], 'head_problem': found['head_problem'],
                         'subject': found['subject'], 'claims': found['claims'],
                         'claim_class': found['claim_class'], 'derived_strength': found['strength'],
                         'type_strength': found['type_strength'], 'bound': found['bound'],
                         'witnesses': found['witnesses'], 'caps': found['caps'],
                         'caller_obligations': obligations.get(theorem['name'], []),
                         'premises': premises_of(theorem, found['claims']),
                         'allowed': theorem.get('allowed') is True})
    return {'schema_version': 1, 'theorems': sorted(theorems, key=lambda t: t['name'])}


def nodes_of(report) -> dict:
    return {n['name']: n for n in report.get('nodes') or [] if isinstance(n, dict) and isinstance(n.get('name'), str)}


def generated_definitions(nodes, modules) -> set:
    """Definitions of the root's generated module(s), from the audited declaration graph."""
    return {name for name, node in nodes.items() if node.get('module') in modules and node.get('kind') == 'definition'}


def declares_scoped(domain) -> bool:
    """A manifest domain that admits a scoped claim (docs/claim-strength.md)."""
    return isinstance(domain, str) and domain.strip().lower().startswith('scoped')


def check_goal(goal: dict, theorems: dict, outcome_counts: dict | None = None, *, definition: str,
               heads: dict | None = None, generated=(), allowed=(), nodes=None, obligations=None) -> dict:
    """`theorems` are the audit's theorem entries by name; `definition` is the root's generated
    definition, which the theorem's conclusion must be about."""
    result = {'theorem': goal['theorem'], 'declared_strength': goal['strength'],
              'derived_strength': None, 'claim_class': None, 'bound': None, 'domain': goal['domain'],
              'derived_domain': None, 'binding': None, 'caps': [],
              'caller_obligations': (obligations or {}).get(goal['theorem'], []), 'premises': None}
    theorem = theorems.get(goal['theorem'])
    if theorem is None:
        return {**result, 'status': 'rejected',
                'reason': 'theorem absent from the audited report (names are exact, not namespace-resolved)'}
    found = assess(theorem, load_heads() if heads is None else heads, definition, generated=generated,
                   allowed=allowed, audited=theorems, nodes=nodes)
    premises = premises_of(theorem, found['claims'])
    result.update(derived_strength=found['strength'], claim_class=found['claim_class'], bound=found['bound'],
                  derived_domain=found['domain'], binding=found['binding'], caps=found['caps'], premises=premises)
    if theorem.get('allowed') is not True:
        return {**result, 'status': 'rejected', 'reason': 'theorem has assurance policy violations'}
    if premises is None:
        return {**result, 'status': 'rejected',
                'reason': 'assurance report lacks the dependency closure (opaque_dependencies); regenerate it'}
    declared = goal['strength']
    if declared not in ORDERED:
        return {**result, 'status': 'rejected', 'reason': f'{declared} is not derivable from a theorem type'}
    if found['head_problem']:
        return {**result, 'status': 'rejected', 'reason': found['head_problem']}
    if found['binding'] != 'direct':
        return {**result, 'status': 'rejected',
                'reason': f'the conclusion is about {found["subject"] or "no recognised computation"}, not the '
                          f'root definition {definition} applied to its parameters ({found["binding"]})'}
    if found['rejected_hypotheses']:
        return {**result, 'status': 'rejected', 'reason': found['caps'][-1]}
    derived = found['strength']
    if derived is None and found['claim_class'] == GUARANTEED_RETURN_UNDER_PREMISE:
        return {**result, 'status': 'rejected',
                'reason': f'declared {declared} needs an unconditional claim; the conclusion only guarantees '
                          'a return under a schedule premise it states'}
    if derived is None or ORDERED[derived] < ORDERED[declared]:
        detail = f' ({"; ".join(found["caps"])})' if found['caps'] else ''
        return {**result, 'status': 'rejected',
                'reason': f'declared {declared} exceeds type-derived {derived or "no claim"}{detail}'}
    if found['scope'] != 'universal' and not declares_scoped(goal['domain']):
        return {**result, 'status': 'rejected',
                'reason': f'declared domain {goal["domain"]!r} is not marked scoped, but the derived domain is '
                          f'scoped: {json.dumps(found["domain"])}'}
    # Outcome evidence can only refuse an absence claim the declared strength asserts.
    for claim in OUTCOMES.STRENGTH_ABSENCE[declared] if outcome_counts is not None else ():
        verdict = OUTCOMES.absence(claim, outcome_counts)
        if verdict['status'] == 'refused':
            return {**result, 'status': 'rejected', 'reason': verdict['reason'], 'blocking': verdict['blocking']}
    return {**result, 'status': 'accepted', 'reason': None}


def _sibling(name, filename=None):
    spec = importlib.util.spec_from_file_location('claims_' + name,
                                                  Path(__file__).resolve().parent / (filename or f'{name}.py'))
    module = importlib.util.module_from_spec(spec)
    sys.dont_write_bytecode = True
    sys.modules[spec.name] = module  # dataclasses resolve annotations through sys.modules
    spec.loader.exec_module(module)
    return module


OUTCOMES = _sibling('outcomes')
MARKERS = _sibling('premise_markers')
REPO = ROOT


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


def root_definition(root: dict) -> str:
    return root['namespace'] + '.' + root['function'].removeprefix(root['prefix'])


def check(manifest_path: Path, report: dict, diffs=()) -> dict:
    project = _sibling('project')
    manifest = project.load_manifest(manifest_path)[0]
    theorems = audited_theorems(report)
    heads = load_heads()
    nodes = nodes_of(report)
    obligations = caller_obligations(report)
    current = _sibling('diff_report', 'diff-report.py').source_hashes(REPO) if diffs else {}
    for path in diffs:
        current_evidence(project, path, current)
    roots = []
    for root in manifest['roots']:
        counts = root_outcomes(project, root, diffs)
        definition = root_definition(root)
        module = nodes.get(definition, {}).get('module')
        generated = generated_definitions(nodes, {module}) if module else set()
        roots.append({'id': root['id'], 'outcomes': counts,
                      'goals': [check_goal(goal, theorems, counts, definition=definition, heads=heads,
                                           generated=generated, allowed=root['assumptions'], nodes=nodes,
                                           obligations=obligations)
                                for goal in root['goals']]})
    rejected = any(g['status'] != 'accepted' for root in roots for g in root['goals'])
    return {'schema_version': 1, 'status': 'fail' if rejected else 'pass', 'roots': roots,
            'scope': 'Strength is derived from the registered conclusion head (module and fingerprint) and capped '
                     'without non-vacuity and (partial) liveness witnesses. The conclusion must be about the root '
                     'definition; hypotheses may not mention generated definitions or claim heads; a scoped derived '
                     'domain needs a domain declared `scoped: ...`. caller_obligations lists the premises '
                     '(ALC-09, IOM-01) under which a claim about a function with an Allocator or Io parameter '
                     'holds: the caller passes the model one. premises lists what an accepted goal rests on '
                     'beyond its type: an inline-asm opaque in the closure carries ASM-01, and ASM-04 (allowlist '
                     'fault conditions) for a no-panic or guaranteed-return claim. Differential outcomes (when supplied) can only '
                     'refuse absence claims: capped, fuel-bounded, unsupported, unsupported-timer or unspecified '
                     'outcomes and observed failures reject a goal; error returns do not. Summaries must be bound to '
                     'the current tree (source/runner fingerprints and case hash) or the check fails. outcomes is '
                     'null for roots without evidence.'}


def head_identities(report: dict) -> dict:
    """Conclusion-head declarations seen in a report, for maintaining assurance/claim-heads.json."""
    seen = {}
    for theorem in report.get('theorems') or []:
        head = (statement_of(theorem) or {}).get('head')
        if isinstance(head, dict) and isinstance(head.get('name'), str):
            seen[head['name']] = {k: head.get(k) for k in ('module', 'kind', 'fingerprint')}
    return dict(sorted(seen.items()))


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    report_cmd = sub.add_parser('report', help='classify every audited theorem')
    heads_cmd = sub.add_parser('heads', help='list conclusion-head declarations (module, fingerprint)')
    check_cmd = sub.add_parser('check', help='reject manifest goals stronger than their theorem types')
    check_cmd.add_argument('manifest', type=Path)
    check_cmd.add_argument('--diff', type=Path, action='append', default=[],
                           help='diff-report summary JSON bound to the current tree; its outcomes can only '
                                'refuse absence claims')
    check_cmd.add_argument('--allow-dirty', action='store_true',
                           help='accept a report or tree with uncommitted tracked changes (recorded in the output)')
    for cmd in (report_cmd, heads_cmd, check_cmd):
        cmd.add_argument('--assurance', type=Path, required=True, help='scripts/assumptions.py report')
        cmd.add_argument('--output', type=Path)
    args = parser.parse_args(argv)
    try:
        report = json.loads(args.assurance.read_text())
        if args.command == 'report':
            result = classify(report)
        elif args.command == 'heads':
            result = head_identities(report)
        else:
            # A claim is only as current as its evidence: recompute the report's source/olean
            # digests and revision binding instead of trusting `status: pass` (H1).
            freshness = _sibling('assumptions').verify_fresh(report, args.allow_dirty)
            result = dict(check(args.manifest, report, args.diff), freshness=freshness)
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
