#!/usr/bin/env python3
"""Shared outcome taxonomy for proof, claim and coverage reports (V06).

The differential runner (`scripts/diff-report.py`) types every observation with a `Kind` and
every comparison with a `Status`. This module maps those observations onto one outcome
taxonomy and decides which outcomes prevent an absence claim. It is pure and stdlib-only;
`scripts/claims.py` and `scripts/project.py coverage` both use it.

Evidence can only refuse an absence claim. A sampled run never proves the absence of a failure,
and only a type-derived or directly bound theorem can support one.
"""
from __future__ import annotations

from collections import Counter
from enum import Enum


class Outcome(str, Enum):
    # Names match the preflight `outcomes` record in scripts/project.py where both exist.
    VALID = 'valid'
    NONDETERMINISTIC_VALID = 'nondeterministic_valid'
    ERROR_RETURN = 'error_return'
    PANIC = 'panic'
    ILLEGAL = 'illegal_behavior'
    UNSPECIFIED = 'unspecified_behavior'
    # Unsupported timer semantics: the default model has no clock (TMR-01), so `time.Timer`,
    # `Futex.timedWait` with a timeout and the timed scheduler's no-clock paths throw
    # `Zig.Error.unsupportedTimer`. Kept apart from `.unspecified` results.
    UNSPECIFIED_TIMER = 'unspecified_timer'
    UNSUPPORTED = 'unsupported_semantics'
    DEADLOCK = 'deadlock'
    # A CPU fault of an allowlisted inline-asm instruction (`Zig.Error.trap`, ASM-04).
    HARDWARE_TRAP = 'hardware_trap'
    # The selected stack budget ran out (`Zig.Error.stackOverflow`, MM-5).
    STACK_OVERFLOW = 'stack_overflow'
    # Tests only observe scheduler fuel exhaustion (`bounded_no_result`); it is not divergence.
    DIVERGENCE = 'divergence'
    SEARCH_CAP = 'search_cap'


# Model failures (`Zig.Error`). A total triple rules out each of them; a partial one each but
# STACK_OVERFLOW, which it reads as non-termination (premise STK-01). A Zig error union value is
# an ordinary returned value and is not among them. Observed stack overflow still refuses an
# absence claim: sampled evidence is conservative.
SAFETY_FAILURES = frozenset({Outcome.PANIC, Outcome.ILLEGAL, Outcome.UNSPECIFIED, Outcome.UNSPECIFIED_TIMER,
                             Outcome.DEADLOCK, Outcome.HARDWARE_TRAP, Outcome.STACK_OVERFLOW})
# Evidence that cannot show a failure is absent, whatever was observed elsewhere.
INCOMPLETE = frozenset({Outcome.SEARCH_CAP, Outcome.DIVERGENCE, Outcome.UNSPECIFIED, Outcome.UNSPECIFIED_TIMER,
                        Outcome.UNSUPPORTED})
# Why each blocking outcome refuses an absence claim; reports name every class found.
REFUSAL_REASONS = {
    Outcome.SEARCH_CAP: 'capped schedule search',
    Outcome.DIVERGENCE: 'fuel-bounded no-result run',
    Outcome.UNSPECIFIED: 'unspecified result',
    Outcome.UNSPECIFIED_TIMER: 'unsupported timer',
    Outcome.UNSUPPORTED: 'unsupported semantics',
    Outcome.PANIC: 'observed panic',
    Outcome.ILLEGAL: 'observed illegal behavior',
    Outcome.DEADLOCK: 'observed deadlock',
    Outcome.HARDWARE_TRAP: 'observed hardware trap',
    Outcome.STACK_OVERFLOW: 'observed stack overflow',
}
# Absence claims (scripts/claims.py names) and the outcomes each one denies.
ABSENCE_CLAIMS = {
    'no-panic': SAFETY_FAILURES,
    'guaranteed-return': SAFETY_FAILURES | {Outcome.DIVERGENCE},
}
# Absence claims asserted by each declared manifest strength (docs/claim-strength.md).
STRENGTH_ABSENCE = {'safety': ('no-panic',), 'partial_correctness': ('no-panic',),
                    'total_correctness': ('no-panic', 'guaranteed-return')}

# Model observation kinds of scripts/diff-report.py. `None` marks a comparison or harness
# failure that is not a model outcome; every other unknown kind fails closed as unsupported.
DIFF_KINDS = {
    'value': Outcome.VALID,
    'error_return': Outcome.ERROR_RETURN,
    'model_panic': Outcome.PANIC,
    'illegal': Outcome.ILLEGAL,
    'unspecified': Outcome.UNSPECIFIED,
    'unspecified_timer': Outcome.UNSPECIFIED_TIMER,
    'deadlock': Outcome.DEADLOCK,
    'trap': Outcome.HARDWARE_TRAP,
    'stack_overflow': Outcome.STACK_OVERFLOW,
    'bounded_no_result': Outcome.DIVERGENCE,
    'search_cap': Outcome.SEARCH_CAP,
    'native_panic': None,
    'native_signal': None,
    'input_failure': None,
    'native_harness_failure': None,
}
# Comparison statuses that imply a model outcome, for rows without `model_kind`.
DIFF_STATUSES = {
    'value_match': Outcome.VALID,
    'error_return_match': Outcome.ERROR_RETURN,
    'panic_match': Outcome.PANIC,
    'ub_excluded': Outcome.PANIC,
    'trap_match': Outcome.HARDWARE_TRAP,
    'illegal_exclusion': Outcome.ILLEGAL,
    'unspecified_exclusion': Outcome.UNSPECIFIED,
    'unspecified_timer_exclusion': Outcome.UNSPECIFIED_TIMER,
    'stack_overflow_exclusion': Outcome.STACK_OVERFLOW,
    'search_cap': Outcome.SEARCH_CAP,
    'bounded_no_result': Outcome.DIVERGENCE,
}


# Outcomes a contract can admit. The incomplete classes (capped search, unspecified or unsupported
# results, unsupported timers) are properties of the evidence or the model, not of a program: no
# contract admits them, and observing one leaves the contract unassessed.
CONTRACT_OUTCOMES = frozenset(Outcome) - INCOMPLETE


def denied_by(strength: str) -> frozenset[Outcome]:
    """Outcomes that a goal of this strength rules out (the failures of its absence claims)."""
    return frozenset().union(*(ABSENCE_CLAIMS[c] for c in STRENGTH_ABSENCE.get(strength, ())))


def default_admits(strength: str) -> frozenset[Outcome]:
    """What a contract admits unless it declares otherwise. A strength with an absence claim
    (safety, partial and total correctness) admits returned values and error returns (a returned
    value, never a model failure): failures are admitted only by explicit declaration. A strength
    that claims nothing about failures (resource bound, correspondence) is not refuted by one."""
    return CONTRACT_OUTCOMES - (SAFETY_FAILURES if denied_by(strength) else frozenset())


def contract_admits(strength: str, declared) -> frozenset[Outcome]:
    """The outcomes a goal's contract admits; raises ValueError for a declaration that is unsound.

    `declared` is None (use the strength's default) or a list of outcome names. A declaration may
    admit documented failures (a function that panics on a bad input) but never an outcome its own
    strength rules out, an incomplete class, an unknown name or a duplicate."""
    if declared is None:
        return default_admits(strength)
    if not isinstance(declared, list) or not declared or not all(isinstance(n, str) for n in declared):
        raise ValueError('outcomes.admits must be a nonempty list of outcome names')
    if len(set(declared)) != len(declared):
        raise ValueError('outcomes.admits lists an outcome twice')
    known = {o.value: o for o in Outcome}
    unknown = sorted(set(declared) - set(known))
    if unknown:
        raise ValueError(f'outcomes.admits names unknown outcomes {unknown}; known: {sorted(known)}')
    admitted = frozenset(known[n] for n in declared)
    if admitted - CONTRACT_OUTCOMES:
        raise ValueError('outcomes.admits cannot admit ' + ', '.join(sorted(o.value for o in admitted - CONTRACT_OUTCOMES))
                         + ': incomplete-evidence classes are not program outcomes')
    if admitted & denied_by(strength):
        raise ValueError(f'outcomes.admits admits {sorted(o.value for o in admitted & denied_by(strength))}, '
                         f'which a {strength} goal rules out')
    return admitted


def contract(strength: str, declared, counts: dict[str, int]) -> dict:
    """A goal's outcome contract against sampled outcome counts. Evidence can only refute it:
    `refuted` (an outcome the contract does not admit was observed), `unassessed` (an incomplete
    class was observed, so the evidence cannot confirm it), `no_evidence`, else `not_refuted`.
    Error returns are admitted outcomes of their own, never a model failure."""
    admitted = contract_admits(strength, declared)
    violations = {o.value: counts[o.value] for o in Outcome
                  if counts.get(o.value) and o in CONTRACT_OUTCOMES and o not in admitted}
    incomplete = {o.value: counts[o.value] for o in Outcome if counts.get(o.value) and o in INCOMPLETE}
    status = ('refuted' if violations else 'unassessed' if incomplete else 'not_refuted' if counts else 'no_evidence')
    return {'admits': sorted(o.value for o in admitted), 'source': 'declared' if declared is not None else f'default for {strength}',
            'observed': dict(counts), 'violations': violations, 'incomplete': incomplete, 'status': status,
            'reason': (None if status in ('not_refuted', 'no_evidence') else
                       'observed outcomes outside the contract: ' + ', '.join(f'{k} ({v})' for k, v in violations.items())
                       if violations else 'incomplete evidence cannot confirm the contract: '
                       + ', '.join(f'{k} ({v})' for k, v in incomplete.items()))}


def case_outcomes(row: dict) -> frozenset[Outcome]:
    """Model outcomes of one differential case row (`<summary>.jsonl`)."""
    found = set()
    status, kind = row.get('status'), row.get('model_kind')
    if status in DIFF_STATUSES:
        found.add(DIFF_STATUSES[status])
    if kind is not None:
        outcome = DIFF_KINDS.get(kind, Outcome.UNSUPPORTED) if isinstance(kind, str) else Outcome.UNSUPPORTED
        if outcome is not None:
            found.add(outcome)
    schedule = row.get('schedule')
    if isinstance(schedule, dict):
        if schedule.get('status') == 'capped':
            found.add(Outcome.SEARCH_CAP)
        if schedule.get('saw_no_result'):
            found.add(Outcome.DIVERGENCE)
        if Outcome.VALID in found:
            # A schedule search chose this value among interleavings.
            found.remove(Outcome.VALID)
            found.add(Outcome.NONDETERMINISTIC_VALID)
    return frozenset(found)


def count(rows) -> dict[str, int]:
    counts = Counter(outcome.value for row in rows for outcome in case_outcomes(row))
    return {outcome.value: counts[outcome.value] for outcome in Outcome if counts[outcome.value]}


def absence(claim: str, counts: dict[str, int]) -> dict:
    """Whether outcome evidence refuses an absence claim. Clean evidence proves nothing."""
    blocking = INCOMPLETE | ABSENCE_CLAIMS[claim]
    found = [o for o in Outcome if o in blocking and counts.get(o.value)]
    if not found:
        return {'status': 'not_refuted', 'blocking': {}, 'reason': None}
    return {'status': 'refused', 'blocking': {o.value: counts[o.value] for o in found},
            'reason': f'{claim} refused: evidence includes '
                      + ', '.join(f'{o.value} ({counts[o.value]}: {REFUSAL_REASONS[o]})' for o in found)
                      + '; capped, fuel-bounded, unsupported, unspecified or observed failure outcomes '
                        'cannot support proved absence'}
