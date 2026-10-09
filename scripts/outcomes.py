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
    # Includes every no-clock timer/timed-wait path: the default model has no clock (TMR-01),
    # so `time.Timer` and `Futex.timedWait` with a timeout are `.unspecified` at run time.
    UNSPECIFIED = 'unspecified_behavior'
    UNSUPPORTED = 'unsupported_semantics'
    DEADLOCK = 'deadlock'
    # The selected stack budget ran out (`Zig.Error.stackOverflow`, MM-5).
    STACK_OVERFLOW = 'stack_overflow'
    # Tests only observe scheduler fuel exhaustion (`bounded_no_result`); it is not divergence.
    DIVERGENCE = 'divergence'
    SEARCH_CAP = 'search_cap'


# Model failures. A partial or total triple rules out each of them (`Zig.Error`); a Zig error
# union value is an ordinary returned value and is not among them.
SAFETY_FAILURES = frozenset({Outcome.PANIC, Outcome.ILLEGAL, Outcome.UNSPECIFIED, Outcome.DEADLOCK,
                             Outcome.STACK_OVERFLOW})
# Evidence that cannot show a failure is absent, whatever was observed elsewhere.
INCOMPLETE = frozenset({Outcome.SEARCH_CAP, Outcome.DIVERGENCE, Outcome.UNSPECIFIED, Outcome.UNSUPPORTED})
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
    'deadlock': Outcome.DEADLOCK,
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
    'illegal_exclusion': Outcome.ILLEGAL,
    'unspecified_exclusion': Outcome.UNSPECIFIED,
    'stack_overflow_exclusion': Outcome.STACK_OVERFLOW,
    'search_cap': Outcome.SEARCH_CAP,
    'bounded_no_result': Outcome.DIVERGENCE,
}


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
    found = {o.value: counts[o.value] for o in Outcome if o in blocking and counts.get(o.value)}
    if not found:
        return {'status': 'not_refuted', 'blocking': {}, 'reason': None}
    return {'status': 'refused', 'blocking': found,
            'reason': f'{claim} refused: evidence includes ' + ', '.join(f'{k} ({v})' for k, v in found.items())
                      + '; capped, fuel-bounded, unsupported, unspecified/timer or observed failure '
                        'outcomes cannot support proved absence'}
