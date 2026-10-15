# Seen-floor: frame-relation decision required

Status: Task 06 architecture stop, 2026-10-15. Based on main `96dfa27e5` and the
unmerged WIP `codex/csl-seen-floor` at `16f0bb0f5`. No model or existing theorem
statement is changed in this report.

## Intended invariant and benefit

The model already uses `Mem.seen` to remember the last message id that each thread
observed at each atomic location. `floorPos` takes the maximum of that message's
position and the happens-before floor. A subsequent permitted read cannot select
an earlier position. This is read-read coherence, including a failed comparison
that observes another thread's write without acquiring that write's own clock.

The WIP adds `Mem.seenAt`, an accessor for that view, and `AMap.own`: when an atomic
location lies entirely in the frame, the stepping thread's view is preserved at
the location's new index. The existing `AMap.seen` preserves the other threads'
views during reindexing. Together they preserve every thread's view of a framed
location, including when retiring unrelated locations shifts its index.
This changes the logical step guarantee; `observeM`, `floorPos`, and the
interpreter's permitted-read behavior need no change for that guarantee.

The word API then represents a view as its position in the word's history:
`Word.ownPos`. `Word.Fresh` supplies distinct message ids below `Mem.nextMsg`.
Loads and failed comparisons read at or after the caller's old position and set
its position to the message observed; a successful RMW/comparison appends a new
message and advances the writer to that message. Other threads' positions do not
decrease. Unrelated steps must preserve those observations.

This is the missing fact for an Event waiter that observes another waiter's
`waiting` message: its next load must exclude the earlier `unset` message even
without a happens-before edge from that other waiter. Current `FEvent.Inv` instead
requires one waiter and happens-before evidence. `FCond.Inv` additionally has a
one-waiter state machine and newest-epoch assumptions. Neither restriction is
lifted by this report; the multi-waiter step regression remains required after
the framework decision and implementation.

## The existing statements and the WIP changes

On main, `ZigLean/Conc/Clock.lean` exports these unconditional/current-index-only
rules (implicit variables are shown by their use):

```lean
theorem FStepIn.observe (li id : Nat) :
    FStepIn hF m (observeM m li id)

theorem FStepIn.loadM (hc : m.current < m.clocks.size)
    (li : Nat) (ord : AtomicOrder) (msg : Msg) :
    FStepIn hF m (Conc.Proto.loadM m li ord msg)
```

The WIP strengthens `AMap`, hence `FStepIn`, and changes those statements to:

```lean
theorem FStepIn.observe {li : Nat} (id : Nat)
    (hnot : ¬ (m.atomics[li]!).In hF) :
    FStepIn hF m (observeM m li id)

theorem FStepIn.loadM (hc : m.current < m.clocks.size) {li : Nat}
    (ord : AtomicOrder) (msg : Msg)
    (hnot : ¬ (m.atomics[li]!).In hF) :
    FStepIn hF m (Conc.Proto.loadM m li ord msg)
```

`AMap.ofSome` also gains a premise preserving the current thread's view for
framed locations. The WIP updates the owned-word atomic-load proofs to establish
`hnot` from frame disjointness, as they already do for writes. Those callers can
discharge the new condition; the old general theorems cannot derive it from
their existing premises.

## Concrete obstruction

`tests/roadmap/sep-full/SeenFrameCX.lean` imports only `ZigLean.Conc.Clock`. It
constructs a location with two distinct messages, ids `0` and `1`, and thread 0's
view at id `1`. The frame contains every byte of the location. Observing id `0`
keeps the location unchanged but changes that view from `1` to `0` and decreases
`floorPos` from `1` to `0`.

* `admitted`: the existing `FStepIn.observe` proves the transition for that frame.
* `admitted_load`: the existing `FStepIn.loadM` also applies; its current-index
  premise is true.
* `in_frame`: the proposed `hnot` premise is false.
* `floor_decreases` and `no_floor_preservation`: even nondecreasing read floors
  do not follow from the current `FStepIn` relation.
* `read_options`: before the raw observation, `readOpts` contains only position
  `1`; afterwards it also contains position `0`.

This is a counterexample to the requested stronger frame invariant while
retaining the current theorem statements. It does not establish unsoundness of
current main: `FStepIn` currently promises no such invariant, and these lemmas
describe a raw observation with no requirement that an atomic read selected it
from `readOpts`. The actual permitted reads already enforce `floorPos`.

## Decision and continuation

Task 06 says that no memory-model change may weaken an existing theorem, and its
common rules require stopping on a statement change. Adding `hnot` is an extra
hypothesis in an existing theorem, and retaining the old unconditional theorem
under the proposed stronger relation contradicts the example above. No new
judgment, alternative frame relation, shim, premise, or allow-list entry is added
to work around that conflict.

The maintainer needs to decide whether to authorize strengthening the existing
frame relation and the corresponding observation/constructor theorem changes.
If authorized, reapply the memory-model portion of the WIP to current main while
preserving its newer message-coverage obligations, keep word facts in the
full-state library, and audit every constructor and caller of `AMap`/`FStepIn`.
Then prove the multi-waiter Event/Condition step, run the task's complete gates,
and update the retirement blocker only after that proof is checked.

Task 01 has not landed a nonlegacy word-vocabulary split. Do not copy the WIP's
new `Conc/WordSeen` import of the legacy `Conc/Word` into a new legacy user or
move the ratchet's structural entries without the required approval. The
existing `Sep/Full/Word` library is the starting point for placement analysis.

Task 07's source analysis identified another acceptance obligation for the
Condition generalization: semaphore signaling occurs while its mutex is held,
whereas current `FCond.Inv.lp`/`CondImpl.signal_wp` require an out-of-lock
signaller. Seen-floor alone must not be described as completing that prerequisite.
