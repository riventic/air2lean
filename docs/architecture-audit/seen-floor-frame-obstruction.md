# Seen-floor: frame locality and multi-waiter audit

Status: 2026-10-16. The obstruction was analyzed on main
`958596cfce71634dbc6487336abd62714a6e6cd0` and the unmerged WIP
`codex/csl-seen-floor` at `16f0bb0f5`. The resumed implementation is based on main
`7ef586aa35afe7219e1bf16ad0ec2734cfe617c2`. The maintainer
[authorized](https://github.com/riventic/air2lean/pull/397#issuecomment-6210721921)
strengthening the existing frame relation and correcting `observe`, `loadM` and
`AMap.ofSome`, subject to generic discharge and preserved or stronger client
contracts. That implementation is in progress. Additional Event abstraction
corrections remain a
[pending decision](https://github.com/riventic/air2lean/pull/397#issuecomment-6211328134);
Event and Condition source are unchanged. The later capacity findings below are
source analyses unless explicitly marked kernel checked.

## Intended invariant and benefit

The model already uses `Mem.seen` to remember the last message id that each thread
observed at each atomic location. `floorPos` takes the maximum of that message's
position and the happens-before floor. A subsequent permitted read cannot select
an earlier position. This is read-read coherence, including a failed comparison
that observes another thread's write without acquiring that write's own clock.

The resumed change adds `Mem.seenAt`, an accessor for that view, and `AMap.own`: when an atomic
location lies entirely in the frame, the stepping thread's view is preserved at
the location's new index. The existing `AMap.seen` preserves the other threads'
views during reindexing. Together they preserve every thread's view of a framed
location, including when retiring unrelated locations shifts its index.
This changes the logical step guarantee; `observeM`, `floorPos`, and the
interpreter's permitted-read behavior need no change for that guarantee.

The semantic word lemmas represent a view as its position in the word's history:
`Word.ownPos`. `Word.Fresh` supplies distinct message ids below `Mem.nextMsg`.
`loadM_seen` establishes the position installed by a load; `ownPos_le_floor`
connects the old position to permitted reads. `rmwM_seen` establishes the new
writer position after appending at the end. Other threads' positions do not
decrease. The operation-level load/CAS/RMW integration through the full-state
library remains incomplete. Unrelated steps must preserve those observations.

This is the missing fact for an Event waiter that observes another waiter's
`waiting` message: its next load must exclude the earlier `unset` message even
without a happens-before edge from that other waiter. Current `FEvent.Inv` instead
requires one waiter and happens-before evidence. `FCond.Inv` additionally has a
one-waiter state machine and newest-epoch assumptions. Neither restriction is
lifted by this report; the multi-waiter step regression and complete task gates
remain required. Exact equality at a framed location follows from separation
and absence of an access there. Coherence alone permits a view to advance; the
soundness argument and primary references are in `docs/sep-threads.md`.

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

* On the baseline relation, the old `admitted` and `admitted_load` proofs apply;
  the latter's current-index premise is true.
* `in_frame`: the proposed `hnot` premise is false.
* `floor_decreases`: even nondecreasing read floors do not follow from the
  baseline `FStepIn` relation.
* `read_options`: before the raw observation, `readOpts` contains only position
  `1`; afterwards it also contains position `0`.
* The adapted `not_admitted`/`not_admitted_load` reject this transition under
  `AMap.own`; `permitted_advance` separately exhibits an allowed read whose view
  advances, so coherence cannot establish equality by itself.

The original counterexample was kernel checked at report head `6932dae54` on
main `a05b4747f`, with axioms `[propext, Classical.choice, Quot.sound]`. The
adapted regression was subsequently checked by the complete Lean prerequisite
and fresh Assurance kernel replay at `48012e0fb`. Its printed axioms are
`[propext, Quot.sound]` for `not_admitted` and `[propext]` for
`permitted_advance`. The historical result is separate from that validation.

This is a counterexample to the requested stronger frame invariant while
retaining the current theorem statements. It does not establish unsoundness of
current main: `FStepIn` currently promises no such invariant, and these lemmas
describe a raw observation with no requirement that an atomic read selected it
from `readOpts`. The actual permitted reads already enforce `floorPos`.

## Authorized correction and remaining boundary

Task 06 says that no memory-model change may weaken an existing theorem, and its
common rules require stopping on a statement change. Adding `hnot` is an extra
hypothesis in an existing theorem, and retaining the old unconditional theorem
under the proposed stronger relation contradicts the example above. No new
judgment, alternative frame relation, shim, premise, or allow-list entry is added
to work around that conflict.

The first correction is now authorized and preserves main's newer
message-coverage obligations. Word floor/freshness facts belong in the existing
full-state library. Atomic callers derive the outside-frame condition from
their existing ownership and disjointness evidence.

Event's current `Inv.frame`, `Inv.other`, `Inv.move`, `Inv.casOk`, `Inv.xchg`,
`MStep.op` and `MStep.sleep` quantify over destination memories without
constraining views or `nextMsg`. Keeping their other fields fixed while resetting
the seen id from `1` to `0`, or the counter to `0`, satisfies their memory
abstractions but invalidates a seen-floor or fresh-id invariant. `Inv.start`
similarly permits a singleton history with id `0` and counter `0`.
`Word.Op`, `Word.Keep` and the existing `LockWord.Step` do not supply the
missing information. Coherence does not prove facts about such arbitrary
destination memories. The additional helper/relation corrections require a
maintainer decision; they must be discharged from actual semantic steps by
generic rules, without an extra client assumption or a separate proof mechanism.

The existing `RestStep` (`Sep/Full/ThreadRest.lean:48–66`) also lacks both
seen transport and counter monotonicity. Its current `FOwned.restStep` consumer
needs neither: the missing consumer is the proposed multi-waiter protocol
stability. `Inv.frame` already obtains both from framed `FStepIn`. `Inv.other`
and `Inv.lstep` need both at the disjoint event word through `MStep` and
`LockWord.Step`; same-word move/read/CAS/exchange additionally need the actual
selected-position or append facts. Queue append, wake, woken and resume keep
atomics, views and counter directly; location preparation and initialization
need freshness evidence.

There are two current `RestStep` producers: `Word.Op.rest` (`Full/Word.lean`)
and `LockWord.Step.rest` (`Full/Lock.lean`). `Word.Op.current` identifies the
actor with the destination current thread; abstract `LockWord.Step` has no such
field. `RestStep` itself has no actor parameter and permits a current-thread
change. Any approved use of existing `AMap` here must therefore identify the
actual actor explicitly, rather than assume either memory's current field
universally. Framed disjoint-location transport permits active-word observation
advances and atomic-index reindexing; it is not global equality of views.
These are missing summary facts, not new helper or client premises. No
`RestStep`, `Word.Op`, Event or Condition statement is changed here.

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

## Checked implementation and dependency boundary

On clean `48012e0fb`, the official complete Lean prerequisite
(`scripts/full-build.sh --no-fixtures`) passed its root, diff and standalone
phases, including both regression fixtures. A subsequent focused run used the
existing private fixture universe, Assurance dependency extraction, kernel
replay and policy. Both cohorts passed the ordinary policy with no violation.
All 65 new or changed theorem roots were present: 54 production and 11
regressions. All three new production definitions, the `AMap.own` projection
and the fixture definitions were reachable from those roots. Actual source,
tool and project `.olean` bindings were unchanged during the run.

The stricter framework dependency requirement nevertheless failed for 13
production roots. Ordinary Assurance policy success is not framework acceptance:

- `FStepIn.storeM` and `rmwM`, plus the modified full-state atomic load,
  newest-write, pointer-load and spurious-CAS roots, reached registered legacy
  `StepIn` through `FStepIn.of_stepIn`, via `refl`, `setBlock` or `recordAt_of`.
- The changed existing `Word.Ok.read` reached registered `Grows`, `Keep`,
  `KeepK`, `BlkStep` and `LocsKeep`. Its `Word.Op` hypothesis and result already
  contain `BlkStep` and `LocsKeep` in their types; changing its proof alone
  cannot remove those two dependencies.
- The new `ownPos_keep` and `Fresh.keep` directly used legacy `Keep`. The new
  `Ok.prep_seen`, `Ok.load_seen`, `Ok.rmw_seen` and `Ok.cas_seen` reached legacy
  block/location relations through `Op`; load and CAS also reached `Ok.read`.

No root was excluded or legacy judgment reclassified. The other 52 roots,
including all 11 regressions, had no such dependency. Every root used only a
subset of `propext`, `Classical.choice` and `Quot.sound`; no missing dependency
node, `Strength`, `AllocBridge` or `toLegacy` route was found. The reused
`Zig.Conc.findIdx?_congr` is defined in `ZigLean.Conc.LockBase`, but its actual
type and proof graph contain only array/index mathematics.

The six new prospective helpers listed above had no retained consumer and were
removed. The existing `FStepIn.refl`, `setBlock` and `recordAt_of` proofs now
construct the target relation directly through existing `AMap` and memory
lemmas, with identical statements, including message coverage and constant-block
conditions. A bounded target build of Clock, Full.Word and the affected atomic
and thread-step callers passed all 75 jobs. This compile does not substitute for
a fresh dependency audit or complete prerequisite on the corrected source.
The previous 65-root result is preserved as evidence before the correction.

The retained `Word.Ok.read` type dependency is still an explicit retirement
boundary. No new legacy-facing transport rule or client assumption has been
introduced to hide it. Event/Condition steps, weak-CAS/futex integration,
complete task gates and the additional architecture decisions remain open;
Task 06 is not ready.

## Finite Event wake count

Source-only finding; no new multi-waiter counterexample has been kernel checked.
The current single-waiter theorem is not alleged unsound.

`FEvent.Inv.wake` (`ZigLean/Sep/Full/Event.lean:667`), `Fits.afterWake` (1066)
and `wp_wake` (1232) accept only `1 ≤ c` as their count condition. Their proofs
use `Inv.one` to show that every queued event waiter is selected. If the invariant
admits two queued waiters, a wake of one followed by the sole setter's
`sw → out` transition leaves a waiter queued with newest value `2` and no setter
at `sw`, violating the retained no-lost-wakeup field `Inv.q`.

The actual translated setter passes `4294967295 : BitVec 32` at
`Proofs/Sync/Gen.lean:686` and `Proofs/Threadsync/Gen.lean:938`.
`ZigLean/Conc/Call.lean:161–162,252–253` converts this using `n.toNat` to
`SyncOp.wake`; `Conc/Sched.lean:218–221` calls `Thread.futexWake`.
`Mem/Thread.lean:672–688` selects at most that finite number of queued ids and
removes only those selected. This path does **not** call the separate
`Os.Linux.wakeLimit` (`Os/Futex.lean:224`), which interprets a signed nonpositive
count as one. The two model boundaries must not be conflated.

For the high-level path, let `N = 4294967295`: `N + 1` distinct queued event
waiters, newest value `2`, and a sole setter at `sw` form the symbolic finite
counter-scenario to an unconditional all-selected claim. A wake of `N` leaves
one queued. No universal modeled-thread bound was found in the source:
`Mem.spawnLimit` defaults to `none`; `spawnAdmits` then accepts; the `available`
spawn policy ignores this budget; and `Thread.forkWith` extends the thread and
clock arrays. This is not permission to introduce a finite-capacity environment
premise. The all-selected fact must follow from an existing sound contract or
resource bound, or the exact obstruction must remain reported. The pending
wake-helper correction is additional to seen/freshness transport.

## Native wake correspondence and lifecycle boundary

The coordinated [source audit](https://github.com/riventic/air2lean/pull/397#issuecomment-6214305346)
checked every pinned release, with Zig 0.17 first. These findings are source
analyses, not new native runs or kernel-checked counterexamples.

| Zig | Source file | Linux wrapper | Darwin wrapper | Full-file SHA256 |
|---|---|---|---|---|
| 0.17.0 | `Io/Threaded.zig` | 1132–1135: saturates at `maxInt(i32)` | 1145–1151: `WAKE_ALL` when count > 1; retries interruption | `1a770001e309f24c8c58a9fdb3c095994c454cbfa9dba9d4f1dede2f134eeac7` |
| 0.16.0 | `Io/Threaded.zig` | 1128–1131: same saturation | 1141–1147: same flag and retry | `eb7bbb4ddf590ec3d0d2a1ee5c3845ef4984d9e440965a3e7c920cd0c906df94` |
| 0.15.2 | `Thread/Futex.zig` | 287–290: same saturation | 234–242: wake-all when count > 1 | `0b03207ea341c962122d4410cb52b52379a3e202be4556c6766efc74587a51b6` |
| 0.14.1 | `Thread/Futex.zig` | 287–290: signed cast or `maxInt(i32)` through the older wrapper | 234–242: same wake-all choice | `f1f8fd850c94e0eb99a9332a2e51dd793f4057e35b6e8f7a04efd46a65c04960` |

The files came from release-source CAS roots bound by
`zig-patch/versions.toml`. On Darwin, three distinct waiters and `wake(p, 2)`
give a small correspondence counter-scenario: successful native std requests
wake-all, whereas the current high-level `wakePick` removes exactly two.
On Linux, the high-level unsigned count can exceed the real wrapper's signed
saturation; an `INT_MAX + 1` queued state is an unrestricted-model scenario,
not a claimed realizable Linux process. `wakePick` chooses which waiters but
removes exactly the minimum of the count and queue size, rather than any
nondeterministically smaller cardinality.

The generated Event path bypasses those translated wrappers: the STD-05
`Io.futexWake` row in `Air2Lean/StdModels.lean` selects `Emit.threadCall`, then
`futexWakeC` converts the count with `n.toNat`. Existing
`Os.Linux.futex_3arg` signed-argument semantics and Darwin `__ulock_wake`
`WAKE_ALL` semantics are not reached. `--allocator-model translated` leaves
the thread rows active. `stdConflict`, the specialized `Io`/`Thread`
representation and the lack of a translated-thread mode are the generic
retirement barriers. The permanent repair requires translating the actual std
wrappers and concrete vtable implementation down to OS primitives. A target
clamp added to the current handwritten std substitution would not retire that
boundary. No such model correction is implemented here.

A live-native-ID capacity argument also needs a sound lifecycle boundary.
Linux v6.12's [allocation path](https://github.com/torvalds/linux/blob/v6.12/kernel/pid.c#L183)
and [sysctl setter](https://github.com/torvalds/linux/blob/v6.12/kernel/sysctl.c#L1720)
do not justify `tid < current pid_max` as a preserved live-thread invariant:
lowering that writable allocation setting can leave larger existing IDs alive.
That conclusion is an inference from those source paths. The numeric
`2^22` limit is kernel/configuration-specific, as
[threads.h](https://github.com/torvalds/linux/blob/v6.12/include/linux/threads.h)
and the [upper-bound check](https://github.com/torvalds/linux/blob/v6.12/kernel/pid.c#L612)
show. Positive signed-32-bit IDs and injectivity over actual live native
threads would suffice for the signed wake bound, once queue distinctness and
live membership are proved. The current impossible `Env.Valid` predicate does
not supply that argument.

Logical thread ids, clocks and history must stay fresh while native ids may be
released at actual termination and reused over disjoint lifetimes. Gated tasks
have no native thread; detaching or consuming a handle is not native exit.
The boundary must follow actual OS/scheduler transitions, including
[PID release](https://github.com/torvalds/linux/blob/v6.12/kernel/pid.c#L126)
and [namespace restrictions](https://github.com/torvalds/linux/blob/v6.12/kernel/fork.c#L2039).
It cannot silently filter future schedules through a static premise.

Adding an exhaustion-error branch under the existing `.available` policy is
also a statement change: `State.spawnOutcome` currently returns zero there,
and `Conc/Logic.lean`'s `spawnOutcome_eq` and guaranteed-spawn continuations
rely on it. A program whose spawn succeeds on that policy could take a new
failure branch after the proposed change. Free ids alone do not guarantee
native creation; Linux checks
[other resources](https://github.com/torvalds/linux/blob/v6.12/kernel/fork.c#L2072)
too. Preserve the guaranteed/fallible distinction and resolve resource
accounting in the existing full-state framework; no spawn-policy edit or new
environment assumption is made here.

## Condition counter capacity

Source-only finding about the actual translated implementation, not a failure of
its current single-waiter theorem. `Proofs/Sync/Gen.lean:58–65` represents
`Io_Condition_State.waiters` and `.signals` as 16-bit fields. Registration at
line 605 atomically adds one to the packed state, then lines 608–610 assert that
the returned old waiter count is below `65535`.

Thus, after `65535` registrations remain outstanding, the next registration
observes old count `65535` and fails the assertion (the packed increment has
already occurred). A generic multiple-waiter proof must account for this
intrinsic implementation capacity using its actual contract and client
resources. Read coherence does not establish a capacity bound. No new caller
premise, global thread bound or weakened public contract has been added here.

## Uninhabited OS environment validity predicate

Kernel checked on the clean, fully built main
`958596cfce71634dbc6487336abd62714a6e6cd0` baseline. This does not show an
existing client theorem is vacuous or establish unsoundness of current main.

`ThreadId` is `Nat` (`ZigLean/Mem/Basic.lean:136`), while `Os.Env.tid` maps it to
`BitVec 32` (`ZigLean/Os/Env.lean:57`). `Env.Valid.tid_inj` (line 77) requires
this map to be injective over **all** natural thread ids. No such map exists.
For any `env`, map the list `List.range (2 ^ 32 + 1)` through
`fun t => (env.tid t).toNat`. Injectivity makes the mapped list duplicate-free;
every element belongs to `List.range (2 ^ 32)`. Its length would therefore be at
most `2 ^ 32`, contradicting its length `2 ^ 32 + 1`. This argument is symbolic
and does not enumerate the range. The separate `tid_pos` field is unnecessary
for the contradiction, so it cannot repair it.

`Zig.Os.EnvCX.not_valid` in the existing
`tests/roadmap/os-threads/Check.lean` fixture contains this same symbolic proof.
The private baseline probe passed in 0.718 seconds of Lean work, with printed
axioms `[propext, Classical.choice, Quot.sound]`. Its source SHA256 was
`25c3d5782f38de3b92fb2894fb59411e4db1dface6f5421b0e5a981422662f5d`;
the actual imported `Os.Env.olean` SHA256 was
`b52ae115829f46c18dc4be4c8637e66f773a1144450919f5ca655bb29013f490`.
The baseline stayed clean, and the `Env.lean` source and compiled module were
unchanged before and after. The integrated fixture subsequently passed the
complete Lean prerequisite and fresh Assurance kernel replay on `48012e0fb`,
with the same printed standard three axioms. Final validation must bind to the
final source; the earlier baseline proof does not substitute for that gate.

A source search at main `958596cfce71634dbc6487336abd62714a6e6cd0` found no
Lean theorem taking `Env.Valid`, `tid_inj` or `tid_pos` as a premise; occurrences
are the definition and explanatory comments in `Os/Env.lean` and `Os/Clock.lean`.
The immediate impact is an uninhabited declared environment premise and a future
vacuity hazard. It must not be used to derive a legitimate Event wake bound.
An eventual repair needs validity scoped to the thread ids actually represented
by the run, with generic preservation and nonvacuity evidence; no such model
repair is implemented in this PR.
