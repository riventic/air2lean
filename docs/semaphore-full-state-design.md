# L10 semaphore migration design

Design only, based on `origin/main` `96dfa27e5` (2026-10-15). Task 06 must land on
`main` before this lane adds any implementation contract or translated instance.
This note changes no proof, claim, premise, or framework entry. The implementation
must use the existing full-state logic and `fsym`.

## Contract boundary

The proposed library home is `ZigLean/Sep/Full/Sem.lean`. The `SemImpl`
implementation contract supplies `wait` and `post`, each of type
`Ptr → Io → ConcM Tgt Unit`, with rules universal over the client protocol, its
ghost type, thread count, caller part, and permit resource. A client uses only
those rules. The translated `Io.Semaphore` will be proved one instance, with
`Sync.ioMutex` and `Sync.ioCond` as its underlying translated components.

Use `FAssn` and `Res` throughout. Let `Y : ThreadId → X` be the client ghost
values, `pv Y` the available count, and `Pool Y : FAssn` the free permits'
resource. The semaphore mutex protects the count's bytes together with `Pool Y`.
The count width, field offsets, alignment, and mutex contended value are layout
parameters with representation obligations; the current translation instantiates
them with a 64-bit count, count at `o`, mutex at `o + 8`, condition state at
`o + 12`, and epoch at `o + 16`. The encoded object has 24 bytes including
padding. Clients must retain the padding and their block extent for teardown.

No client resource is fixed to a counter, mailbox, pointer, or block. It may use
any existing full-state assertion, including knowledge and ghost receipts.
Extent fractions are bounds on blocks; they do not provide fractional ownership
of protected bytes. The contract needs no new resource algebra.

At each protocol-admissible transfer point, let `Y' = upd Y t x'` and require
`Y t = x`:

| Operation | Count obligation | Resource obligation | Caller part on return |
| --- | --- | --- | --- |
| `wait` | `pv Y ≠ 0`, `pv Y' = pv Y - 1` | `Pool Y ⊢ Pool Y' ⋆ T` | old part separated from a resource satisfying `T` |
| `post` | `pv Y' = pv Y + 1`, with the addition proved in range | `T ⋆ Pool Y ⊢ Pool Y'` | the old part with the deposited resource removed |

Here `T` is an arbitrary `FAssn`. The full-state resource split and validity
replace legacy heap union/disjointness. The combined resource must be preserved
when it moves between a caller part and the holder's pool: no byte, knowledge,
ghost authority, credit, or stack room may be manufactured. A library transfer
lemma must cover both directions; it must preserve `FOwned`, race ownership,
the lock invariant, and the client's remaining invariant. The current
`FLock.Fits.wp_hold` frames the caller part unchanged, so a permit transfer is
not merely another per-field instance of that rule.

The wait rule starts outside the semaphore's code and returns outside it, with
exactly one additional permit resource and the requested client ghost
transition. Its loop tests the protected count again after every condition wait.
The post rule returns one permit and its resource. Both return the caller's
mutex and condition places to outside their code, preserve unrelated caller
resources, and return `m'.current = t`. Other waiters may remain registered.
Retain the existing depth guarantees (`wait`:
`d' < d`; `post`: `d' ≤ d`) and `P.cost = none`. These bounds support protocol
adequacy; they are not a termination or fairness claim.

Use `FLock.Fits` with `FCond.prim` for the shared invariant, compatibility laws,
word separation, and stable client rest. Do not copy `Sem.Fits` into another
judgment or add a second semaphore proof engine. Clients discharge resource
transfers, ghost transitions, layout, stable-rest, progress, and the existing
mode/stack obligations of the implementation. The instance proves the actual
generated control flow with library rules.

In particular, the current `CondImpl.wait_wp` explicitly requires
`(L.part g).Plain`: a condition implementation may allocate stack locals. Keep
that requirement separate from the transferred `T`; preserve the caller's mode
with the existing plain-mode rules (`FOwned.start_plainRest`/`dupPlain`) for the
unmetered client proofs. Do not claim support for metered callers without
discharging their room/tick obligations. All six public client theorem statements
must remain unchanged; if an implementation rule would require a new public
premise, report that obstruction instead of adding it.

## Required condition support

Task 06 must establish usable read-read coherence for multiple condition waiters,
including unrelated steps and retirement/reindexing of atomic locations. A
caller-local observation floor may not disappear when another thread runs.
The state encoding must cover every representable waiter/signal count, with
`0 ≤ signals ≤ waiters` and the registration bound checked; it cannot keep
`FCond.SV` restricted to `0`, `1`, and `0x10001`. Counts and epoch wrap must follow
the translated arithmetic. Seen-floor alone does not justify treating an old
epoch value as the newest write or ruling out wraparound.

The multi-waiter rules must preserve registration/signal accounting and the
release/acquire ordering that makes the state read respect an observed epoch.
A signal reserves at most one signal; it does not hand a permit to a specific
waiter or prove every waiter signalled. Wake selection and spurious wakeups remain
arbitrary, and the semaphore loop must tolerate another waiter taking the
available permit first. Do not export `hone`, an all-epoch happens-before
premise, fixed thread IDs, or a no-competing-waiter premise as semaphore client
requirements.

There is also an independent condition-rule gap on the design base:
`CondImpl.signal_wp` requires `L.ph g = .out`, and `FCond.Inv.lp` puts signallers
outside the mutex. The generated `Io_Semaphore_post` calls
`Io_Condition_signal` **before unlocking**, as does the baton signal in
`Io_Semaphore_waitUncancelable` when permits remain. A general condition rule
must allow signaling while holding the associated mutex and retain the holder's
resource, as well as cover existing signaling outside it. Resolve this in the
full-state condition library and translated condition proof. Do not alter the
generated semaphore or add an assumed signal contract.

Strict safety includes the absence of deadlock. When the count is zero, a client
must supply its protocol's concrete progress argument; a semaphore cannot promise
progress for a program where every thread waits and nobody can post. While
signals, epoch increments, or wakes are pending, the library must account for
the runnable thread that completes them. No fairness assumption is added.

## Existing framework boundary requiring coordinator confirmation

Task 07 describes blocking wait/post as `CTriple`s. On the design base,
`ZigLean/Sep/Full/Conc.lean` explicitly fails closed at futex wait/wake, spawn,
and join stops. Its `WP.call_fowned` bridge runs a `CTriple` inside a protocol;
it does not prove the converse or supply a rule for those stops.

The implementable proposal follows the already accepted `MutexImpl` and
`CondImpl` pattern: full-state `Proto.WP` method contracts and `fsym` WP walks,
with `FTTriple`/`CTriple` library rules where their existing semantics apply.
`Proto.WP` was approved as target in the coordinator decisions of
[legacy-retirement.md](legacy-retirement.md). Confirm that this is the intended
reading of Task 07 before implementation. A literal `CTriple` requirement for
blocking synchronization would need an approved framework change; this lane
must not silently introduce one or weaken the schedule statements.

The new implementation contract is also detected by the structural framework
ratchet. Its eventual registration must use the maintainer's explicit approval,
not a fabricated approval string or a new unapproved `Fits` judgment. This
design PR leaves `assurance/proof-framework.json` unchanged.

## Clients and retirement order

Follow [#341](https://github.com/riventic/air2lean/pull/341),
[#346](https://github.com/riventic/air2lean/pull/346), and
[#349](https://github.com/riventic/air2lean/pull/349): generic client protocols
are independent of Zig version and implementation; version-specific files walk
only their generated code and instantiate its checked implementation.

1. After Task 06 lands, merge current `main`, perform full worktree initialization,
   and add the generic library transfer/condition rules and translated instance.
   Use `FLock.Fits.wp_readRest` for the read-shared `io` prefix and the general
   holder rule for count loads/stores. Check whether
   [#385](https://github.com/riventic/air2lean/pull/385) has landed before relying
   on the executor applying `wp_hold` directly; it was open at design time.
2. Migrate `SemCounter` through a generic protocol: the free initial permit owns
   `n`; a thread that takes it owns `n`; post returns the updated counter. Preserve
   the two increments per thread, spawn policy, join obligations, and final free.
3. Migrate `Mailbox` through a generic protocol and only the semaphore methods:
   main transfers the unwritten message to the producer at spawn; post publishes
   both fields; wait transfers them to the consumer before its reads. The
   existing mailbox is a Lean model client, not a translated Zig export; retain
   that distinction in claims.
4. Retire `Proofs/Sync/Lock.lean` after its callers use `MutexImpl`.
   `Proofs/Sync/Contracts.lean` also depends on its legacy `MutexOps`,
   `SemContract`, and `CondContract`; migrate their callers and remove obsolete
   wrappers, or record a concrete remaining-user deletion plan in the same PR.
   Remove the obsolete import in `tests/review/AllProofs.lean` when deleting Lock.
5. Coordinate the embedded semaphore boundary with L11. The legacy `Sem.Spec`
   named in the task actually lives in `Proofs/Sync/RwLock.lean`; L11 owns its
   deletion. Its replacement must use the same generic semaphore rules and
   transfer the complete protected resource through the last-reader handoff.

Each implementation slice lands independently before the next is branched from
`main`; no stack on an unmerged prerequisite. Remove migrated files from
`legacy_users` only when their imports and proof bodies actually permit it.
The condition/semaphore legacy rules are deleted only after their last caller.
Any transitional workaround gets an engine-ledger entry with a descriptive slug,
exact residual goal, affected files, and deletion condition; do not copy a rule
into a client to bypass missing `fsym` support. Existing ledger row 76 tracks
the read-rest and holder copies in Semaphore/SemCounter and other lanes; remove
only this lane's sites until all users have migrated.

## Statements and validation to preserve

Preserve the statements of all six public results verbatim, including the
available-spawn premise, arbitrary placement, fuel and oracle, and the existing
stack-overflow exception of the safety statements:

| File | All completed schedules | All-schedule safety | Kernel nonvacuity witness |
| --- | --- | --- | --- |
| `Proofs/Sync/SemCounter.lean` | `semaphoreCounter_spec`: `.ok 4` | `semaphoreCounter_safe` | `semaphoreCounter_completes`: existing environment, oracle zero, fuel 1000, result 4 |
| `Proofs/Sync/Mailbox.lean` | `mailbox_spec`: `.ok 34` | `mailbox_safe` | `mailbox_completes`: existing environment, oracle zero, fuel 1000, result 34 |

Removing `Conc.Unroll` may not drop the completion witnesses or replace them
with an assumption. Use the existing shared kernel-checked scheduler/loop
lemmas, coordinated with their retirement owner. If `fsym` cannot perform the
required bounded run proof, report that precise engine gap instead of adding a
new tactic, per-client evaluator, `native_decide`, or weaker existence claim.

Mutation checks run in private restricted check trees and record the first
proof failure and log for each mutation:

- Initial `SemCounter` count `1 → 0` must break the initial resource/progress
  proof or the existing completion witness; `1 → 2` must fail the single-owner
  invariant rather than granting two owners of `n`.
- Change `post`'s count update from `+1` to `+2` or suppress it. The translated
  instance must fail its count/transfer obligation. Apply this to generated
  check-tree code, or regenerate after mutating the Zig source; do not mutate
  only an unused initializer definition.
- Move or omit a mailbox producer store, or publish before both stores. The
  resource transfer or result proof must fail; `.ok 34` remains the required post.
- The multi-waiter library regression must include two registered waiters,
  competing signal consumption, arbitrary wake selection, spurious wakeup,
  and an observed epoch that cannot be forgotten by an unrelated step.

The default 0.16.0 full build and the 0.17.0 sync check tree must both explicitly
build the semaphore and both clients. The existing 0.17.0 CI step lists only
Event, Cond, Handoff, and Mutex, so extend the declared fixture/CI coverage in
the implementation PR. Build the applicable aarch64 translation/native rows as
well; list their actual generated inputs rather than assuming the default tree
establishes cross-target coverage.

Before an implementation PR is ready, run the task's full gate sequence:
`scripts/full-build.sh`; touched fixture checks plus alloc-fba, lists-fba,
alloc-arena, sep-auto, one-logic and claims; `scripts/fixture-checks.sh` and
`scripts/gate.sh` where present; `scripts/regen.sh --pr`; `scripts/preflight.sh`;
and `scripts/proof-framework.py --base origin/main`. Run heavy work through the
shared CAS and `scripts/build-guard.py` with reports/logs after obtaining a
coordinator build slot. Review and simplify every PR. Do not commit whole-tree
generated artifacts. Only a fully gated implementation gets a `READY` comment;
the task coordinator merges it.
