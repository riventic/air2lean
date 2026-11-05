import Proofs.Sync.RwLock

/-!
# Reusable synchronization contracts (C14)

A contract is a `Prop` structure over the *operations* of a sync object, not over its code. A
client proof that takes a contract as a hypothesis never sees the std implementation: it receives
only the operation as an abstract function.

The mutex, semaphore and condition contracts are the full-state ones (`MutexImpl`, `SemImpl`,
`CondImpl`, for every implementation; the table in `docs/rwlock-contracts.md` lists them and their
proofs). This file keeps `RwContract`: the `Io.RwLock` operations `lockSharedUncancelable`,
`unlockShared`, `lockUncancelable`, `unlock`, proved by `rwLock` from the existing `RwLockRead`
specs, only for the restricted protocol of `Proofs/Sync/RwLock.lean` (reader 0, writer 1, the
counter resource `NPts`). It is over the legacy thread protocol (`Proto.WP`) and goes with
RwLock (`docs/legacy-retirement.md`).

**Out of scope (stated, not claimed).**
- *Fairness, termination and starvation freedom*: `RwContract` is partial correctness plus
  strict safety; a run that runs out of fuel satisfies every post. It does not state that a
  waiter is eventually woken or that `lock` eventually returns.
- *General RwLock*: the reusable `RwLock` contract for any number of readers and an arbitrary
  protected resource needs a new kit for the state word (`Proofs/Sync/RwLock.lean` fixes reader 0,
  writer 1 and `NPts`). `RwContract` only packages the restricted specs.
- *`Io.Event` / `ResetEvent`*: the translated events are proved against the full-state event
  contract (`EventImpl`, `ZigLean/Sep/Full/Event.lean`: `Sync.ioEvent`, `Threadsync.resetEvent`),
  which `handoff` uses (`Proofs/Handoff/`); its scope is one waiter at a time.
- *WaitGroup*: Zig 0.16.0's `examples/sync` has no translated `WaitGroup`; the 0.15.2
  `Thread.WaitGroup` proof (`Proofs/Threadsync/WaitGroup.lean`) is a fixed two-task client.
- *Condition broadcast, timeouts and cancellation* are not covered.
-/

open Zig Zig.Conc

namespace Sync.Contracts

/-! ## `Io.RwLock` (restricted) -/

section RwLock

open Sync.RwLockRead

variable {S : Type} [Inhabited S]

/-- The shared and exclusive `Io.RwLock` rules of the restricted protocol `proto E` of
`Proofs/Sync/RwLock.lean` (reader 0, writer 1, counter resource `NPts`), over a semaphore part
`E` with `E.Spec`. Not a contract for arbitrary readers or resources. -/
structure RwContract (E : Sync.RwLockRead.Sem S)
    (lockS unlockS lockX unlockX : Ptr → Io → ConcM Tgt Unit) : Prop where
  lockShared : ∀ {j : Bool} {io : Io} {G : ThreadId → Gh S} {m : Mem} {d : Nat},
    (proto E).inv (upd G 0 (gA (.ls j) Heap.empty default)) m →
    (proto E).WP 0 (lockS (bPtr.add 16) io) (fun _ G' m' d' => d' ≤ d ∧
      m'.current = 0 ∧ ∃ h, (proto E).inv (upd G' 0 (gA (.sh j) h default)) m') G m d
  unlockShared : ∀ {j : Bool} {h : Heap} {io : Io} {G : ThreadId → Gh S} {m : Mem} {d : Nat},
    (proto E).inv (upd G 0 (gA (.sh j) h default)) m →
    (proto E).WP 0 (unlockS (bPtr.add 16) io) (fun _ G' m' d' => d' ≤ d ∧
      m'.current = 0 ∧ (proto E).inv (upd G' 0 (gA (.dn j) Heap.empty default)) m') G m d
  lock : ∀ {k : Nat}, k < 2 → ∀ {io : Io} {G : ThreadId → Gh S} {m : Mem} {d : Nat},
    (proto E).inv (upd G 1 (gA (.wo k) Heap.empty default)) m →
    (proto E).WP 1 (lockX (bPtr.add 16) io) (fun _ G' m' d' => d' < d ∧
      m'.current = 1 ∧ ∃ h, NPts k h ∧ (proto E).inv (upd G' 1 (gA (.wn k) h default)) m') G m d
  unlock : ∀ {k : Nat} {hn : Heap}, NPts k hn → ∀ {io : Io} {G : ThreadId → Gh S} {m : Mem}
    {d : Nat}, (proto E).inv (upd G 1 (gA (.wn k) hn default)) m →
    (proto E).WP 1 (unlockX (bPtr.add 16) io) (fun _ G' m' d' => d' < d ∧
      m'.current = 1 ∧ (proto E).inv (upd G' 1 (gA (.wo k) Heap.empty default)) m') G m d

/-- **The translated `Io.RwLock` satisfies the restricted contract**, for every semaphore part
with `E.Spec` (`spec₀` gives it for the translated semaphore). -/
theorem rwLock {E : Sync.RwLockRead.Sem S} (hE : E.Spec) :
    RwContract E Io_RwLock_lockSharedUncancelable Io_RwLock_unlockShared
      Io_RwLock_lockUncancelable Io_RwLock_unlock where
  lockShared hi := lockS_spec hE hi
  unlockShared hi := unlockS_spec hE hi
  lock hk _ _ _ _ hi := wlock_spec hE hk hi
  unlock hp _ _ _ _ hi := wunlock_spec hE hp hi

end RwLock

end Sync.Contracts
