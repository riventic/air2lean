import ZigLean.Conc.Basic
import ZigLean.Basic
import ZigLean.Mem.Thread

/-!
# Calls and sync ops in a concurrent function

`Zig.CM Tgt σ α`: the body monad of a concurrent function, its locals over `ConcM`. The lifts
of calls to the other function kinds (`callMC`, `callRC`), the sync ops that `Emit.lean` writes
(each atomic op: a `pick` of the oracle, then the op in `MemM`; `spawnC`, `joinC`), and the lemmas
that `partial_fixpoint` needs to see through them (as `ZigLean/Mem/Basic.lean` has for `MM`).
-/

namespace Zig

/-- The body monad of a concurrent function. -/
abbrev CM (Tgt σ α : Type) := StateT σ (ConcM Tgt) α

variable {Tgt σ α : Type}

/-- A call from a concurrent function to another one. -/
@[inline] def callC (r : ConcM Tgt α) : CM Tgt σ α := StateT.lift r

/-- A call from a concurrent function to a function that uses memory: no stop. -/
@[inline] def callMC (r : MemM α) : CM Tgt σ α := StateT.lift (ConcM.liftMem r)

/-- A call from a concurrent function to a pure function. -/
@[inline] def callRC (r : Result α) : CM Tgt σ α := StateT.lift (ConcM.liftMem (StateT.lift r))

/-- A choice of the oracle among `count m` options (`SyncOp.pick`): another thread can run
first. -/
def pickC (count : Mem → Nat) : CM Tgt σ Nat := StateT.lift (ConcM.sync (Tgt := Tgt) (.pick count))

/-! ### Atomic ops: the oracle picks the message or the place (`ZigLean/Mem/Thread.lean`) -/

def atomicLoadC {n : Nat} (ord : AtomicOrder) (align : Nat) (p : Ptr) : CM Tgt σ (BitVec n) := do
  let c ← pickC (loadCount n ord align p)
  callMC (atomicLoadAt c ord align p)

def atomicStoreC {n : Nat} (ord : AtomicOrder) (align : Nat) (p : Ptr) (v : BitVec n) :
    CM Tgt σ Unit := do
  let c ← pickC (storeCount n ord align p)
  callMC (atomicStoreAt c ord align p v)

def atomicRmwC {n : Nat} (op : RmwOp) (signed : Bool) (ord : AtomicOrder) (align : Nat) (p : Ptr)
    (v : BitVec n) : CM Tgt σ (BitVec n) := do
  let c ← pickC (rmwCount n ord align p)
  callMC (atomicRmwAt c op signed ord align p v)

def cmpxchgC {n : Nat} (succ fail : AtomicOrder) (align : Nat) (p : Ptr) (expected new : BitVec n) :
    CM Tgt σ (Option (BitVec n)) := do
  let c ← pickC (casCount n succ align p expected)
  callMC (cmpxchgAt c succ fail align p expected new)

def atomicLoadAsC (α : Type) {n : Nat} [Packed α n] (ord : AtomicOrder) (align : Nat) (p : Ptr) :
    CM Tgt σ α := do
  let c ← pickC (loadCount n ord align p)
  callMC (atomicLoadAs α c ord align p)

def atomicStoreAsC {α : Type} {n : Nat} [Packed α n] (ord : AtomicOrder) (align : Nat) (p : Ptr)
    (v : α) : CM Tgt σ Unit := do
  let c ← pickC (storeCount n ord align p)
  callMC (atomicStoreAs c ord align p v)

def atomicRmwAsC {α : Type} {n : Nat} [Packed α n] (op : RmwOp) (ord : AtomicOrder) (align : Nat)
    (p : Ptr) (v : α) : CM Tgt σ α := do
  let c ← pickC (rmwCount n ord align p)
  callMC (atomicRmwAs c op ord align p v)

def cmpxchgAsC {α : Type} {n : Nat} [Packed α n] (succ fail : AtomicOrder) (align : Nat) (p : Ptr)
    (expected new : α) : CM Tgt σ (Option α) := do
  let c ← pickC (casCount n succ align p (Packed.toBits expected))
  callMC (cmpxchgAs c succ fail align p expected new)

/-- Weak CAS has one scheduler choice covering both message selection and spurious failure. -/
def cmpxchgWeakC {n : Nat} (succ fail : AtomicOrder) (align : Nat) (p : Ptr)
    (expected new : BitVec n) : CM Tgt σ (Option (BitVec n)) := do
  let c ← pickC (weakCasCount n succ align p expected)
  callMC (cmpxchgWeakAt c succ fail align p expected new)

def cmpxchgWeakAsC {α : Type} {n : Nat} [Packed α n] (succ fail : AtomicOrder) (align : Nat)
    (p : Ptr) (expected new : α) : CM Tgt σ (Option α) := do
  let c ← pickC (weakCasCount n succ align p (Packed.toBits expected))
  callMC (cmpxchgWeakAs c succ fail align p expected new)

/-- `Thread.spawn`: a new thread, or a declared error when the run's environment lets assignment
fail (`Env.spawn`, `docs/std-models.md` §Thread model). -/
def spawnC (t : Tgt) : CM Tgt σ (Except ErrName ThreadId) :=
  StateT.lift (ConcM.sync (.spawn t))

/-- `Thread.join`: waits until thread `tid` ends. -/
def joinC (tid : ThreadId) : CM Tgt σ Unit := StateT.lift (discard (ConcM.sync (Tgt := Tgt) (.join tid)))

/-! ### Futex (`std.Io`, 0.16.0; `docs/std-models.md` §Thread model) -/

/-- `std.Io`: the model has one `Io`. Its fields (`userdata`, the `vtable` of function
pointers) are not translated: the std code calls the futex through `Io.futexWait` and
`Io.futexWake`, which are the model. -/
structure Io where
  deriving DecidableEq, Repr, Inhabited

/-- 16 bytes, the size of `std.Io` (two pointers). -/
instance : Enc Io where
  size := 16
  align := 8
  encode _ := Array.replicate 16 (.int 0)
  decode _ := pure ⟨⟩

/-- `Io.futexWaitUncancelable(T, ptr, expected)`: the `u32` bits of `expected`. -/
def futexWaitC {α : Type} {n : Nat} [Packed α n] (_ : Io) (p : Ptr) (expected : α) : CM Tgt σ Unit :=
  StateT.lift (discard (ConcM.sync (Tgt := Tgt) (.wait p ((Packed.toBits expected).setWidth 32))))

/-- `Io.futexWait(T, ptr, expected)`: as `futexWaitC`; the model never cancels
(`error.Canceled` does not happen). -/
def futexWaitCancelableC {α : Type} {n : Nat} [Packed α n] (io : Io) (p : Ptr) (expected : α) :
    CM Tgt σ (Except ErrName Unit) := do
  futexWaitC io p expected
  pure (.ok ())

/-- `Io.futexWake(T, ptr, max_waiters)`. -/
def futexWakeC (_ : Io) (p : Ptr) (n : BitVec 32) : CM Tgt σ Unit :=
  StateT.lift (discard (ConcM.sync (Tgt := Tgt) (.wake p n.toNat)))

/-! ### `Io.Group` (0.16.0; `docs/std-models.md` §Thread model)

A task of a group that gets its own thread is a model thread: the group records it
(`Mem.groups`), and `Group.await` joins each task of the group. `Group.async` does not promise a
thread: std runs the task in the caller or defers it until `await`, so the generated code calls
`groupAsyncWithPolicyC` (`ZigLean/Conc/Spawn.lean`), an oracle choice among `groupAsyncC` (a
thread), the caller (eager) and `groupDeferC` (deferred), which the run's environment picks
(`Env`). When the environment's assignment fails (`SpawnPolicy.fallible`), `Group.async` runs
the task in the caller and `Group.concurrent` returns `ConcurrencyUnavailable`. The model never
cancels, so `Group.cancel` is `await`. -/

/-- One outcome of `Io.Group.async(g, io, function, args)`: the task `t` runs as a new thread of
the group. -/
def groupAsyncC (g : Ptr) (_ : Io) (t : Tgt) (fallback : ConcM Tgt Unit) : CM Tgt σ Unit := do
  match ← StateT.lift (ConcM.sync (.spawn t)) with
  | .ok tid => callMC (Thread.groupAdd g tid)
  | .error _ => callC fallback

/-- One outcome of `Io.Group.async`: the task `t` is deferred until the group's `await` or
`cancel` (`SyncOp.spawnGated`): a thread of the group that starts only once `Thread.groupTake`
releases it. In std this is the task that runs inside `await`. -/
def groupDeferC (g : Ptr) (_ : Io) (t : Tgt) : CM Tgt σ Unit := do
  let tid ← StateT.lift (ConcM.sync (.spawnGated t))
  callMC (Thread.groupAdd g tid)

/-- `Io.Group.concurrent`: a thread of the group, or `error.ConcurrencyUnavailable` when the
environment's assignment fails (`SpawnPolicy.fallible`). -/
def groupConcurrentC (g : Ptr) (_ : Io) (t : Tgt) : CM Tgt σ (Except ErrName Unit) := do
  match ← StateT.lift (ConcM.sync (.spawn t)) with
  | .ok tid =>
    callMC (Thread.groupAdd g tid)
    pure (.ok ())
  | .error _ => pure (.error "ConcurrencyUnavailable")

/-- `Io.Group.await`: joins each task of the group, in the order of their spawn. -/
def groupAwaitC (g : Ptr) (_ : Io) : CM Tgt σ (Except ErrName Unit) := do
  let tids ← callMC (Thread.groupTake g)
  for tid in tids do joinC tid
  pure (.ok ())

/-- `Io.Group.cancel`: the model never cancels, so it waits for the tasks as `await` does. -/
def groupCancelC (g : Ptr) (io : Io) : CM Tgt σ Unit := do
  let _ ← groupAwaitC g io

/-! ### `std.Thread` (0.14.1, 0.15.2; `docs/std-models.md` §Thread model) -/

/-- The owner check (`Thread.mutexOwnerCheck`) that the translator puts at the start of the
translated `Thread.Mutex.FutexImpl.unlock` (`Air2Lean.ownerCheckedUnlocks`): the mutex word is at
offset 0 of `p`. -/
def mutexOwnerCheck (p : Ptr) : ConcM Tgt Unit := ConcM.liftMem (Thread.mutexOwnerCheck p)

/-- `Thread.Futex.wait(ptr, expect)`: the futex wait of the model (no `Io`). -/
def threadFutexWaitC (p : Ptr) (expected : BitVec 32) : CM Tgt σ Unit :=
  StateT.lift (discard (ConcM.sync (Tgt := Tgt) (.wait p expected)))

/-- `Thread.Futex.wake(ptr, max_waiters)`. -/
def threadFutexWakeC (p : Ptr) (n : BitVec 32) : CM Tgt σ Unit :=
  StateT.lift (discard (ConcM.sync (Tgt := Tgt) (.wake p n.toNat)))

/-- One try of `os_unfair_lock_lock` at the lock word `p`: an acquire `cmpxchg` 0 → 1; on a
failure, a futex wait while the word holds the value read. `true`: try again. -/
def osUnfairLockTry (p : Ptr) : CM Tgt σ Bool := do
  match ← cmpxchgC (n := 32) .acquire .relaxed 4 p 0 1 with
  | none => pure false
  | some v => threadFutexWaitC p v; pure true

/-- `os_unfair_lock_lock` (macOS; `Thread.Mutex.DarwinImpl.lock`): a C function, so the model is
the lock's contract, built from the model's ops: the word is 1 while a thread holds the lock;
the lock is an acquire, the unlock a release (the happens-before edge); a thread that waits
sleeps at the futex (so a deadlock is `.deadlock`). -/
def osUnfairLockC (p : Ptr) : CM Tgt σ Unit := do
  let _ ← loop (osUnfairLockTry p) id
  pure ()

/-- `os_unfair_lock_unlock`: the owner check (`Thread.mutexOwnerCheck`: an unlock by a thread
that does not hold the lock is `.illegal`, as the C function terminates the process), a release
`xchg` of 0 (the C function is a release `cmpxchg` of the owner to 0, an RMW), then a wake of one
waiter. -/
def osUnfairUnlockC (p : Ptr) : CM Tgt σ Unit := do
  callMC (Thread.mutexOwnerCheck p)
  let _ ← atomicRmwC .xchg false .release 4 p (0 : BitVec 32)
  threadFutexWakeC p 1

/-- `os_unfair_lock_trylock`: one acquire `cmpxchg` 0 → 1. -/
def osUnfairTryLockC (p : Ptr) : CM Tgt σ Bool := do
  return (← cmpxchgC (n := 32) .acquire .relaxed 4 p 0 1).isNone

section Monotone
open Lean.Order

theorem ConcM.monotone_liftMem {γ : Type} [PartialOrder γ] (f : γ → MemM α) (hmono : monotone f) :
    monotone (fun x => (ConcM.liftMem (f x) : ConcM Tgt α)) := by
  intro x₁ x₂ hx n m
  have h : (f x₁).run m ⊑ (f x₂).run m := hmono x₁ x₂ hx m
  show CoN.le (.leaf ((f x₁).run m)) (.leaf ((f x₂).run m))
  generalize (f x₁).run m = a at h ⊢
  generalize (f x₂).run m = b at h ⊢
  cases h with
  | bot => exact .bot _
  | refl => exact CoN.le_refl _

@[partial_fixpoint_monotone]
theorem monotone_callC {γ : Type} [PartialOrder γ] (f : γ → ConcM Tgt α) (hmono : monotone f) :
    monotone (fun (x : γ) => (callC (f x) : CM Tgt σ α)) := by
  apply monotone_of_monotone_apply
  intro s
  show monotone (fun x => (f x) >>= fun a => pure (a, s))
  exact monotone_bind _ _ _ hmono (monotone_const _)

@[partial_fixpoint_monotone]
theorem monotone_groupAsyncC {γ : Type} [PartialOrder γ] (g : Ptr) (io : Io) (t : Tgt)
    (f : γ → ConcM Tgt Unit) (hmono : monotone f) :
    monotone (fun x => (groupAsyncC g io t (f x) : CM Tgt σ Unit)) := by
  unfold groupAsyncC
  apply monotone_bind _ _ _ (monotone_const _)
  apply monotone_of_monotone_apply
  intro r
  cases r with
  | ok tid => exact monotone_const _
  | error e => exact monotone_callC f hmono

@[partial_fixpoint_monotone]
theorem monotone_callMC {γ : Type} [PartialOrder γ] (f : γ → MemM α) (hmono : monotone f) :
    monotone (fun (x : γ) => (callMC (f x) : CM Tgt σ α)) :=
  monotone_callC _ (ConcM.monotone_liftMem f hmono)

@[partial_fixpoint_monotone]
theorem monotone_callRC {γ : Type} [PartialOrder γ] (f : γ → Result α) (hmono : monotone f) :
    monotone (fun (x : γ) => (callRC (f x) : CM Tgt σ α)) := by
  apply monotone_callC _ (ConcM.monotone_liftMem _ _)
  apply monotone_of_monotone_apply
  intro m
  show monotone (fun x => (f x) >>= fun a => pure (a, m))
  exact monotone_bind _ _ _ hmono (monotone_const _)

@[partial_fixpoint_monotone]
theorem monotone_runCM' {γ : Type} [PartialOrder γ] (f : γ → CM Tgt σ α) (hmono : monotone f)
    (s : σ) : monotone (fun (x : γ) => (f x).run' s) := by
  have h := Functor.monotone_map (fun x => StateT.run (f x) s) (·.1) (monotone_stateTRun f hmono s)
  simpa [StateT.run', StateT.run] using h

@[partial_fixpoint_monotone]
theorem monotone_loopCM {ε γ : Type} [PartialOrder γ] (f : γ → CM Tgt σ ε) (again : ε → Bool)
    (hmono : monotone f) : monotone (fun (x : γ) => loop (f x) again) := by
  intro x1 x2 hx
  have hle : f x1 ⊑ f x2 := hmono x1 x2 hx
  apply loop.fixpoint_induct (f x1) again (motive := fun v => v ⊑ loop (f x2) again)
  · exact fun _ hc h => csup_le hc h
  · intro l hl
    rw [loop.eq_1 (f x2) again]
    apply PartialOrder.rel_trans (MonoBind.bind_mono_left hle)
    apply MonoBind.bind_mono_right
    intro e
    split
    · exact hl
    · exact PartialOrder.rel_refl

end Monotone

end Zig
