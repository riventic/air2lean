import Proofs.Threadsync.Deadline
import ZigLean.Sep.Full.Event
import ZigLean.Conc.Unroll

/-!
# Why `EventImpl.set` must order memory (`ZigLean/Sep/Full/Event.lean`, **Setters**)

Two sets that are wrong for a client, run in 0.15.2's `threadsync.waitGroup` (its tasks' last
`finish` sets the event after its `fetchSub`; `main` waits and then reads the whole `Tally`,
whose bytes 8..12 are the event's word):

* `futexSetR`: `Thread.ResetEvent.FutexImpl.set` with its `xchg(is_set)` relaxed instead of
  release. Nothing orders the tasks' counter stores before `main`'s read: `relaxedSet_races`.
  The same copies of `finish` and `task` with the generated set are the generated code
  (`dispatchW_gen`), which completes (`Threadsync.WG.waitGroup_completes`), so the order is the
  only difference.
* `set2`: a set that writes `is_set` twice (two release `xchg`s, each followed by a wake if it
  read `waiting`). `main` synchronizes with the first and reads the `Tally` while the second is
  pending: `doubleSet_races`. One such write (`setX`) completes: `oneSet_completes`.

Both met the earlier `EventImpl.set_wp` statement (kernel-checked against the event library of
96e635910): its `FEvent.wp_xchg` took any order, and admitted a setter back at `out` after its
write, so the proof of `ResetEvent.futexSet_wp` went through for `futexSetR` verbatim and two
`setX` steps composed. The contract now excludes both (`FEvent.Next`):
* each `is_set` write of the event's code is a release RMW of the newest write by a setter from
  `out` (`next_isSet`), so `futexSetR`'s relaxed write is no step of the event's code;
* a setter at `sd`, where `set_wp` returns it after its write, writes nothing (`next_sd`). Only
  the protocol's own ghost step moves it back to `out`, and `set_wp` is proved for every
  protocol, so one `set` cannot write twice.

The runs use the oracle that always picks option 0.
-/

open Zig

namespace Threadsync.EventSet

/-- 0.15.2's `Thread.ResetEvent.FutexImpl.set` with a relaxed `xchg(is_set)`. -/
def futexSetR (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    match ← ((do
      let i2 ← pure p0
      let i3 ← pure (i2)
      match ← ((do
        let i5 ← pure i3
        let i6 ← Zig.atomicLoadC (n := 32) Zig.AtomicOrder.relaxed 4 i5
        pure (.br4 i6)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit) with
      | .br4 v4 => (do
        let i8 ← pure (v4 == (2 : BitVec 32))
        if i8 then (do
          pure .ret)
        else (do
          pure .br1))
      | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit) with
    | .br1 => (do
      match ← ((do
        let i13 ← pure p0
        match ← ((do
          let i15 ← pure i13
          let i16 ← Zig.atomicRmwC Zig.RmwOp.xchg false Zig.AtomicOrder.relaxed 4 i15 (2 : BitVec 32)
          pure (.br14 i16)) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit) with
        | .br14 v14 => (do
          let i18 ← pure (v14 == (1 : BitVec 32))
          if i18 then (do
            let i20 ← pure p0
            let i21 ← pure (i20)
            let _i22 ← Zig.threadFutexWakeC i21 (4294967295 : BitVec 32)
            pure .br12)
          else (do
            pure .br12))
        | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit) with
      | .br12 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_ResetEvent_FutexImpl_setLocals Thread_ResetEvent_FutexImpl_setExit).run' (default : Thread_ResetEvent_FutexImpl_setLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

/-- A release `xchg(is_set)`, then a wake of every waiter if it read `waiting`. -/
def setX (p : Zig.Ptr) : Zig.ConcM Tgt Unit := do
  let r ← (Zig.atomicRmwC Zig.RmwOp.xchg false Zig.AtomicOrder.release 4 p (2 : BitVec 32) :
    Zig.CM Tgt Unit (BitVec 32)).run ()
  if r.1 == (1 : BitVec 32) then do
    let _ ← (Zig.threadFutexWakeC p (4294967295 : BitVec 32) : Zig.CM Tgt Unit Unit).run ()
    pure ()
  else pure ()

/-- A set that writes `is_set` twice. -/
def set2 (p : Zig.Ptr) : Zig.ConcM Tgt Unit := do
  setX p
  setX p

/-- 0.15.2's `WaitGroup.finish` with the set `sf`. -/
def finishW (sf : Zig.Ptr → Zig.ConcM Tgt Unit) (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← pure p0
    match ← ((do
      let i3 ← pure i1
      let i4 ← Zig.atomicRmwC Zig.RmwOp.sub false Zig.AtomicOrder.acqRel 8 i3 (2 : BitVec 64)
      pure (.br2 i4)) : Zig.CM Tgt Thread_WaitGroup_finishLocals Thread_WaitGroup_finishExit) with
    | .br2 v2 => (do
      let i6 ← Zig.divTrunc false v2 (2 : BitVec 64)
      let i7 ← pure (i6)
      let i8 ← pure (Zig.gt false i7 (0 : BitVec 64))
      let _i9 ← Zig.callRC (debug_assert i8)
      match ← ((do
        let i11 ← pure (v2)
        let i12 ← pure (i11 == (3 : BitVec 64))
        if i12 then (do
          let i14 ← Zig.callMC (Zig.ptrProject p0 (·.add 8))
          let _i15 ← Zig.callC (sf i14)
          pure .br10)
        else (do
          pure .br10)) : Zig.CM Tgt Thread_WaitGroup_finishLocals Thread_WaitGroup_finishExit) with
      | .br10 => (do
        pure .ret)
      | e => pure e)
    | e => pure e) : Zig.CM Tgt Thread_WaitGroup_finishLocals Thread_WaitGroup_finishExit).run' (default : Thread_WaitGroup_finishLocals)
  match e with
  | .ret => pure ()
  | _ => throw .panic

/-- The fixture's `task` with the set `sf`. -/
def taskW (sf : Zig.Ptr → Zig.ConcM Tgt Unit) (p0 : Zig.Ptr) : Zig.ConcM Tgt (Unit) := do
  let e ← ((do
    let i1 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
    let _i2 ← Zig.callC (Thread_Mutex_lock i1)
    let i3 ← Zig.callMC (Zig.ptrProject p0 (·.add 20))
    let i4 ← Zig.load (BitVec 32) 4 i3
    let i5 ← Zig.add false i4 (1 : BitVec 32)
    Zig.store (α := BitVec 32) 4 i3 i5
    let i7 ← Zig.callMC (Zig.ptrProject p0 (·.add 16))
    let _i8 ← Zig.callC (Thread_Mutex_unlock i7)
    let i9 ← pure p0
    let _i10 ← Zig.callC (finishW sf i9)
    pure .ret) : Zig.CM Tgt taskLocals taskExit).run' (default : taskLocals)
  match e with
  | .ret => pure ()

def dispatchW (sf : Zig.Ptr → Zig.ConcM Tgt Unit) : Tgt → Zig.ConcM Tgt Unit
  | .producer a => discard (producer a)
  | .work a => discard (work a)
  | .task a => discard (taskW sf a)

/-- **The relaxed set races**: `main`'s whole-`Tally` read after its wait is not ordered after
the tasks' counter stores. -/
theorem relaxedSet_races :
    Witness.errOf (Sched.run ⟨.any, .available⟩ (dispatchW futexSetR) 1000 (fun _ => 0)
      (@waitGroup ⟨Os.Env.example⟩) (mem0 .fresh)) = some .illegal := by
  unroll_sched 10

/-- **The double set races**: `main` reads the `Tally` while the second write is pending. -/
theorem doubleSet_races :
    Witness.errOf (Sched.run ⟨.any, .available⟩ (dispatchW set2) 1000 (fun _ => 0)
      (@waitGroup ⟨Os.Env.example⟩) (mem0 .fresh)) = some .illegal := by
  unroll_sched 10

/-- Control for `futexSetR`: the copies of `finish` and `task` with the generated set are the
generated `dispatch`, which completes with 2 under the same schedule
(`Threadsync.WG.waitGroup_completes`). -/
theorem dispatchW_gen : dispatchW Thread_ResetEvent_set = dispatch := by
  funext x; cases x <;> rfl

/-- Control for `set2`: one release write and its wake completes with 2; the race of `set2` is
its second write. -/
theorem oneSet_completes :
    Witness.okVal (Sched.run ⟨.any, .available⟩ (dispatchW setX) 1000 (fun _ => 0)
      (@waitGroup ⟨Os.Env.example⟩) (mem0 .fresh)) = some 2 := by
  unroll_sched 10

open Zig.Conc Zig.Full

variable {γ : Type} (E : FEvent γ) {t : ThreadId} {g : γ} {p : EPh} {m m' : Mem}

/-- **The contract excludes the relaxed set**: an `is_set` write of a step of the event's code
is a release RMW of the newest write by a setter from `out`, so its release clock covers its
writer's clock. -/
theorem next_isSet (h : E.Next t g p m m') (hsz : (E.W.hist m').size = (E.W.hist m).size + 1)
    (hv : (E.W.hist m')[(E.W.hist m).size]!.Val (2 : BitVec 32)) :
    E.sx g ∧ E.ph g = .out ∧ ∃ ord : AtomicOrder, ord.isRel = true ∧
      (E.W.hist m')[(E.W.hist m).size]! = Word.rmwEnt m' t ord (E.newest m) (2 : BitVec 32) ∧
      VClock.le (E.W.hist m')[(E.W.hist m).size]!.clock
        (E.W.hist m')[(E.W.hist m).size]!.relClock = true := by
  rcases h with ⟨hh, -⟩ | ⟨ord, v, hh, ⟨rfl, -⟩ | ⟨rfl, hsx, hrel, hph, -⟩⟩
  · rw [hh] at hsz; omega
  · rw [hh, FEvent.get_push_eq] at hv
    exact absurd (FEvent.val_eq FEvent.rmwEnt_val hv) (by decide)
  · rw [hh, FEvent.get_push_eq]; exact ⟨hsx, hph, ord, hrel, rfl, Word.rmwEnt_rel hrel⟩

/-- **The contract excludes the double set**: a setter at `sd`, where `EventImpl.set_wp`
returns it, writes nothing and stays at `sd`. -/
theorem next_sd (hg : E.ph g = .sd) (h : E.Next t g p m m') :
    E.W.hist m' = E.W.hist m ∧ p = .sd := by
  rcases h with ⟨hh, hn⟩ | ⟨_, _, _, ⟨-, -, hph, -⟩ | ⟨-, -, -, hph, -⟩⟩
  · rw [hg] at hn; exact ⟨hh, hn⟩
  · rw [hg] at hph; cases hph
  · rw [hg] at hph; cases hph

end Threadsync.EventSet
