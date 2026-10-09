import ZigLean.Os
import ZigLean.Conc.Sched
import ZigLean.Simp

/-!
# Rules of the OS futex, wake and interrupt models (premises OSF-01, OSF-02, OSG-01; proof-only)

Facts about `ZigLean/Os/Futex.lean` and `ZigLean/Os/Thread.lean` that client proofs (the planned
`FutexSpec`, `docs/thread-io-translation.md` §4.1) use, and kernel-checked runs of the scheduler:

* a wake's options are exactly the subsets of `min n k` of the `k` threads queued at the address,
  there is always one (`wakeCount_pos`), and every thread it wakes was queued there
  (`wakeSets_mem`);
* a wake and an interrupt touch only the wait queue and the interrupt set: no clock, footprint,
  block or atomic location changes, so they give no happens-before edge (`wakeAt_frame`,
  `interrupt_frame`);
* the kernel's compare has one option unless the word is the expected value, then two (or three
  with a timeout) (`waitCount_ne`, `waitCount_eq`);
* kernel-checked schedules: a spurious `EINTR` with nobody waking; a timed wait that returns with
  nobody waking; a wake that gives no edge (the waiter's plain read races); the Linux join loop
  over `CHILD_CLEARTID` that does give the edge.

Not imported by `ZigLean.lean`: `lake build ZigLean.Conc.OsRules`.
-/

namespace Zig
namespace Os

/-! ## Wake subsets -/

theorem sublistsLen_length {α : Type} :
    ∀ (k : Nat) (xs ys : List α), ys ∈ sublistsLen k xs → ys.length = k
  | 0, _, ys, h => by simp [sublistsLen] at h; simp [h]
  | _ + 1, [], _, h => by simp [sublistsLen] at h
  | k + 1, _ :: xs, ys, h => by
    simp only [sublistsLen, List.mem_append, List.mem_map] at h
    rcases h with ⟨zs, hz, rfl⟩ | h
    · simp [sublistsLen_length k xs zs hz]
    · exact sublistsLen_length (k + 1) xs ys h

theorem sublistsLen_sublist {α : Type} :
    ∀ (k : Nat) (xs ys : List α), ys ∈ sublistsLen k xs → ys.Sublist xs
  | 0, _, ys, h => by simp [sublistsLen] at h; simp [h]
  | _ + 1, [], _, h => by simp [sublistsLen] at h
  | k + 1, x :: xs, ys, h => by
    simp only [sublistsLen, List.mem_append, List.mem_map] at h
    rcases h with ⟨zs, hz, rfl⟩ | h
    · exact (sublistsLen_sublist k xs zs hz).cons_cons x
    · exact (sublistsLen_sublist (k + 1) xs ys h).cons x

theorem sublistsLen_ne_nil {α : Type} :
    ∀ (k : Nat) (xs : List α), k ≤ xs.length → sublistsLen k xs ≠ []
  | 0, _, _ => by simp [sublistsLen]
  | _ + 1, [], h => by simp at h
  | k + 1, _ :: xs, h => by
    simp only [List.length_cons] at h
    simp only [sublistsLen, ne_eq, List.append_eq_nil_iff, List.map_eq_nil_iff, not_and]
    intro hk
    exact absurd hk (sublistsLen_ne_nil k xs (by omega))

/-- The number of threads a wake of up to `n` (`none`: all) wakes among `k` queued ones. -/
def wakeSize (n : Option Nat) (k : Nat) : Nat := (n.map (Nat.min · k)).getD k

theorem wakeSize_le (n : Option Nat) (k : Nat) : wakeSize n k ≤ k := by
  cases n <;> simp [wakeSize, Nat.min_le_right]

/-- A wake always has an option. -/
theorem wakeCount_pos (p : Ptr) (n : Option Nat) (m : Mem) : 0 < wakeCount p n m := by
  unfold wakeCount wakeSets
  exact List.length_pos_iff.mpr (sublistsLen_ne_nil _ _ (wakeSize_le n _))

/-- Every option of a wake is a set of `wakeSize n k` threads queued at `p`, in queue order. -/
theorem wakeSets_mem {m : Mem} {p : Ptr} {n : Option Nat} {ts : List ThreadId}
    (h : ts ∈ wakeSets m p n) :
    ts.Sublist (m.waitersAt p) ∧ ts.length = wakeSize n (m.waitersAt p).length :=
  ⟨sublistsLen_sublist _ _ _ h, sublistsLen_length _ _ _ h⟩

/-- A wake changes only the queue: the memory, the clocks, the footprint, the atomic locations
and the threads are as before. No happens-before edge. -/
theorem wakeAt_frame {c : Nat} {p : Ptr} {n : Option Nat} {m m' : Mem} {k : Option Nat}
    (h : ((wakeAt c p n).run m).run = some (.ok (k, m'))) :
    m'.blocks = m.blocks ∧ m'.clocks = m.clocks ∧ m'.footprint = m.footprint ∧
      m'.atomics = m.atomics ∧ m'.threads = m.threads := by
  unfold wakeAt at h
  cases hs : (wakeSets m p n)[c]? with
  | none =>
    simp [wakeThreads, zig_unfold, ExceptT.run, hs] at h
    obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some ts =>
    simp [wakeThreads, zig_unfold, ExceptT.run, hs] at h
    obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- An interrupt changes only the queue and the interrupt set (OSG-01). -/
theorem interrupt_frame {t : ThreadId} {m m' : Mem}
    (h : ((interrupt t).run m).run = some (.ok ((), m'))) :
    m'.blocks = m.blocks ∧ m'.clocks = m.clocks ∧ m'.footprint = m.footprint ∧
      m'.atomics = m.atomics ∧ m'.threads = m.threads := by
  simp only [interrupt, zig_unfold, ExceptT.run] at h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The kernel's compare -/

theorem waitCount_ne {p : Ptr} {e v : BitVec 32} {timed : Bool} {m m' : Mem}
    (h : ((futexWord p).run m).run = some (.ok (v, m'))) (hne : v ≠ e) :
    waitCount p e timed m = 1 := by
  simp [waitCount, h, hne]

theorem waitCount_eq {p : Ptr} {e : BitVec 32} {timed : Bool} {m m' : Mem}
    (h : ((futexWord p).run m).run = some (.ok (e, m'))) :
    waitCount p e timed m = if timed then 3 else 2 := by
  simp [waitCount, h]

/-! ## Kernel-checked schedules (x86_64-linux) -/

namespace OsRulesExamples

/-- A run's result, without the memory. -/
def result {α : Type} (dispatch : Nat → ConcM Nat Unit) (fuel : Nat) (o : List Nat)
    (main : ConcM Nat α) : Option (Except Error α) :=
  ((Sched.run dispatch fuel (o.getD · 0) main {}).run).map (·.map (·.1))

def noKids : Nat → ConcM Nat Unit := fun _ => pure ()

def word (v : BitVec 32) : ConcM Nat Ptr := ConcM.liftMem do
  let p ← alloc .heap 4 4
  store 4 p v
  pure p

/-- A futex wait that nobody wakes can still return: spurious `EINTR` (OSF-01). -/
example : result noKids 5 [0, 1] (do let p ← word 0; Linux.futex_4arg p 0x80 0 none) =
    some (.ok (negErrno Linux.E.INTR)) := by decide +kernel

/-- ... or sleep forever: the run deadlocks. -/
example : result noKids 5 [0, 0] (do let p ← word 0; Linux.futex_4arg p 0x80 0 none) =
    some (.error .deadlock) := by decide +kernel

/-- A timed wait that sleeps stays runnable and times out: no deadlock. -/
example : result noKids 6 [0, 0] (do
    let p ← word 0
    let ts ← ConcM.liftMem do
      let t ← alloc .heap 16 8
      store 8 t (0 : BitVec 64)
      store 8 (t.add 8) (1000 : BitVec 64)
      pure t
    Linux.futex_4arg p 0 0 (some ts)) = some (.ok (negErrno Linux.E.TIMEDOUT)) := by decide +kernel

def p0 : Ptr := ⟨some 0, 0⟩
def d1 : Ptr := ⟨some 1, 0⟩

/-- A waiter that reads, after its wait, the data at `d1`. -/
def readerKid : Nat → ConcM Nat Unit := fun _ => do
  let _ ← Linux.futex_4arg p0 0x80 0 none
  let _ ← ConcM.liftMem (load (BitVec 64) 8 d1)

/-- The waker writes `d1`, then wakes the waiter: a wake is no synchronization. -/
def wakerMain : ConcM Nat Unit := do
  let _ ← word 0
  let _ ← ConcM.liftMem (do let d ← alloc .heap 8 8; store 8 d (0 : BitVec 64))
  let t : ThreadId ← ConcM.sync (.spawn 0)
  ConcM.liftMem (store 8 d1 (5 : BitVec 64))
  let _ ← Linux.futex_3arg p0 0x81 1
  ConcM.sync (.join t)

/-- A wake gives no happens-before edge (OSF-02): a schedule where the woken waiter's plain read
of the waker's earlier plain write is a data race. -/
example : result readerKid 12 [0, 0, 0, 0, 0, 1] wakerMain = some (.error .illegal) := by
  decide +kernel

/-- A `clone` thread that writes `d1`; its exit clears the `i32` at `p0` (`CHILD_CLEARTID`). -/
def cloneKid : Nat → ConcM Nat Unit := fun _ =>
  Linux.cloneThread (ConcM.liftMem (store 8 d1 (42 : BitVec 64))) p0

/-- `LinuxThreadImpl.join`: a `seq_cst` load of `child_tid` until it is 0, with a futex wait. -/
def joinLoop : Nat → ConcM Nat Unit
  | 0 => throw .panic
  | k + 1 => do
    let c ← pick (loadCount 32 .seqCst 4 p0)
    let tid : BitVec 32 ← ConcM.liftMem (atomicLoadAt c .seqCst 4 p0)
    if tid = 0 then return
    let _ ← Linux.futex_4arg p0 0 tid none
    joinLoop k

def cloneMain : ConcM Nat (BitVec 64) := do
  let _ ← word 1
  let _ ← ConcM.liftMem (do let d ← alloc .heap 8 8; store 8 d (0 : BitVec 64))
  let pt ← ConcM.liftMem (alloc .heap 4 4)
  let _ ← Linux.clone Env.example 0 0 Linux.stdCloneFlags (some pt) 0 (some p0)
  joinLoop 3
  ConcM.liftMem (load (BitVec 64) 8 d1)

/-- The join loop gets the edge from the exit's release store (OST-01/02): the parent reads the
thread's plain write without a race. (Every schedule: `tests/roadmap/os-threads/Check.lean`.) -/
example : result cloneKid 20 [] cloneMain = some (.ok 42) := by decide +kernel

end OsRulesExamples

end Os
end Zig
