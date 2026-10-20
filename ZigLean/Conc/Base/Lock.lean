import ZigLean.Conc.Clock

/-!
# Lock phases and clock/thread facts

Pure vocabulary shared by the retiring lock rules and the full-state logic: a thread's place
in lock code (`LPh`), clocks that happened before every or some thread (`AllLe`, `SomeLe`),
array lookup facts, and thread fork/join bookkeeping. The legacy atomic-location transport
relation remains in `ZigLean.Conc.LockBase` until its `FStepIn`/`RestStep` retirement.
-/

namespace Zig
namespace Conc

/-- Where a thread is in the code of a lock (`Io.Mutex`). -/
inductive LPh where
  /-- The thread has not started, or it has ended. -/
  | gone
  /-- Not in the lock's code, or at `lock`'s first try (`cmpxchg`). -/
  | out
  /-- In `lock`'s loop, before its `xchg`. -/
  | spin
  /-- At a futex wait of `lock`. -/
  | wait
  /-- It holds the lock. -/
  | holds
  /-- At the futex wake of `unlock`. -/
  | wake
  /-- Out of the lock's code, at the futex wait of another sync object: it can sleep there. -/
  | away
  deriving DecidableEq

/-- In the lock's code, after `lock`'s first try: the thread will take the lock or wake a
waiter. -/
def LPh.busy : LPh → Bool
  | .spin | .wait | .holds | .wake => true
  | _ => false

/-- The clock `c` happened before every thread. -/
def AllLe (m : Mem) (c : VClock) : Prop :=
  ∀ u < m.threads.size, VClock.le c (m.clocks[u]!) = true

/-- The clock `c` happened before a thread. -/
def SomeLe (m : Mem) (c : VClock) : Prop :=
  ∃ u < m.threads.size, VClock.le c (m.clocks[u]!) = true

/-- `findIdx?` with a predicate that has the same value at each index. -/
theorem findIdx?_congr {α : Type} {xs ys : Array α} {p : α → Bool} (hs : ys.size = xs.size)
    (h : ∀ k (h1 : k < ys.size) (h2 : k < xs.size), p ys[k] = p xs[k]) :
    ys.findIdx? p = xs.findIdx? p := by
  cases hf : xs.findIdx? p with
  | some i =>
    obtain ⟨hi, hp, hj⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
    exact Array.findIdx?_eq_some_iff_getElem.mpr ⟨by omega, by rw [h i (by omega) hi]; exact hp,
      fun j hji => by rw [h j (by omega) (by omega)]; exact hj j hji⟩
  | none =>
    have hn := Array.findIdx?_eq_none_iff.mp hf
    refine Array.findIdx?_eq_none_iff.mpr fun y hy => ?_
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hy
    rw [h k hk (by omega)]; exact hn _ (Array.getElem_mem _)

/-- Replacing an atomic record while retaining its address preserves every
address-search result. This does not assert that its message record is unchanged. -/
theorem findIdx?_set_address {xs : Array ALoc} {j : Nat} {old new : ALoc}
    (hj : xs[j]? = some old) (hb : new.block = old.block) (ho : new.off = old.off)
    (b o : Nat) :
    (xs.set! j new).findIdx? (fun l => l.block == b && l.off == o) =
      xs.findIdx? (fun l => l.block == b && l.off == o) := by
  have hjs : j < xs.size := (Array.getElem?_eq_some_iff.mp hj).1
  refine findIdx?_congr (by simp) fun k h1 h2 => ?_
  by_cases he : j = k
  · subst k
    rw [Array.getElem?_eq_getElem hjs] at hj
    cases hj
    simp [Array.set!_eq_setIfInBounds, hb, ho]
  · simp only [Array.set!_eq_setIfInBounds]
    rw [Array.getElem_setIfInBounds, if_neg he]

/-- Appending preserves an existing first match and the complete record at its
original index, regardless of the appended record's address. -/
theorem first_push {α : Type} {xs : Array α} {p : α → Bool} {i : Nat} {old : α}
    (hf : xs.findIdx? p = some i) (hi : xs[i]? = some old) (new : α) :
    (xs.push new).findIdx? p = some i ∧ (xs.push new)[i]? = some old := by
  have hlt : i < xs.size := (Array.getElem?_eq_some_iff.mp hi).1
  refine ⟨?_, ?_⟩
  · rw [Array.findIdx?_push, hf]
    rfl
  · rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt]
    exact hi

/-- An address-preserving set at another address preserves the complete first
record at the same index. No location length or global layout premise is needed. -/
theorem first_set_address_ne {xs : Array ALoc} {j i : Nat} {old new saved : ALoc}
    {b o : Nat} (hj : xs[j]? = some old)
    (hb : new.block = old.block) (ho : new.off = old.off)
    (hne : old.block ≠ b ∨ old.off ≠ o)
    (hf : xs.findIdx? (fun l => l.block == b && l.off == o) = some i)
    (hi : xs[i]? = some saved) :
    (xs.set! j new).findIdx? (fun l => l.block == b && l.off == o) = some i ∧
      (xs.set! j new)[i]? = some saved := by
  have hji : j ≠ i := by
    intro he
    subst j
    have heq : old = saved := Option.some.inj (hj.symm.trans hi)
    obtain ⟨hit, hp, _⟩ := Array.findIdx?_eq_some_iff_getElem.mp hf
    rw [(Array.getElem?_eq_some_iff.mp hi).2] at hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    rw [heq] at hne
    rcases hne with hn | hn
    · exact hn hp.1
    · exact hn hp.2
  refine ⟨(findIdx?_set_address hj hb ho b o).trans hf, ?_⟩
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hji]
  exact hi

/-! ## Threads: joined, forked -/

/-- Thread `u` was joined (`main` never is). -/
def joinedB (m : Mem) (u : ThreadId) : Bool :=
  u != 0 && ((m.threads[u]?).map (·.joined)).getD false

theorem joinedB_fork {m m' : Mem} {t c : ThreadId} {gt : Bool}
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m'))) :
    joinedB m' = joinedB m := by
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨-, rfl⟩ := hf
  funext u
  unfold joinedB
  simp only [Array.getElem?_push]
  split
  · rename_i h; subst h; simp
  · rfl

/-- A fork or deferred fork keeps the spawning thread current. -/
theorem fork_current {m m' : Mem} {t c : ThreadId} {gt : Bool}
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m'))) :
    m'.current = t := by
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  exact (congrArg Mem.current hf.2).symm

theorem fork_threads {m m' : Mem} {t c : ThreadId} {gt : Bool}
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m'))) :
    c = m.threads.size ∧ m'.threads = m.threads.push { spawner := t, joined := false, gated := gt } := by
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  exact ⟨rfl, rfl⟩

theorem join_threads {m m' : Mem} {t u : ThreadId} {rec : ThreadRec}
    (hr : m.threads[u]? = some rec)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m'))) :
    m'.current = t ∧ m'.threads = m.threads.setIfInBounds u { rec with joined := true } := by
  obtain ⟨rec', hr', -, rfl⟩ := Proto.join_eq hj
  simp only at hr'
  rw [hr] at hr'; cases hr'
  exact ⟨rfl, Array.set!_eq_setIfInBounds⟩

theorem upd_comm {β : Type} (f : ThreadId → β) {t u : ThreadId} (x y : β) (h : t ≠ u) :
    upd (upd f t x) u y = upd (upd f u y) t x := by
  funext w; unfold upd; by_cases h1 : w = t <;> by_cases h2 : w = u <;> simp_all

end Conc
end Zig
