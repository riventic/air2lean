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
