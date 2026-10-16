import ZigLean.Conc.Clock

/-!
# The place of a thread in a lock's code, and the atomic locations around a word

Shared by the lock of the legacy thread logic (`ZigLean/Conc/Lock.lean`) and the lock over
full-state resources (`ZigLean/Sep/Full/LockWord.lean`, `ZigLean/Sep/Full/Lock.lean`): where a
thread is in a lock's code (`LPh`), clocks that happened before every or some thread (`AllLe`,
`SomeLe`), a change of the atomic locations that keeps every location at another address
(`LocsKeep`), and which threads were joined (`joinedB`).
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

/-- The atomic locations at other addresses than `(b, o)` stay (the same index, the same
location), and a new location is at `(b, o)`, with `k` bytes. -/
structure LocsKeep (b o k : Nat) (m m' : Mem) : Prop where
  new : ∀ l ∈ m'.atomics, l ∈ m.atomics ∨ (l.block = b ∧ l.off = o ∧ l.len = k)
  same : ∀ b' o', (b' ≠ b ∨ o' ≠ o) → ∀ i l,
    (m'.atomics.findIdx? (fun l => l.block == b' && l.off == o') = some i ∧ m'.atomics[i]? = some l) ↔
    (m.atomics.findIdx? (fun l => l.block == b' && l.off == o') = some i ∧ m.atomics[i]? = some l)

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

theorem LocsKeep.of_eq {b o k : Nat} {m m' : Mem} (h : m'.atomics = m.atomics) : LocsKeep b o k m m' :=
  ⟨fun l hl => .inl (h ▸ hl), fun _ _ _ _ _ => by rw [h]⟩

theorem LocsKeep.trans {b o k : Nat} {m₁ m₂ m₃ : Mem} (h₁ : LocsKeep b o k m₁ m₂)
    (h₂ : LocsKeep b o k m₂ m₃) : LocsKeep b o k m₁ m₃ :=
  ⟨fun l hl => (h₂.new l hl).elim (h₁.new l) .inr,
    fun b' o' hne i l => (h₂.same b' o' hne i l).trans (h₁.same b' o' hne i l)⟩

/-- A change of location `j` at `(b, o)` that keeps its address. -/
theorem LocsKeep.set {b o k j : Nat} {m m' : Mem} {l l' : ALoc} (hj : m.atomics[j]? = some l)
    (hb : l.block = b) (ho : l.off = o) (hb' : l'.block = b) (ho' : l'.off = o) (hl' : l'.len = k)
    (h : m'.atomics = m.atomics.set! j l') : LocsKeep b o k m m' := by
  have hjs := (Array.getElem?_eq_some_iff.mp hj).1
  refine ⟨fun x hx => ?_, fun b₁ o₁ hne i x => ?_⟩
  · rw [h, Array.set!_eq_setIfInBounds] at hx
    rcases Array.mem_or_eq_of_mem_set (w := hjs) (by simpa [Array.setIfInBounds, hjs] using hx)
      with hx | rfl
    · exact .inl hx
    · exact .inr ⟨hb', ho', hl'⟩
  · have hf : (m.atomics.set! j l').findIdx? (fun l => l.block == b₁ && l.off == o₁) =
        m.atomics.findIdx? (fun l => l.block == b₁ && l.off == o₁) := by
      refine findIdx?_congr (by simp) fun k h1 h2 => ?_
      by_cases e : j = k
      · subst e
        rw [Array.getElem?_eq_getElem hjs] at hj; cases hj
        simp [Array.set!_eq_setIfInBounds, hb', ho', hb, ho]
      · simp only [Array.set!_eq_setIfInBounds]
        rw [Array.getElem_setIfInBounds, if_neg e]
    rw [h, hf]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have hi := (Array.findIdx?_eq_some_iff_getElem.mp h1)
      obtain ⟨hik, hp, -⟩ := hi
      have hij : i ≠ j := fun e => by
        subst e
        rw [Array.getElem?_eq_getElem hik] at hj; cases hj
        simp [hb, ho] at hp; rcases hne with h | h <;> simp_all
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hij)] at h2
      exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      obtain ⟨hik, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp h1
      have hij : i ≠ j := fun e => by
        subst e
        rw [Array.getElem?_eq_getElem hik] at hj; cases hj
        simp [hb, ho] at hp; rcases hne with h | h <;> simp_all
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hij)]
      exact h2

/-- A new location at `(b, o)`. -/
theorem LocsKeep.push {b o k : Nat} {m m' : Mem} {l' : ALoc} (hb' : l'.block = b) (ho' : l'.off = o)
    (hl' : l'.len = k) (h : m'.atomics = m.atomics.push l') : LocsKeep b o k m m' := by
  refine ⟨fun x hx => ?_, fun b₁ o₁ hne i x => ?_⟩
  · rw [h] at hx
    rcases Array.mem_push.mp hx with hx | rfl
    · exact .inl hx
    · exact .inr ⟨hb', ho', hl'⟩
  · rw [h, Array.findIdx?_push]
    have hn : ¬ (l'.block == b₁ && l'.off == o₁) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq, hb', ho']
      rintro ⟨rfl, rfl⟩; rcases hne with h | h <;> exact h rfl
    cases hf : m.atomics.findIdx? (fun l => l.block == b₁ && l.off == o₁) with
    | some k =>
      have hk := (Array.findIdx?_eq_some_iff_getElem.mp hf).1
      simp only [Option.some_or]
      constructor
      · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; cases h1
        rw [Array.getElem?_push_lt hk] at h2; rw [Array.getElem?_eq_getElem hk]; exact h2
      · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; cases h1
        rw [Array.getElem?_push_lt hk, ← Array.getElem?_eq_getElem hk]; exact h2
    | none =>
      simp only [Option.none_or]
      rw [show (if (l'.block == b₁ && l'.off == o₁) = true then some m.atomics.size else none) = none
        from if_neg hn]
      simp

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
