import ZigLean.Conc.Clock

/-!
# Ownership clocks across thread creation and join

These are memory-model facts about arbitrary heaps. They do not depend on a separation-logic
judgment or a protocol: fork copies the parent's clock after bumping it, and join merges the
child's clock into the parent's. The operations change neither blocks nor recorded accesses.
-/

namespace Zig

open Conc

/-- Changing neither the recorded accesses nor the number of blocks preserves ownership by
the same clock. -/
theorem Mem.OwnsC.congr {m m' : Mem} {c : VClock} {h : Heap} (ho : m.OwnsC c h)
    (hfp : m'.footprint = m.footprint) (hbs : m'.blocks.size = m.blocks.size) :
    m'.OwnsC c h := by
  intro e he ht
  rw [hfp] at he
  rw [hbs] at ht
  exact ho e he ht

/-- A fork makes no existing thread's clock smaller. -/
theorem Mem.Owns.fork {m m' : Mem} {t u c : ThreadId} {gt : Bool} {h : Heap}
    (ho : m.Owns u h) (hcs : m.clocks.size = m.threads.size) (hu : u < m.threads.size)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m'))) :
    m'.Owns u h := by
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  have hu' : u < m.clocks.size := hcs ▸ hu
  refine Mem.OwnsC.mono (c := m.clocks[u]!) ?_ ?_
  · exact ho.congr rfl rfl
  · rw [Proto.getElem!_push, if_pos (by simpa using hu'), Proto.getElem!_set!_ite]
    split
    · rename_i e; rw [e.1]; exact VClock.le_bump _ _
    · exact VClock.le_refl _

/-- The new thread inherits ownership from its parent's clock. -/
theorem Mem.Owns.fork_child {m m' : Mem} {t c : ThreadId} {gt : Bool} {h : Heap}
    (ho : m.Owns t h) (hcs : m.clocks.size = m.threads.size)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m'))) :
    m'.Owns c h := by
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  refine Mem.OwnsC.mono (c := m.clocks[t]!) ?_ ?_
  · exact ho.congr rfl rfl
  · rw [Proto.getElem!_push, if_neg (by simp [hcs]), if_pos (by simp [hcs])]
    exact VClock.le_bump _ _

/-- Join gives the parent ownership of both heaps. -/
theorem Mem.Owns.join {m m' : Mem} {t u : ThreadId} {h₁ h₂ : Heap}
    (h₁o : m.Owns t h₁) (h₂o : m.Owns u h₂) (ht : t < m.clocks.size)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m'))) :
    m'.Owns t (h₁ ∪ h₂) := by
  obtain ⟨rec, _, _, rfl⟩ := Proto.join_eq hj
  apply Mem.OwnsC.union
  · refine Mem.OwnsC.mono (c := m.clocks[t]!) ?_ ?_
    · exact h₁o.congr rfl rfl
    · rw [Proto.getElem!_set!_ite, if_pos ⟨rfl, ht⟩]
      exact VClock.le_trans (VClock.le_bump _ _) (VClock.le_merge_left _ _)
  · refine Mem.OwnsC.mono (c := m.clocks[u]!) ?_ ?_
    · exact h₂o.congr rfl rfl
    · rw [Proto.getElem!_set!_ite, if_pos ⟨rfl, ht⟩]
      exact VClock.le_merge_right _ _

/-- A join changes no other thread's clock. -/
theorem Mem.Owns.join_other {m m' : Mem} {t u w : ThreadId} {h : Heap}
    (ho : m.Owns w h) (hw : w ≠ t)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m'))) :
    m'.Owns w h := by
  obtain ⟨rec, _, _, rfl⟩ := Proto.join_eq hj
  change Mem.OwnsC _ _ _
  rw [Proto.getElem!_set!_ite, if_neg (by simp [hw])]
  exact ho.congr rfl rfl

end Zig
