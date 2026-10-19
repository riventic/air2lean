import ZigLean.Conc.Base.Lock

/-!
# Legacy atomic-location transport

`LocsKeep` and its unchanged lemmas remain in this listed legacy module. Full-state lock
code still uses them; the open `conc-base-owned` ledger row records their replacement through
`FStepIn`/`RestStep`. Pure lock phases and clock/thread facts live in `Conc.Base.Lock`.
-/

namespace Zig
namespace Conc

/-- The atomic locations at other addresses than `(b, o)` stay (the same index, the same
location), and a new location is at `(b, o)`, with `k` bytes. -/
structure LocsKeep (b o k : Nat) (m m' : Mem) : Prop where
  new : ∀ l ∈ m'.atomics, l ∈ m.atomics ∨ (l.block = b ∧ l.off = o ∧ l.len = k)
  same : ∀ b' o', (b' ≠ b ∨ o' ≠ o) → ∀ i l,
    (m'.atomics.findIdx? (fun l => l.block == b' && l.off == o') = some i ∧ m'.atomics[i]? = some l) ↔
    (m.atomics.findIdx? (fun l => l.block == b' && l.off == o') = some i ∧ m.atomics[i]? = some l)

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

end Conc
end Zig
