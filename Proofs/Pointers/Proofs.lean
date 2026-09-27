import Proofs.Pointers.Gen
import ZigLean.Mem.Lemmas
import ZigLean.Simp

/-!
# Proofs about `examples/pointers/pointers.zig`

`swap` exchanges two `u32` values that do not overlap, and `swap(p, p)` keeps the value.
`dueOf` returns a pointer into its argument, and `same` compares block and offset.
-/

open Pointers Zig

/-- `swap` as its four memory operations. -/
theorem swap_run {m m₁ m₂ : Mem} {p q : Ptr} {x y : BitVec 32}
    (hx : (load (BitVec 32) 4 p).run m = pure (x, m))
    (hy : (load (BitVec 32) 4 q).run m = pure (y, m))
    (h₁ : (store 4 p y).run m = pure ((), m₁))
    (h₂ : (store 4 q x).run m₁ = pure ((), m₂)) :
    (swap p q).run m = pure ((), m₂) := by
  simp only [StateT.run] at hx hy h₁ h₂
  simp only [swap, StateT.run', zig_unfold, hx, hy, h₁, h₂]

/-- `swap` exchanges two `u32` values whose bytes do not overlap. If `p = q`, the value stays. -/
theorem swap_spec (m : Mem) (p q : Ptr) (x y : BitVec 32)
    (hx : (load (BitVec 32) 4 p).run m = pure (x, m))
    (hy : (load (BitVec 32) 4 q).run m = pure (y, m))
    (hd : p = q ∨ p.block ≠ q.block ∨ p.off + 4 ≤ q.off ∨ q.off + 4 ≤ p.off) :
    ∃ m', (swap p q).run m = pure ((), m') ∧
      (load (BitVec 32) 4 p).run m' = pure (y, m') ∧ (load (BitVec 32) 4 q).run m' = pure (x, m') := by
  rcases hd with rfl | hd
  · -- One pointer: both loads read the same value.
    have hxy : x = y := by
      have h : (some (.ok (x, m)) : Option (Except Error (BitVec 32 × Mem))) = some (.ok (y, m)) :=
        hx.symm.trans hy
      injection h with h; injection h with h; injection h
    subst hxy
    have h₁ := load_writeAt_same hx x
    exact ⟨_, swap_run hx hx (store_run' hx x) (store_run' h₁ x),
      load_writeAt_same h₁ x, load_writeAt_same h₁ x⟩
  · have hd' : q.block ≠ p.block ∨ q.off + 4 ≤ p.off ∨ p.off + 4 ≤ q.off := by
      rcases hd with h | h | h
      · exact Or.inl (Ne.symm h)
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    -- m₁: after `a.* = b.*`.
    have hp₁ := load_writeAt_same hx y
    have hq₁ := load_writeAt_other hx hy hd y
    exact ⟨_, swap_run hx hy (store_run' hx y) (store_run' hq₁ x),
      load_writeAt_other hq₁ hp₁ hd' x, load_writeAt_same hq₁ x⟩

/-- `&j.due`: the offset of `due` in `Job` is 4 (the compiler's layout). -/
theorem dueOf_spec (j : Ptr) (m : Mem) : (dueOf j).run m = pure (j.add 4, m) := by
  simp [dueOf, zig_unfold]

/-- Pointer equality is equality of block and offset. -/
theorem same_spec (p q : Ptr) (m : Mem) : (same p q).run m = pure (decide (p = q), m) := by
  simp [same, zig_unfold]
  rfl

theorem maxPtr_none_left (b : Option Ptr) (m : Mem) : (maxPtr none b).run m = pure (b, m) := by
  simp [maxPtr, zig_unfold]

theorem maxPtr_none_right (p : Ptr) (m : Mem) : (maxPtr (some p) none).run m = pure (some p, m) := by
  simp [maxPtr, zig_unfold, Zig.optPayload]

/-- Two pointers: the one to the larger value; `p` if the values are equal. -/
theorem maxPtr_spec (p q : Ptr) (m : Mem) (x y : BitVec 32)
    (hx : (load (BitVec 32) 4 p).run m = pure (x, m))
    (hy : (load (BitVec 32) 4 q).run m = pure (y, m)) :
    (maxPtr (some p) (some q)).run m = pure (some (if y.toNat ≤ x.toNat then p else q), m) := by
  simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hx hy
  by_cases h : y.toNat ≤ x.toNat <;>
    simp [maxPtr, zig_unfold, Zig.optPayload, hx, hy, h, Zig.ge, Zig.le, BitVec.ule]

/-- `delay` adds `d` to the job's `duration` (at offset 0). -/
theorem delay_spec (j : Ptr) (m : Mem) (x d : BitVec 32)
    (hx : (load (BitVec 32) 4 (j.add 0)).run m = pure (x, m)) (h : x.toNat + d.toNat < 2 ^ 32) :
    ∃ m', (delay j d).run m = pure ((), m') ∧
      (load (BitVec 32) 4 (j.add 0)).run m' = pure (x + d, m') := by
  have hs := store_run' hx (x + d)
  refine ⟨_, ?_, load_writeAt_same hx (x + d)⟩
  simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hx hs
  have hno : ¬ 2 ^ 32 ≤ x.toNat + d.toNat := by omega
  simp [delay, zig_unfold, hx, hs, Zig.add, BitVec.uaddOverflow, hno]

/-- A sum that does not fit in `u32` is the safety panic `integerOverflow`. -/
theorem delay_overflow (j : Ptr) (m : Mem) (x d : BitVec 32)
    (hx : (load (BitVec 32) 4 (j.add 0)).run m = pure (x, m)) (h : 2 ^ 32 ≤ x.toNat + d.toNat) :
    (delay j d).run m = throw .overflow := by
  simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hx
  simp [delay, zig_unfold, hx, Zig.add, BitVec.uaddOverflow, h]
