import Gen

/-! Clients of the retained compiler-generated bitset fixtures (`firstSet`, `clearLowest`,
`cardinality` from `bitops.zig`); no generated body is replaced. The gate compiles the fresh
`Gen.lean` to an olean beside this file; the tracked `qualified/0.16.0/Gen.lean` satisfies
the same statements. Kernel-checked; no `native_decide`, project axiom or placeholder. -/

namespace BitopsGenerated

/-- `cardinality` returns the exact population count, at most the word width. -/
theorem cardinality_spec (x : BitVec 64) :
    ∃ r, Bitops.cardinality x = pure r ∧ r.toNat = x.cpop.toNat ∧ r.toNat ≤ 64 := by
  have hc : (Zig.popcount 7 x).toNat = x.cpop.toNat := Zig.popcount_toNat_of_width x (by decide)
  have hle : (Zig.popcount 7 x).toNat ≤ 64 := Zig.popcount_le 7 x (by decide)
  have hr : ((Zig.popcount 7 x).setWidth 32).toNat = (Zig.popcount 7 x).toNat := by
    simp only [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨(Zig.popcount 7 x).setWidth 32, by simp [Bitops.cardinality], by rw [hr, hc], by rw [hr]; exact hle⟩

/-- The empty set reports the 64 sentinel. -/
theorem firstSet_empty : Bitops.firstSet 0 = pure 64 := rfl

/-- A nonempty set reports its lowest member: set, in range, and nothing below it is set. -/
theorem firstSet_spec (x : BitVec 64) (hx : x ≠ 0) :
    ∃ r, Bitops.firstSet x = pure r ∧ r.toNat < 64 ∧ x.getLsbD r.toNat = true ∧
      ∀ j < r.toNat, x.getLsbD j = false := by
  have hb : x.ctz.toNat < 2 ^ 7 := Nat.lt_of_le_of_lt (Zig.ctz_le_width x) (by decide)
  have hlt : x.ctz.toNat < 64 := by
    have := BitVec.lt_def.mp (BitVec.ctz_lt_iff_ne_zero.mpr hx)
    simpa using this
  have hc := Zig.ctz_toNat 7 x hb
  have hr : ((Zig.ctz 7 x).setWidth 32).toNat = (Zig.ctz 7 x).toNat := by
    simp only [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨(Zig.ctz 7 x).setWidth 32, ?_, ?_, ?_, ?_⟩ <;> try rw [hr]
  · simp [Bitops.firstSet, show ¬x = 0#64 from hx]
  · omega
  · exact Zig.getLsbD_at_ctz 7 x hb hx
  · exact Zig.getLsbD_below_ctz 7 x hb

/-- `clearLowest` is the iteration step and strictly shrinks a nonempty set. -/
theorem clearLowest_spec (x : BitVec 64) : Bitops.clearLowest x = pure (x &&& Zig.subWrap x 1) := rfl

theorem clearLowest_lt (x : BitVec 64) (hx : x ≠ 0) :
    ∃ r, Bitops.clearLowest x = pure r ∧ r.toNat < x.toNat ∧ ∀ j, r.getLsbD j = true → x.getLsbD j = true :=
  ⟨_, clearLowest_spec x, Zig.and_subWrap_one_lt x hx, fun j h => by
    simp only [BitVec.getLsbD_and, Bool.and_eq_true] at h; exact h.1⟩

end BitopsGenerated
