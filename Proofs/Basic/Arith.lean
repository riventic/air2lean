import Proofs.Basic.Gen

/-!
# Proofs about `clampAdd` and `absDiff` from `examples/basic/basic.zig`
-/

open Basic

/-- Zig `a +| b` on `u16` saturates instead of panicking. -/
theorem clampAdd_spec (a b : BitVec 16) :
    clampAdd a b = pure (BitVec.ofNat 16 (min (a.toNat + b.toNat) 65535)) := by
  have h : Zig.addSat false a b = BitVec.ofNat 16 (min (a.toNat + b.toNat) 65535) := by
    apply BitVec.eq_of_toNat_eq
    simp [Zig.addSat, Zig.clamp, Zig.val]
    omega
  unfold clampAdd
  simp [zig_unfold, h]

/-- The checked signed `x - y` (for `y ≤ x`) overflows iff `|x - y| ≥ 2 ^ 31`. -/
theorem ssubOverflow_iff (x y : BitVec 32) (hle : y.toInt ≤ x.toInt) :
    x.ssubOverflow y ↔ ¬ (x.toInt - y.toInt).natAbs < 2 ^ 31 := by
  simp [BitVec.ssubOverflow]; omega

/-- The `@intCast` to `u32` of a non-overflowing `x - y` (for `y ≤ x`) is `|x - y|`. -/
theorem intCast_sub (x y : BitVec 32) (hle : y.toInt ≤ x.toInt) (hof : ¬ x.ssubOverflow y) :
    Zig.intCast true false 32 (x - y) = pure (BitVec.ofNat 32 (x.toInt - y.toInt).natAbs) := by
  have hnat := mt (ssubOverflow_iff x y hle).2 hof
  have hsub : (x - y).toInt = x.toInt - y.toInt := BitVec.toInt_sub_of_not_ssubOverflow hof
  simp [Zig.intCast, Zig.val, hsub]
  split
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp
    omega
  · omega

/-- `absDiff` computes `|a - b|` (i32 → u32, via a checked signed subtraction): it panics iff
the signed difference has magnitude `≥ 2 ^ 31`. -/
theorem absDiff_spec (a b : BitVec 32) :
    absDiff a b = if (a.toInt - b.toInt).natAbs < 2 ^ 31 then
        pure (BitVec.ofNat 32 (a.toInt - b.toInt).natAbs)
      else throw .overflow := by
  unfold absDiff
  by_cases hgt : b.toInt < a.toInt
  · have hgt' : Zig.gt true a b = true := by
      simp [Zig.gt, Zig.lt, BitVec.slt_eq_decide, hgt]
    have hiff := ssubOverflow_iff a b (by omega)
    by_cases hof : a.ssubOverflow b
    · simp [zig_unfold, hgt', Zig.sub, hof, hiff.1 hof]
    · simp [zig_unfold, hgt', Zig.sub, hof, intCast_sub a b (by omega) hof,
        Decidable.of_not_not (mt hiff.2 hof)]
  · have hgt' : Zig.gt true a b = false := by
      simp [Zig.gt, Zig.lt, BitVec.slt_eq_decide, hgt]
    have hcomm : (a.toInt - b.toInt).natAbs = (b.toInt - a.toInt).natAbs := by omega
    have hiff := ssubOverflow_iff b a (by omega)
    rw [hcomm]
    by_cases hof : b.ssubOverflow a
    · simp [zig_unfold, hgt', Zig.sub, hof, hiff.1 hof]
    · simp [zig_unfold, hgt', Zig.sub, hof, intCast_sub b a (by omega) hof,
        Decidable.of_not_not (mt hiff.2 hof)]
