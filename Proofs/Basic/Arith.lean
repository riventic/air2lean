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
    by_cases hof : a.ssubOverflow b
    · have hnat : ¬ (a.toInt - b.toInt).natAbs < 2 ^ 31 := by
        simp [BitVec.ssubOverflow] at hof
        omega
      simp [zig_unfold, hgt', Zig.sub, hof, hnat]
    · have hnat : (a.toInt - b.toInt).natAbs < 2 ^ 31 := by
        simp [BitVec.ssubOverflow] at hof
        omega
      have hsub : (a - b).toInt = a.toInt - b.toInt := BitVec.toInt_sub_of_not_ssubOverflow hof
      have hic : Zig.intCast true false 32 (a - b) = pure (BitVec.ofNat 32 (a.toInt - b.toInt).natAbs) := by
        simp [Zig.intCast, Zig.val, hsub]
        split
        · congr 1
          apply BitVec.eq_of_toNat_eq
          simp
          omega
        · omega
      simp [zig_unfold, hgt', Zig.sub, hof, hnat, hic]
  · have hgt' : Zig.gt true a b = false := by
      simp [Zig.gt, Zig.lt, BitVec.slt_eq_decide, hgt]
    by_cases hof : b.ssubOverflow a
    · have hnat : ¬ (a.toInt - b.toInt).natAbs < 2 ^ 31 := by
        simp [BitVec.ssubOverflow] at hof
        omega
      simp [zig_unfold, hgt', Zig.sub, hof, hnat]
    · have hnat : (a.toInt - b.toInt).natAbs < 2 ^ 31 := by
        simp [BitVec.ssubOverflow] at hof
        omega
      have hsub : (b - a).toInt = b.toInt - a.toInt := BitVec.toInt_sub_of_not_ssubOverflow hof
      have hic : Zig.intCast true false 32 (b - a) = pure (BitVec.ofNat 32 (a.toInt - b.toInt).natAbs) := by
        simp [Zig.intCast, Zig.val, hsub]
        split
        · congr 1
          apply BitVec.eq_of_toNat_eq
          simp
          omega
        · omega
      simp [zig_unfold, hgt', Zig.sub, hof, hnat, hic]
