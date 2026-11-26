import ZigLean.Mem.WidthLemmas

/-!
# T05: the contracts of the DES kernels, stated once for every target

`kernels.zig` is translated once per target profile (`check.sh`): x86_64-linux, aarch64-macos,
wasm32-freestanding and wasm32-wasi. A `Kernels` value is one such translation, and
`Kernels.Meets k w` is the contract of a translation `k` for a profile of pointer width `w`.
It is stated here once, without naming a target, and what follows from it is proved once
(`Kernels.Meets.exact_agree`, `Kernels.Meets.usize_bits_eq_iff`, the `timeAdd` and `eventBefore`
facts). `V0_17_1/Proofs.lean` proves that each translation meets it at its profile's width; the
statements about one target's generated module are instances.

The classes are those of `relation.json` (docs/research/T05.md): the contract of an **exact**
kernel does not mention `w`, so two translations that meet the contract are equal on it whatever
their targets; the contract of a **target-specific** kernel (`usize_bits`) is a function of `w`.
-/

namespace WasmCorrespondence

open Zig

/-- The translations of the kernels of `kernels.zig` for one target profile. Every export maps
`u64` words to a `u64` word. -/
structure Kernels where
  des_time_add32 : BitVec 64 → BitVec 64 → Result (BitVec 64)
  des_time_add64 : BitVec 64 → BitVec 64 → Result (BitVec 64)
  des_event_before : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → Result (BitVec 64)
  usize_bits : Result (BitVec 64)

/-- Flow's `addDuration` rule at `n` bits on operands truncated to `n` bits: the sum, or
`maxInt(u64)` (the kernels' `none`) when it overflows `n` bits or is the reserved `2 ^ n - 1`. -/
def timeAdd (n : Nat) (a b : BitVec 64) : BitVec 64 :=
  ((addBelowMaxOpt (a.setWidth n) (b.setWidth n)).map (·.setWidth 64)).getD (-1)

/-- The event order: the earlier time first, then the lower 32-bit sequence number. -/
def eventBefore (t1 s1 t2 s2 : BitVec 64) : BitVec 64 :=
  if t1.toNat < t2.toNat ∨ (t1 = t2 ∧ s1.toNat % 2 ^ 32 < s2.toNat % 2 ^ 32) then 1 else 0

/-- The contract of a translation for a profile of pointer width `w`. No kernel panics. -/
structure Kernels.Meets (k : Kernels) (w : PtrWidth) : Prop where
  time_add32 : ∀ a b, k.des_time_add32 a b = pure (timeAdd 32 a b)
  time_add64 : ∀ a b, k.des_time_add64 a b = pure (timeAdd 64 a b)
  event_before : ∀ t1 s1 t2 s2, k.des_event_before t1 s1 t2 s2 = pure (eventBefore t1 s1 t2 s2)
  usize_bits : k.usize_bits = pure (BitVec.ofNat 64 w.bits)

/-! ## The representability rule -/

/-- Below the reserved maximum the result is the exact sum of the truncated operands. -/
theorem timeAdd_exact {n : Nat} (hn : n ≤ 64) (a b : BitVec 64)
    (h : a.toNat % 2 ^ n + b.toNat % 2 ^ n < 2 ^ n - 1) :
    (timeAdd n a b).toNat = a.toNat % 2 ^ n + b.toNat % 2 ^ n := by
  have hle : 2 ^ n ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hn
  have hs := addBelowMaxOpt_eq_some (a.setWidth n) (b.setWidth n)
    (by simpa [BitVec.toNat_setWidth] using h)
  simp only [timeAdd, hs.1, Option.map_some, Option.getD_some, BitVec.toNat_setWidth, hs.2]
  exact Nat.mod_eq_of_lt (by omega)

/-- An overflow of `n` bits and the reserved maximum itself are `none`. -/
theorem timeAdd_none {n : Nat} (a b : BitVec 64)
    (h : 2 ^ n - 1 ≤ a.toNat % 2 ^ n + b.toNat % 2 ^ n) : timeAdd n a b = -1 := by
  have hs := (addBelowMaxOpt_eq_none_iff (a.setWidth n) (b.setWidth n)).mpr
    (by simpa [BitVec.toNat_setWidth] using h)
  simp [timeAdd, hs]

/-! ## The event order -/

theorem eventBefore_irrefl (t s : BitVec 64) : eventBefore t s t s = 0 := by
  simp [eventBefore]

theorem eventBefore_asymm (t1 s1 t2 s2 : BitVec 64) (h : eventBefore t1 s1 t2 s2 = 1) :
    eventBefore t2 s2 t1 s1 = 0 := by
  unfold eventBefore at h ⊢
  split at h
  · rename_i hc
    split
    · rename_i hc'
      exfalso
      rcases hc' with h' | ⟨rfl, h'⟩ <;> rcases hc with hc | ⟨hc, hs⟩ <;>
        first | omega | (subst hc; omega)
    · rfl
  · exact absurd h (by decide)

/-! ## What two translations share -/

/-- The exact kernels do not depend on the target: translations that meet the contract, for any
two pointer widths, are the same functions on them. -/
theorem Kernels.Meets.exact_agree {k k' : Kernels} {w w' : PtrWidth} (h : k.Meets w)
    (h' : k'.Meets w') :
    k.des_time_add32 = k'.des_time_add32 ∧ k.des_time_add64 = k'.des_time_add64 ∧
      k.des_event_before = k'.des_event_before := by
  refine ⟨?_, ?_, ?_⟩
  · funext a b; rw [h.time_add32, h'.time_add32]
  · funext a b; rw [h.time_add64, h'.time_add64]
  · funext t1 s1 t2 s2; rw [h.event_before, h'.event_before]

/-- The target-specific kernel tells the pointer widths apart, and nothing else. -/
theorem Kernels.Meets.usize_bits_eq_iff {k k' : Kernels} {w w' : PtrWidth} (h : k.Meets w)
    (h' : k'.Meets w') : k.usize_bits = k'.usize_bits ↔ w = w' := by
  rw [h.usize_bits, h'.usize_bits]
  have inj (x y : BitVec 64) : (pure x : Result (BitVec 64)) = pure y ↔ x = y :=
    ⟨fun e => Except.ok.inj (Option.some.inj e), fun e => e ▸ rfl⟩
  cases w <;> cases w' <;> simp only [inj] <;> decide

/-- `des_time_add64` below the reserved maximum, on any target: the exact `u64` sum. -/
theorem Kernels.Meets.time_add64_exact {k : Kernels} {w : PtrWidth} (h : k.Meets w)
    (a b : BitVec 64) (hs : a.toNat + b.toNat < 2 ^ 64 - 1) :
    k.des_time_add64 a b = pure (a + b) ∧ (a + b).toNat = a.toNat + b.toNat := by
  have hs' := addBelowMaxOpt_eq_some a b hs
  refine ⟨?_, hs'.2⟩
  rw [h.time_add64]
  simp [timeAdd, hs'.1]

end WasmCorrespondence
