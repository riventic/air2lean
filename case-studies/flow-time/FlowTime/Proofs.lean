import FlowTime.Gen
import ZigLean.Mem.WidthLemmas

/-! Universal contracts for the two monomorphizations of Flow's original `addDuration`.
The `timestamp*_body` lemmas unfold the generated definitions, connecting the reusable
arithmetic argument to the AIR-derived code: both are instances of the library's width-generic
case analysis of `@addWithOverflow` against `maxInt` (`Zig.addWithOverflow_max_cases`), which
the translations of the same rule for other targets use too
(`tests/roadmap/wasm-correspondence`, T05). There are no added axioms. -/

namespace FlowTime

/-- The representability contract: the maximum bit pattern is reserved. -/
def timestampSpec {n : Nat} (a b : BitVec n) : Zig.Result (Except Zig.ErrName (BitVec n)) :=
  pure (if 2 ^ n - 1 ≤ a.toNat + b.toNat then .error "TimeOverflow" else .ok (a + b))

/-- Under no machine overflow, equality with the reserved pattern is exactly equality
of the mathematical sum with the reserved maximum. -/
theorem reserved_iff {n : Nat} (a b : BitVec n)
    (h : a.toNat + b.toNat < 2 ^ n) :
    a + b = BitVec.ofNat n (2 ^ n - 1) ↔ a.toNat + b.toNat = 2 ^ n - 1 := by
  have hp : 0 < 2 ^ n := Nat.two_pow_pos n
  have hm : 2 ^ n - 1 < 2 ^ n := by omega
  constructor
  · intro he
    have he' := congrArg BitVec.toNat he
    simpa [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
      Nat.mod_eq_of_lt hm] using he'
  · intro he
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, he]

/-- The contract is the width-generic closed form of the library (`Zig.addBelowMaxOpt`,
`ZigLean/Mem/WidthLemmas.lean`): `none` is `error.TimeOverflow`. -/
theorem timestampSpec_eq {n : Nat} (a b : BitVec n) :
    timestampSpec a b = pure ((Zig.addBelowMaxOpt a b).elim (.error "TimeOverflow") .ok) := by
  unfold timestampSpec Zig.addBelowMaxOpt
  split <;> rfl

/- Each monomorphization is an instance of the one width-generic case analysis
(`Zig.addWithOverflow_max_cases`) at its width's `maxInt`. -/
theorem timestamp32_body (a b : BitVec 32) : timestamp32 a b = timestampSpec a b := by
  rw [timestampSpec_eq]
  rcases Zig.addWithOverflow_max_cases a b 4294967295#32 (by decide) with h | h | h <;>
    simp [timestamp32, zig_unfold, h]

theorem timestamp64_body (a b : BitVec 64) : timestamp64 a b = timestampSpec a b := by
  rw [timestampSpec_eq]
  rcases Zig.addWithOverflow_max_cases a b 18446744073709551615#64 (by decide) with h | h | h <;>
    simp [timestamp64, zig_unfold, h]

/-- Generic exact-addition theorem used by both original-source monomorphizations. -/
theorem timestampSpec_exact {n : Nat} (a b : BitVec n)
    (h : a.toNat + b.toNat < 2 ^ n - 1) :
    timestampSpec a b = pure (.ok (a + b)) ∧
      (a + b).toNat = a.toNat + b.toNat := by
  have hs := Zig.addBelowMaxOpt_eq_some a b h
  exact ⟨by rw [timestampSpec_eq, hs.1]; rfl, hs.2⟩

/-- The only error cases are machine overflow or equality with the reserved maximum. -/
theorem timestampSpec_error_iff {n : Nat} (a b : BitVec n) :
    timestampSpec a b = pure (.error "TimeOverflow") ↔
      2 ^ n ≤ a.toNat + b.toNat ∨ a.toNat + b.toNat = 2 ^ n - 1 := by
  by_cases h : 2 ^ n - 1 ≤ a.toNat + b.toNat
  · have hbad : 2 ^ n ≤ a.toNat + b.toNat ∨ a.toNat + b.toNat = 2 ^ n - 1 := by omega
    simp [timestampSpec, h, hbad]
  · have hgood : ¬ (2 ^ n ≤ a.toNat + b.toNat ∨ a.toNat + b.toNat = 2 ^ n - 1) := by omega
    constructor
    · intro he
      simp only [timestampSpec, if_neg h] at he
      change (some (Except.ok (Except.ok (a + b))) : Zig.Result (Except Zig.ErrName (BitVec n))) =
        some (Except.ok (Except.error "TimeOverflow")) at he
      have inner := Except.ok.inj (Option.some.inj he)
      cases inner
    · intro hbad
      exact False.elim (hgood hbad)

/-- Every successful result is the exact mathematical addition, below the reservation. -/
theorem timestamp32_exact (a b : BitVec 32) (h : a.toNat + b.toNat < 2 ^ 32 - 1) :
    timestamp32 a b = pure (.ok (a + b)) ∧ (a + b).toNat = a.toNat + b.toNat := by
  rw [timestamp32_body]
  exact timestampSpec_exact a b h

theorem timestamp64_exact (a b : BitVec 64) (h : a.toNat + b.toNat < 2 ^ 64 - 1) :
    timestamp64 a b = pure (.ok (a + b)) ∧ (a + b).toNat = a.toNat + b.toNat := by
  rw [timestamp64_body]
  exact timestampSpec_exact a b h

theorem timestamp32_error_iff (a b : BitVec 32) :
    timestamp32 a b = pure (.error "TimeOverflow") ↔
      2 ^ 32 ≤ a.toNat + b.toNat ∨ a.toNat + b.toNat = 2 ^ 32 - 1 := by
  rw [timestamp32_body]
  exact timestampSpec_error_iff a b

theorem timestamp64_error_iff (a b : BitVec 64) :
    timestamp64 a b = pure (.error "TimeOverflow") ↔
      2 ^ 64 ≤ a.toNat + b.toNat ∨ a.toNat + b.toNat = 2 ^ 64 - 1 := by
  rw [timestamp64_body]
  exact timestampSpec_error_iff a b

end FlowTime
