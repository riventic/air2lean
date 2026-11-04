import Proofs.Recursion.Proofs
import ZigLean.Simp

/-!
# Recursive generated functions, through their full-state contracts

The functions are the committed translations of `examples/recursion/recursion.zig`
(`Proofs/Recursion/Gen.lean`). `Proofs.Recursion.Proofs` proves their full-state total contracts
with the generic `FTotalTriple.rec_group` and one `fsym` walk per group. This fixture preserves
its result equations as consumers of the public adequacy projections; it does not repeat the
generated-program induction or command walk.

* `gcd`: self-recursive; the second argument decreases by `a % b < b`, not by one.
* `isEven`/`isOdd`: a mutually recursive group, with both results combined below.
* `fact`: self-recursive with a checked multiply; the specification carries a range premise,
  retained unchanged from the bounded total contract.

These pure `Zig.Result` functions have no modeled frame operations; their native interpretation
retains STK-01. Memory-backed recursion additionally needs the actual stack resources and room,
as in `Proofs/Pointers/Sep.lean`; these equations make no native-stack or cost claim.
-/

namespace RecursionTest
open Zig

/-! ## Self-recursive: `gcd` -/

theorem rem_unsigned (a b : BitVec 32) :
    Zig.rem false a b = if b = 0 then throw .illegal else pure (a % b) := rfl

theorem gcd_spec (a b : BitVec 32) :
    Recursion.gcd a b = pure (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat)) :=
  _root_.gcd_spec a b

/-! ## Mutually recursive: `isEven` / `isOdd` -/

theorem succ_parity0 (k : Nat) : ((k + 1) % 2 == 0) = (k % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h, Nat.add_mod]

theorem succ_parity1 (k : Nat) : ((k + 1) % 2 == 1) = (k % 2 == 0) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h, Nat.add_mod]

/-- `n.toNat = (n - 1).toNat + 1` for `n ≠ 0`: the recursive argument is one smaller. -/
theorem toNat_pred (n : BitVec 32) (hn0 : n ≠ 0#32) : n.toNat = (n - 1#32).toNat + 1 := by
  rw [Zig.toNat_sub_one n hn0]
  have : n.toNat ≠ 0 := fun h => hn0 (BitVec.eq_of_toNat_eq (by simpa using h))
  omega

theorem isEven_isOdd_spec (n : BitVec 32) :
    Recursion.isEven n = pure (n.toNat % 2 == 0) ∧ Recursion.isOdd n = pure (n.toNat % 2 == 1) :=
  ⟨_root_.isEven_spec n, _root_.isOdd_spec n⟩

/-! ## A range premise in the specification: `fact` -/

def natFact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * natFact n

private theorem natFact_eq (k : Nat) : natFact k = _root_.natFact k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [natFact, _root_.natFact, ih]

theorem natFact_mono {m n : Nat} (h : m ≤ n) : natFact m ≤ natFact n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    rename_i n' _
    exact Nat.le_trans ih (Nat.le_mul_of_pos_left (natFact n') (show 0 < n' + 1 by omega))

/-- The existing range premise is exactly the bounded full-state contract's premise. -/
theorem fact_spec (n : BitVec 32) (hb : n.toNat ≤ 12) :
    Recursion.fact n = pure (BitVec.ofNat 32 (natFact n.toNat)) := by
  simpa only [natFact_eq] using _root_.fact_ok n hb

end RecursionTest

-- Only the standard axioms: no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`).
/-- info: 'RecursionTest.isEven_isOdd_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecursionTest.isEven_isOdd_spec
