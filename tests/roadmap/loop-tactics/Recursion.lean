import Proofs.Recursion.Proofs

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

/-! ## Self-recursive: `gcd` -/

theorem gcd_spec (a b : BitVec 32) :
    Recursion.gcd a b = pure (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat)) :=
  _root_.gcd_spec a b

/-! ## Mutually recursive: `isEven` / `isOdd` -/

theorem isEven_isOdd_spec (n : BitVec 32) :
    Recursion.isEven n = pure (n.toNat % 2 == 0) ∧ Recursion.isOdd n = pure (n.toNat % 2 == 1) :=
  ⟨_root_.isEven_spec n, _root_.isOdd_spec n⟩

/-! ## A range premise in the specification: `fact` -/

/-- The shared mathematical factorial of `Proofs.Recursion.Proofs`. -/
abbrev natFact : Nat → Nat := _root_.natFact

/-- The existing range premise is exactly the bounded full-state contract's premise. -/
theorem fact_spec (n : BitVec 32) (hb : n.toNat ≤ 12) :
    Recursion.fact n = pure (BitVec.ofNat 32 (natFact n.toNat)) :=
  _root_.fact_ok n hb

end RecursionTest

-- Only the standard axioms: no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`).
/-- info: 'RecursionTest.isEven_isOdd_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecursionTest.isEven_isOdd_spec

/-- info: 'RecursionTest.gcd_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecursionTest.gcd_spec

/-- info: 'RecursionTest.fact_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecursionTest.fact_spec
