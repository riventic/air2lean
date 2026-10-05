import Proofs.Vectors.Proofs

/-!
Kernel-only domain regressions for the checked-in four-lane unsigned addition.
All operands are arbitrary: there is no sampled execution or native evaluator.
This module is included by the existing `Proofs.+` library glob.
-/

namespace Vectors.CheckedAddChecks

-- A witness can be any lane; no premise excludes overflow in earlier lanes.
example (a b : Zig.Vec (BitVec 32) 4) (i : Fin 4)
    (h : 2 ^ 32 ≤ a.lanes[i.val].toNat + b.lanes[i.val].toNat) :
    checkedAdd a b = throw .overflow :=
  checkedAdd_overflow a b ⟨i.val, i.isLt, h⟩

-- Equality at the threshold is overflow, rather than a successful wrapped zero.
example (a b : Zig.Vec (BitVec 32) 4) (i : Fin 4)
    (h : a.lanes[i.val].toNat + b.lanes[i.val].toNat = 2 ^ 32) :
    checkedAdd a b = throw .overflow :=
  checkedAdd_overflow a b ⟨i.val, i.isLt, Nat.le_of_eq h.symm⟩

-- The successful equation gives the bound back for each arbitrary lane.
example (a b : Zig.Vec (BitVec 32) 4)
    (h : checkedAdd a b = pure (Zig.Vec.map2 (· + ·) a b))
    (i : Nat) (hi : i < 4) :
    (a.lanes[i]'hi).toNat + (b.lanes[i]'hi).toNat < 2 ^ 32 :=
  (checkedAdd_ok_iff a b).mp h i hi

-- An overflow equation cannot arise without an actual overflowing lane.
example (a b : Zig.Vec (BitVec 32) 4)
    (h : checkedAdd a b = throw .overflow) :
    ∃ i : Fin 4, 2 ^ 32 ≤ a.lanes[i.val].toNat + b.lanes[i.val].toNat :=
  (checkedAdd_overflow_iff a b).mp h

-- The unconditional classification rules out the model's no-result outcome.
example (a b : Zig.Vec (BitVec 32) 4) : (checkedAdd a b).run.isSome = true := by
  rw [checkedAdd_spec]
  split <;> rfl

end Vectors.CheckedAddChecks
