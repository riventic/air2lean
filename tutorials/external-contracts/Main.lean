import ZigLean.External

/-!
External contracts: a project-supplied Lean model for an external `clamp(x: u8, hi: u8) u8`,
its contract, the evidence that the model meets the contract, and a client consequence that
uses only the contract.

From the repository root:
  lake build ZigLean.External
  lake env lean tutorials/external-contracts/Main.lean

See tutorials/external-contracts/README.md for the registry entry, the exercise and the
negative control.
-/

namespace ExternalContracts

open Zig Zig.External

/-- The model (registry `implementation`): it reads no memory and changes nothing. -/
def clamp (args : BitVec 8 × BitVec 8) : MemM (BitVec 8) :=
  pure (if args.1.toNat ≤ args.2.toNat then args.1 else args.2)

/-- The contract (registry `contract`): the result is at most `hi`, memory is unchanged, no new
accesses, no failure and no divergence. -/
def clampContract : Contract (BitVec 8 × BitVec 8) (BitVec 8) where
  pre := fun _ _ => True
  post := fun args before result after => result.toNat ≤ args.2.toNat ∧ after = before
  frame := fun _ before after => after = before
  access := fun _ _ _ => False
  failure := fun _ _ _ => False
  divergence := fun _ _ => False

/-- The evidence (registry `proof`, `trust: "proved"`, `termination: "total"`, `errors: []`,
`effects: "preserves"`). -/
theorem clampEvidence : clampContract.Holds .total [] .preserves clamp := by
  intro args before _
  change ((if args.1.toNat ≤ args.2.toNat then args.1 else args.2).toNat ≤ args.2.toNat ∧
      before = before) ∧ before = before ∧
    (∃ delta : Array FootprintEntry,
      before.footprint = before.footprint ++ delta ∧ ∀ entry, entry ∈ delta.toList → False) ∧
    (Effects.preserves = .preserves → before = before)
  refine ⟨⟨?_, rfl⟩, rfl, ⟨#[], by simp, by simp⟩, fun _ => rfl⟩
  split <;> omega

/-- A client consequence through the reusable rule: every successful call returns at most
`hi`. -/
theorem clamp_le_hi {args : BitVec 8 × BitVec 8} {before after : Mem} {result : BitVec 8}
    (run : clamp args before = some (.ok (result, after))) : result.toNat ≤ args.2.toNat :=
  (clampContract.success clampEvidence trivial run).1

end ExternalContracts
