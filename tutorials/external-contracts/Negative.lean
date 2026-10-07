import ZigLean.External

/-! Negative control: Lean must reject this file. The contract promises only `result ≤ hi`,
not `result = x`, so a client cannot derive the identity from the contract. The model and
contract are repeated from Main.lean. -/
-- expect-error: Type mismatch

namespace ExternalContracts

open Zig Zig.External

def clamp (args : BitVec 8 × BitVec 8) : MemM (BitVec 8) :=
  pure (if args.1.toNat ≤ args.2.toNat then args.1 else args.2)

def clampContract : Contract (BitVec 8 × BitVec 8) (BitVec 8) where
  pre := fun _ _ => True
  post := fun args before result after => result.toNat ≤ args.2.toNat ∧ after = before
  frame := fun _ before after => after = before
  access := fun _ _ _ => False
  failure := fun _ _ _ => False
  divergence := fun _ _ => False

theorem clampEvidence : clampContract.Holds .total [] .preserves clamp := by
  intro args before _
  change ((if args.1.toNat ≤ args.2.toNat then args.1 else args.2).toNat ≤ args.2.toNat ∧
      before = before) ∧ before = before ∧
    (∃ delta : Array FootprintEntry,
      before.footprint = before.footprint ++ delta ∧ ∀ entry, entry ∈ delta.toList → False) ∧
    (Effects.preserves = .preserves → before = before)
  refine ⟨⟨?_, rfl⟩, rfl, ⟨#[], by simp, by simp⟩, fun _ => rfl⟩
  split <;> omega

theorem clamp_returns_x {args : BitVec 8 × BitVec 8} {before after : Mem} {result : BitVec 8}
    (run : clamp args before = some (.ok (result, after))) : result = args.1 :=
  (clampContract.success clampEvidence trivial run).1

end ExternalContracts
