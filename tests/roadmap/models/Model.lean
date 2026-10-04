import ZigLean.External

namespace RegistryExample

def identity (x : BitVec 8) : Zig.MemM (BitVec 8) := pure x

def contract : Zig.External.Contract (BitVec 8) (BitVec 8) where
  pre := fun _ _ => True
  post := fun x before result after => result = x ∧ after = before
  frame := fun _ before after => after = before
  access := fun _ _ _ => False
  failure := fun _ _ _ => False
  divergence := fun _ _ => False

theorem evidence : contract.Holds .total [] .preserves identity := by
  intro x before _
  change (x = x ∧ before = before) ∧ before = before ∧
    (∃ delta : Array Zig.FootprintEntry,
      before.footprint = before.footprint ++ delta ∧
      ∀ entry, entry ∈ delta.toList → False) ∧
    (Zig.External.Effects.preserves = .preserves → before = before)
  refine ⟨⟨rfl, rfl⟩, rfl, ?_, ?_⟩
  · exact ⟨#[], by simp, by simp⟩
  · intro _; rfl

/-- A client consequence uses the reusable rule and declared contract. -/
theorem client_rule {x before result after}
    (run : identity x before = some (.ok (result, after))) : result = x := by
  exact (contract.success evidence (by trivial) run).1

end RegistryExample
