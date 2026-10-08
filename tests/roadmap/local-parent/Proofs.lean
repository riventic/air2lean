import Air2Lean.Memory
import ZigLean.Mem.Parent

/-! Kernel reduction of the bounded provenance rule, independently of code generation, and
the general recovery theorems (L11). -/
open Air2Lean
namespace LocalParentProof

-- The kernel unfolds provenance and concrete array operations for these claims.
deriving instance DecidableEq for LocalPathStep
private def types : Array Ty := #[.int false 32, .struct "Pair" "auto" #[("x", 0), ("y", 0)],
  .ptr "one" false 0, .ptr "one" false 1,
  .struct "Outer" "auto" #[("inner", 1)], .ptr "one" false 4]
private def layouts : Array Layout := Array.replicate types.size {}

/-- Removing only the terminal step leaves the enclosing container path unchanged. -/
example : localParentPath? types layouts 2 3 1 #[.field 4 0 3, .field 1 1 2] =
    some #[.field 4 0 3] := by decide +kernel
example : localParentPath? types layouts 3 5 0 #[.field 4 0 3] = some #[] := by decide +kernel
example : localParentPath? types layouts 2 3 0 #[.field 1 1 2] = none := rfl
example : localParentPath? types layouts 2 5 1 #[.field 1 1 2] = none := rfl
example : localParentPath? types layouts 2 3 0 #[] = none := rfl
example : localParentPath? types layouts 2 3 0 #[.slice] = none := rfl

/-- Every accepted local recovery, of any depth and types, removes exactly the terminal
step: the recovered place has the original root and the original container path, so it
aliases the container (`Emit.lean`'s `FCtx.computePlaces` pops the same step). -/
theorem localParentPath_pop {types : Array Ty} {layouts : Array Layout} {source result : TyId}
    {index : Nat} {path q : Array LocalPathStep}
    (h : localParentPath? types layouts source result index path = some q) : q = path.pop := by
  unfold localParentPath? at h
  repeat' split at h
  all_goals first | (simp at h) | skip
  all_goals
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h <;> simp_all

/-- Recovering the parent of a field projection (`localPlacePaths` pushes the step) gives
back the container's own path. -/
theorem localParentPath_push {types : Array Ty} {layouts : Array Layout} {source result : TyId}
    {index : Nat} {path q : Array LocalPathStep} {step : LocalPathStep}
    (h : localParentPath? types layouts source result index (path.push step) = some q) :
    q = path := by
  rw [localParentPath_pop h, Array.pop_push]

/-- The memory lowering of `bag.items[1].b` and its recovery (`arrayItem` in `Pipeline.lean`):
the item pointer, in the original block. -/
example (bag : Zig.Ptr) :
    (((bag.add 4).elem 8 1).add 4).add (-4) = (bag.add 4).elem 8 1 ∧
      ((((bag.add 4).elem 8 1).add 4).add (-4)).block = bag.block :=
  ⟨Zig.Ptr.parent_elem_field bag 4 8 1 4, rfl⟩
end LocalParentProof
