import Air2Lean.Memory

/-! Kernel reduction of the bounded provenance rule, independently of code generation. -/
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
end LocalParentProof
