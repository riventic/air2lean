import ZigLean.Mem.Basic

/-!
# The fields of a spawn capture

A spawn copies its argument tuple into the child. `Emit.lean` classifies each captured field
(`Tgt.captures`): a value is copied bits with no pointer identity; a pointer or slice copies only
its identity, so the pointed-to region stays in shared memory and a proof must say how the child
gets it (`ZigLean/Conc/Transfer.lean`). Fields whose type may embed pointer identities that the
emitter does not decompose (aggregates holding pointers, allocators, `Io`, thread handles) are
`other`: the generated ownership obligation cannot be discharged for them.
-/

namespace Zig.Conc

/-- One captured field of a spawn target, in source order. -/
inductive Capture where
  /-- Copied bits with no pointer identity: no ownership obligation. -/
  | value
  /-- A copied single-item or many-item pointer: its region must be transferred or shared. -/
  | ptr (p : Ptr)
  /-- A copied slice: its region (from `s.ptr`) must be transferred or shared. -/
  | slice (s : Slice)
  /-- A value whose embedded pointer identities are not decomposed. -/
  | other
  deriving DecidableEq, Repr, Inhabited

end Zig.Conc
