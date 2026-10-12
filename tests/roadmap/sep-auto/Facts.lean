import ZigLean.Sep.Full.Auto

/-!
# `fsym` on variable pointers (`docs/proof-automation.md`)

Pointers whose block is not in the context: `fsym` reads the block, the offset and the alignment
of a pointer off the precondition's atoms that own memory at it (`@[fsym_facts]`), when a rule's
side goal or an `if` needs them; a pointer kept in an optional field of the locals is found by
splitting the field (its equation replaces the field in the facts and in the precondition). The
programs are written by hand in the shape the translator generates.
-/

namespace SepAuto.Facts

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- `@intFromPtr` of a pointer and its alignment check (`std.mem.isAligned`). -/
def checkAligned (p : Ptr) : MemM Unit := do
  let a ← Zig.ptrAddr p
  if a % 8 = 0 then pure () else throw .panic

/-- The address of a variable pointer into an owned, 8-aligned region whose block the context
does not know: the region gives the block (for `ptrAddr`), and the alignment decides the check. -/
theorem aligned (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) (hs : 0 < bs.size) :
    FTotalTriple (up (regionIn p A S K 8 bs)) (checkAligned p) (fun _ => up (regionIn p A S K 8 bs)) := by
  unfold checkAligned
  fsym

/-- A word field at offset 8 of a node at a variable pointer: the pointer formation needs the
node's block and a nonnegative offset, both from the owned words. -/
def secondField (p : Ptr) : MemM (BitVec 64) := do
  let q ← Zig.ptrProject p (·.add 8)
  Zig.load (BitVec 64) 8 q

theorem second_field (p : Ptr) (v w : BitVec 64) :
    FTotalTriple (up (pts p 8 v) ⋆ up (pts (p.add 8) 8 w)) (secondField p)
      (fun r => ⟪r = w⟫ ⋆ up (pts p 8 v) ⋆ up (pts (p.add 8) 8 w)) := by
  unfold secondField
  fsym

/-- The locals of a generated function with an optional pointer. -/
structure Locals where
  cur : Option Ptr

/-- `if (s.cur) |p| p.* else 0`, as generated (`.?` after the test). -/
def firstWord (s : Locals) : MemM (BitVec 64) := do
  if s.cur.isSome then
    let p ← StateT.lift (optPayload s.cur)
    Zig.load (BitVec 64) 8 p
  else pure 0

/-- The precondition matches on the field: the test splits it. -/
theorem first_word (s : Locals) (v : BitVec 64) :
    FTotalTriple (match s.cur with | none => emp | some p => up (pts p 8 v)) (firstWord s)
      (fun r => match s.cur with | none => ⟪r = 0⟫ | some p => ⟪r = v⟫ ⋆ up (pts p 8 v)) := by
  unfold firstWord
  fsym

end SepAuto.Facts
