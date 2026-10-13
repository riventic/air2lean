import ZigLean.Sep.Full.Auto

/-!
# `fsym` on variable pointers (`docs/proof-automation.md`)

Pointers whose block is not in the context: `fsym` reads the block, the offset and the alignment
of a pointer off the precondition's atoms that own memory at it (`@[fsym_facts]`), when a rule's
side goal or an `if` needs them; a pointer kept in an optional field of the locals is found by
splitting the field (its equation replaces the field in the facts and in the precondition).
Facts that need the memory or a pair of atoms (`MemFacts`: a token's grant in its authority's
map) close an unreachable panic. The programs are written by hand in the shape the translator
generates.
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

/-- The state of an allocator with grants: a first node, if any, and the grant map (which is
empty without a first node). -/
structure Grants where
  first : Option Ptr
  M : GMap

/-- `const node = self.first orelse unreachable` of a `free` that holds a grant's token. -/
def firstNode (w : Grants) : MemM Unit :=
  if w.first.isSome then pure () else throw .panic

/-- The panic is unreachable from a pair of atoms (`MemFacts`, `facts_gfrag`): a token names a
grant of its authority's map, and the map is empty without a first node. The test `isSome`
becomes `w.first = none`, which reduces the `match`, whose fact `w.M = GMap.empty` replaces the
field. -/
theorem first_node (w : Grants) (γ e i : Nat) (g : GRegion) :
    FTotalTriple (⟪match w.first with | none => w.M = GMap.empty | some _ => True⟫ ⋆
        gauthP γ e w.M none ⋆ gfrag γ e i g) (firstNode w)
      (fun _ => gauthP γ e w.M none ⋆ gfrag γ e i g) := by
  unfold firstNode
  fsym

set_option linter.unusedVariables false in
/-- Rejected: without the token the panic is reachable. -/
example (w : Grants) (γ e : Nat) : True := by
  fail_if_success
    have : FTotalTriple (⟪match w.first with | none => w.M = GMap.empty | some _ => True⟫ ⋆
        gauthP γ e w.M none) (firstNode w) (fun _ => gauthP γ e w.M none) := by
      unfold firstNode
      fsym
  trivial

/-- The block of a pointer value (`⟨some b, o⟩`, a mapping's start) is its first component, by
evaluation, also with no fact about it: the planner joins two regions of it. -/
theorem block_of_value (b : BlockId) (A S : Nat) (K : BlockKind) (bs cs : Array Byte)
    (hb : bs.size = 8) :
    EUpd (up (regionIn ⟨some b, 0⟩ A S K 8 bs) ⋆ up (regionIn (Ptr.add ⟨some b, 0⟩ 8) A S K 8 cs))
      (up (regionIn ⟨some b, 0⟩ A S K 8 (bs ++ cs))) := by
  fsym_entail

end SepAuto.Facts
