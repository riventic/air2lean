import ZigLean.Sep.Full.AutoAll

/-!
# Blocks in the full-state logic (`ZigLean/Sep/Full/Block.lean`), library-only

A block is made and ended again; `fsym` walks it with the library's `alloc` and `free` rules
(partial: `alloc` may find no room, a stack overflow).
-/

namespace OneLogic.Block

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- Make an 8-byte heap block and free it. -/
def cycle : MemM Unit := do
  let p ← Zig.alloc .heap 8 8
  Zig.free p

theorem cycle_spec (R : FAssn) : FTriple R cycle (fun _ => R) := by
  unfold cycle
  fsym

/-- The same with a stack block (`allocStack`). -/
def stackCycle : MemM Unit := do
  let p ← Zig.allocStack 16 8
  Zig.free p

theorem stackCycle_spec (R : FAssn) : FTriple R stackCycle (fun _ => R) := by
  unfold stackCycle
  fsym

/-- A free under every placement and provenance mode (address reuse, M05): it returns, and the
block's bytes and extent are gone. -/
theorem free_withPlacement {p : Ptr} {A S : Nat} {bs : Array Byte} {b : BlockId}
    (hpb : p.block = some b) (hS : bs.size = S) (h0 : p.off = 0) (hpos : 0 < S) {m : Mem}
    {r rF : Res} (hh : Holds m r rF) (hp : (up (bytesAt p A S .heap bs) ⋆ bext b S .heap) r)
    (hs : m.FSeq) (σ : Placement) (pm : ProvenanceMode) :
    ∃ v m' r', (Zig.free p).run (m.withPlacement σ pm) = pure (v, m') ∧ Holds m' r' rF ∧
      emp r' ∧ m'.FSeq :=
  (FTotalTriple.free hpb hS h0 hpos (by decide)).withPlacement hh hp hs σ pm

end OneLogic.Block
