import ZigLean.Sep.Full.Disjoint

/-! O-H regression: globals at program start (`Mem.globalPlace`, `Mem.ofGlobals_liveBounded`).

A placement may put a global anywhere in the address space, so the fallback after `Mem.top` can
find no room for the next one. The first fit (`Mem.firstFit`) packs that global into a gap
instead, so the globals of every program whose globals fit (`Mem.GlobalsFit`, which the
translator checks: `GLOBALS_TOO_LARGE`, `tests/roadmap/input-validation`) end below `2 ^ 63`
under every placement, and the memory at program start has the layout of `Mem.FSeq`. -/

open Zig

/-- A placement that puts block 0 at the very end of a 2^20-byte address space. -/
def σEnd : Placement :=
  { propose := (fun b => if b = 0 then some (2 ^ 20 - 64) else none), addrLimit := 2 ^ 20 }

def gs : List (Array Byte × Nat × BlockKind) :=
  [(Array.replicate 64 .undef, 8, .global), (Array.replicate 32 .undef, 8, .global)]

/-- Block 0 is where the placement put it; block 1 finds no room after it and goes first fit. -/
example : (Mem.ofGlobals σEnd gs).blocks.toList.map (·.addr) = [2 ^ 20 - 64, 4096] := by decide +kernel

theorem gs_layout (σ : Placement) : (Mem.ofGlobals σ gs).LiveLayout :=
  Mem.ofGlobals_liveLayout σ gs (by decide)

#print axioms gs_layout
