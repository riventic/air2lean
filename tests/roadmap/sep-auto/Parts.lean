import ZigLean.Sep.Full.Auto

/-!
# Accesses over several owned parts (`ZigLean/Sep/Full/Parts.lean`, `docs/proof-automation.md` §Parts)

A struct whose bytes several parts own: the arena's header (its child allocator's bytes as a
region, its two list heads as atomic words, which the atomic ops need), a list header as one atom
per field. A load of the whole struct reads each field from the part that owns it and builds the
struct of the fields' values (`ReadsAt`, `load_reads`); a store writes each field by the rule of
the part that owns it (`storeBytes_parts`), and each part keeps its view (the words their
atomic tag). The structs are written as the translator writes them (Zig 0.17's
`std.heap.ArenaAllocator`, `std.ArrayListUnmanaged(u32)`).
-/

namespace SepAuto.Parts

open Zig Zig.Full Zig.Full.FAssn

structure Alloc where
  ptr : Zig.Ptr
  vtable : Zig.Ptr
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Alloc where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.ptr), (8, Zig.Enc.encode v.vtable)]
  decode bs := do pure { ptr := ← Zig.Enc.decodeAt bs 0, vtable := ← Zig.Enc.decodeAt bs 8 }

structure State where
  used_list : Option (Zig.Ptr)
  free_list : Option (Zig.Ptr)
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc State where
  size := 16
  align := 8
  encode v := Zig.Enc.fields 16 [(0, Zig.Enc.encode v.used_list), (8, Zig.Enc.encode v.free_list)]
  decode bs := do pure { used_list := ← Zig.Enc.decodeAt bs 0, free_list := ← Zig.Enc.decodeAt bs 8 }

structure Arena where
  child_allocator : Alloc
  state : State
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Arena where
  size := 32
  align := 8
  encode v := Zig.Enc.fields 32 [(0, Zig.Enc.encode v.child_allocator), (16, Zig.Enc.encode v.state)]
  decode bs := do pure { child_allocator := ← Zig.Enc.decodeAt bs 0, state := ← Zig.Enc.decodeAt bs 16 }

/-- The list heads, loaded as one struct from two atomic words. -/
theorem load_state (p : Ptr) (a b : Option Ptr) :
    FTotalTriple (aptsE p a ⋆ aptsE (p.add 8) b) (load State 8 p)
      (fun r => ⟪r = ⟨a, b⟩⟫ ⋆ aptsE p a ⋆ aptsE (p.add 8) b) := by
  fsym

/-- The list heads, stored as one struct into two atomic words (the arena's `reset`): each word
keeps its tag. -/
theorem store_state (p : Ptr) (a b : Option Ptr) (s : State) :
    FTotalTriple (aptsE p a ⋆ aptsE (p.add 8) b) (store 8 p s)
      (fun _ => aptsE p s.used_list ⋆ aptsE (p.add 8) s.free_list) := by
  fsym

/-- The arena's header, loaded whole: the child allocator from its region (whose bytes decode to
it), the list heads from their words, at the arena's pointer plus 16 and 24. -/
theorem load_arena (ctx : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) (c : Alloc)
    (a b : Option Ptr) (hs : bs.size = 16) (hc : Enc.decode bs = pure c) :
    FTotalTriple (up (regionIn ctx A S K 8 bs) ⋆ aptsE (ctx.add 16) a ⋆ aptsE (ctx.add 24) b)
      (load Arena 8 ctx)
      (fun r => ⟪r = ⟨c, ⟨a, b⟩⟩⟫ ⋆ up (regionIn ctx A S K 8 bs) ⋆ aptsE (ctx.add 16) a ⋆
        aptsE (ctx.add 24) b) := by
  fsym

/-- The arena's `reset`: its list heads (at the arena's pointer plus 16) stored empty. -/
theorem reset_state (ctx : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) (a b : Option Ptr) :
    FTotalTriple (up (regionIn ctx A S K 8 bs) ⋆ aptsE (ctx.add 16) a ⋆ aptsE (ctx.add 24) b)
      (store 8 (ctx.add 16) ({ used_list := none, free_list := none } : State))
      (fun _ => up (regionIn ctx A S K 8 bs) ⋆ aptsE (ctx.add 16) (none : Option Ptr) ⋆
        aptsE (ctx.add 24) (none : Option Ptr)) := by
  fsym

structure Lock where
  state : BitVec 64
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Lock where
  size := 8
  align := 8
  encode v := Zig.Enc.fields 8 [(0, Zig.Enc.encode v.state)]
  decode bs := do pure { state := ← Zig.Enc.decodeAt bs 0 }

structure Hdr where
  items : Zig.Slice
  capacity : BitVec 64
  pointer_stability : Lock
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Enc Hdr where
  size := 32
  align := 8
  encode v := Zig.Enc.fields 32 [(0, Zig.Enc.encode v.items), (16, Zig.Enc.encode v.capacity), (24, Zig.Enc.encode v.pointer_stability)]
  decode bs := do pure { items := ← Zig.Enc.decodeAt bs 0, capacity := ← Zig.Enc.decodeAt bs 16, pointer_stability := ← Zig.Enc.decodeAt bs 24 }

/-- A list header held as one atom per field, loaded whole. -/
theorem load_hdr (p : Ptr) (s : Slice) (c : BitVec 64) (l : Lock) :
    FTotalTriple (up (pts p 8 s) ⋆ up (pts (p.add 16) 8 c) ⋆ up (pts (p.add 24) 8 l)) (load Hdr 8 p)
      (fun r => ⟪r = ⟨s, c, l⟩⟫ ⋆ up (pts p 8 s) ⋆ up (pts (p.add 16) 8 c) ⋆
        up (pts (p.add 24) 8 l)) := by
  fsym

end SepAuto.Parts
