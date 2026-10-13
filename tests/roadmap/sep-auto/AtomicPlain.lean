import ZigLean.Sep.Full.Auto

/-!
# Plain accesses of atomic words (`ZigLean/Sep/Full/AtomicPlain.lean`)

A word that atomic ops use is also read and written by plain loads and stores (the arena's list
heads, a node's packed size word). `fsym` walks them with the word's own rules, and the word keeps
its atomic tag (`apts`/`aptsE` after the access), so the atomic ops still apply.
-/

namespace SepAuto.AtomicPlain

open Zig Zig.Full Zig.Full.FAssn

/-- A packed struct over a 64-bit word, as the translator writes it. -/
structure Size where
  resizing : Bool
  «_» : BitVec 63
  deriving Repr, Inhabited, DecidableEq

instance : Zig.Packed Size 64 where
  toBits v := ((Zig.Packed.toBits v.resizing).setWidth 64 <<< 0) ||| ((Zig.Packed.toBits v.«_»).setWidth 64 <<< 1)
  ofBits b := { resizing := Zig.Packed.get b 0, «_» := Zig.Packed.get b 1 }

instance : Zig.Enc Size where
  size := 8
  align := 8
  encode v := Zig.Enc.encode (Zig.Packed.toBits v)
  decode bs := do
    let b : BitVec 64 ← Zig.Enc.decode bs
    Zig.Packed.ofBits? b

/-- A plain load and store of an atomic pointer word (a list head): the tag stays. -/
theorem head_swap (p : Ptr) (x y : Option Ptr) :
    FTotalTriple (aptsE p x ⋆ aptsE (p.add 8) y)
      (do let a ← load (Option Ptr) 8 p; store 8 (p.add 8) a; store 8 p (none : Option Ptr))
      (fun _ => aptsE p (none : Option Ptr) ⋆ aptsE (p.add 8) x) := by
  fsym

/-- A plain load and store of an atomic word. -/
theorem word_inc (p : Ptr) (v : BitVec 64) :
    FTotalTriple (apts p v) (do let a ← load (BitVec 64) 8 p; store 8 p (a + 1))
      (fun _ => apts p (v + 1)) := by
  fsym

/-- A packed struct over an atomic word: loaded from the word's bits, stored as its bits. -/
theorem packed_load (p : Ptr) (v : BitVec 64) :
    FTotalTriple (apts p v) (load Size 8 p)
      (fun r => ⟪r = Packed.ofBits v⟫ ⋆ apts p v) := by
  fsym

theorem packed_store (p : Ptr) (v : BitVec 64) (s : Size) :
    FTotalTriple (apts p v) (store 8 p s) (fun _ => apts p (Packed.toBits s)) := by
  fsym

end SepAuto.AtomicPlain
