import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.AutoPrim

/-!
# `fsym` on small programs (`docs/proof-automation.md`)

A walk through loads, checked arithmetic and stores; an assertion-level `if` decided by the
facts; returns that carve a region and raise a share's bound. The programs are written by hand
in the shape the translator generates.
-/

namespace SepAuto.Walk

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- Add `n` to the word at `ctx`, checked; return the new value. -/
def bump (ctx : Ptr) (n : BitVec 64) : MemM (BitVec 64) := do
  let e ← Zig.load (BitVec 64) 8 ctx
  let e' ← StateT.lift (Zig.add false e n)
  Zig.store (α := BitVec 64) 8 ctx e'
  pure e'

theorem bump_spec (ctx : Ptr) (e : Nat) (n : BitVec 64) (h : e + n.toNat < 2 ^ 64) :
    FTotalTriple (up (pts ctx 8 (BitVec.ofNat 64 e))) (bump ctx n)
      (fun r => ⟪r.toNat = e + n.toNat⟫ ⋆ up (pts ctx 8 (BitVec.ofNat 64 (e + n.toNat)))) := by
  fsym

/-- An `if` of the precondition that the facts decide. -/
theorem ite_pre (ctx : Ptr) (e : Nat) (n : BitVec 64) (X : FAssn) (h : e + n.toNat < 2 ^ 64) (he : 0 < e) :
    FTotalTriple (up (pts ctx 8 (BitVec.ofNat 64 e)) ⋆ (if e = 0 then X else emp)) (bump ctx n)
      (fun _ => up (pts ctx 8 (BitVec.ofNat 64 (e + n.toNat)))) := by
  fsym

/-- A return that carves a region: a prefix of `k` bytes, and the rest at `p + k` with any bytes
of the right size. -/
theorem carve (p : Ptr) (A S : Nat) (K : BlockKind) (bs : Array Byte) (k : Nat) (hk : k ≤ bs.size)
    (b : BlockId) (hb : p.block = some b) :
    FTotalTriple (up (regionIn p A S K 1 bs)) (pure () : MemM Unit)
      (fun _ => up (regionIn p A S K 1 (bs.extract 0 k)) ⋆
        FAssn.ex fun t : Array Byte => ⟪t.size = bs.size - k⟫ ⋆ up (regionIn (p.add k) A S K 1 t)) := by
  fsym

/-- A return that raises a share's bound with another share of the block (fractions kept). -/
theorem raise (b : BlockId) (q₁ q₂ : Frac) (k₁ k₂ k : Nat) (h : k ≤ k₂) :
    FTotalTriple (bshare b q₁ k₁ ⋆ bshare b q₂ k₂) (pure () : MemM Unit)
      (fun _ => bshare b q₁ k ⋆ FAssn.ex fun q => bshare b q k₂) := by
  fsym

/-- A precondition that holds of `some` only. -/
def onlySome (p : Ptr) : Option (BitVec 32) → FAssn
  | none => ⟪False⟫
  | some v => up (pts p 4 v)

/-- The `none` case is unreachable (its precondition is `⟪False⟫` after the split): closed,
although its command has no rule. -/
theorem false_pre (p : Ptr) (o : Option (BitVec 32)) :
    FTotalTriple (onlySome p o)
      (match o with
        | none => Zig.load (BitVec 64) 8 p
        | some _ => pure 0)
      (fun _ => FAssn.ex fun v : BitVec 32 => up (pts p 4 v)) := by
  fsym

/-- An item of a vector value (`Zig.vindex`, `AutoPrim.vindex_step`). -/
theorem vindex_item (a : Vector (BitVec 64) 2) :
    FTotalTriple emp (StateT.lift (Zig.vindex a (1 : BitVec 64)) : MemM (BitVec 64))
      (fun r => ⟪r = a[1]⟫) := by
  fsym

end SepAuto.Walk
