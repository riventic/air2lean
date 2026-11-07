import Proofs.Lists.Open
import ZigLean.Sep.Full.Ghost
import ZigLean.Sep.Full.AutoAttr
import ZigLean.Sep.Full.ListSeg

set_option linter.unusedVariables false

namespace Lists.Open
open Zig Zig.Full Zig.Full.FAssn

abbrev reverse.loop6.node (V : Type) (D : Zig.Ptr → V → FAssn) (p : Zig.Ptr) (v : V) (q : Option Zig.Ptr) : FAssn :=
  up (pts p 8 q) ⋆ D p v

@[fsym_inv] def reverse.loop6.inv (V : Type) (D : Zig.Ptr → V → FAssn) (xs : List V) (s0 : reverseLocals) (s : reverseLocals) (n : Nat) : FAssn :=
  FAssn.ex fun ys : List V => FAssn.ex fun zs : List V =>
    ⟪xs = ys.reverse ++ zs ∧
      zs.length = n⟫ ⋆
    listSeg (reverse.loop6.node V D) s.prev none ys ⋆
    listSeg (reverse.loop6.node V D) s.cur none zs ⋆
    plain

@[fsym_inv] def reverse.loop6.post (V : Type) (D : Zig.Ptr → V → FAssn) (xs : List V) (s0 : reverseLocals) (r : reverseExit × reverseLocals) : FAssn :=
  ⟪r.1 = reverseExit.br5⟫ ⋆
    listSeg (reverse.loop6.node V D) r.2.prev none xs.reverse ⋆
    plain

abbrev sum.loop6.node (X : Zig.Ptr → FAssn) (p : Zig.Ptr) (v : BitVec 32) (q : Option Zig.Ptr) : FAssn :=
  up (pts p 8 q) ⋆ up (pts (p.add 8) 4 v) ⋆ X p

@[fsym_inv] def sum.loop6.inv (X : Zig.Ptr → FAssn) (xs : List (BitVec 32)) (s0 : sumLocals) (s : sumLocals) (n : Nat) : FAssn :=
  FAssn.ex fun ys : List (BitVec 32) => FAssn.ex fun zs : List (BitVec 32) =>
    ⟪xs = ys ++ zs ∧
      zs.length = n ∧
      s.s.toNat = s0.s.toNat + (ys.map BitVec.toNat).sum ∧
      s0.s.toNat + (xs.map BitVec.toNat).sum < 2 ^ 64⟫ ⋆
    listSeg (sum.loop6.node X) s0.p s.p ys ⋆
    listSeg (sum.loop6.node X) s.p none zs ⋆
    plain

@[fsym_inv] def sum.loop6.post (X : Zig.Ptr → FAssn) (xs : List (BitVec 32)) (s0 : sumLocals) (r : sumExit × sumLocals) : FAssn :=
  ⟪r.1 = sumExit.br5 ∧
      r.2.s.toNat = s0.s.toNat + (xs.map BitVec.toNat).sum⟫ ⋆
    listSeg (sum.loop6.node X) s0.p none xs ⋆
    plain

end Lists.Open
