import AllocFba.AutoDefs
import ZigLean.Sep.Full.Auto
namespace AllocFba.FBA2
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto Gen

theorem fresize (ctx : Ptr) (B : FBuf) (s : Slice) (k : Nat) (n ra : BitVec 64) (A S : Nat)
    (K : BlockKind) (q q' : Frac) (tl : Array Byte) (hk : k < 64) (hn : 0 < n.toNat)
    (hfit : (finv ctx B).fits n.toNat k) (hpos : 0 < s.len.toNat) (hq : q'.val ≤ q.val)
    (hsh : n.toNat < s.len.toNat → q' = q) :
    FTotalTriple ((finv ctx B).own ⋆ ((finv ctx B).held s.ptr s.len.toNat k A S K q q' ⋆
      FAllocInv.relBytes s.ptr A S K n.toNat s.len.toNat tl))
      (impl.resize ctx s k n ra) ((finv ctx B).rresizePost s.ptr k s.len.toNat n.toNat A S K q q' tl) := by
  fsym
