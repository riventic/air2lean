import AllocFba.AutoDefs
import ZigLean.Sep.Full.Auto
namespace AllocFba.FBA2
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto Gen

set_option maxHeartbeats 2000000 in
theorem fresize (ctx : Ptr) (B : FBuf) (s : Slice) (k : Nat) (n ra : BitVec 64)
    (bs : Array Byte) (hn : 0 < n.toNat) (hfit : (finv ctx B).fits n.toNat k) (hlen : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) :
    FTotalTriple ((finv ctx B).own ⋆ (finv ctx B).granted s.ptr k bs) (impl.resize ctx s k n ra)
      ((finv ctx B).resizePost s.ptr k bs n.toNat) := by
  fsym
