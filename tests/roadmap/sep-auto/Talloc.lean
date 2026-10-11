import AllocFba.AutoDefs
import ZigLean.Sep.Full.Auto
namespace AllocFba.FBA2
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto Gen

theorem falloc (ctx : Ptr) (B : FBuf) (n : BitVec 64) (k : Nat) (ra : BitVec 64)
    (hn : 0 < n.toNat) (hk : k < 64) (hfit : (finv ctx B).fits n.toNat k) :
    FTotalTriple (fown ctx B) (impl.alloc ctx n k ra) ((finv ctx B).allocPost n.toNat k) := by
  fsym
