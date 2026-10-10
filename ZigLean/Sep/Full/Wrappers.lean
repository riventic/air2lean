import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.AllocSpec.Wrappers

/-!
# The `std.mem.Allocator` wrapper contracts over `FAllocSpec`

Every wrapper contract of `ZigLean/Sep/AllocSpec/Wrappers.lean` is proved for an arbitrary
`Logic`. `FAllocSpec.toLegacy` gives a full-state allocator specification whose tokens are legacy
assertions (`LegacyTokens J I O`) as a legacy `AllocSpec` in `FLogic.legacy FL O`: the full-state
logic `FL` with the allocator state `O` framed around every assertion. So each contract holds in
the full-state logic. The statements below spell out the common ones: precondition `O ⋆ up P`,
postcondition `O ⋆ up Q`, for the legacy `P` and `Q` of the contract.

Both translated allocators have legacy tokens: the FixedBufferAllocator (`I.toFull`, `O = emp`,
`AllocInv.toFull_legacy`) and the page allocator (`PageSpec.inv own`, `O = own`).
-/

namespace Zig
namespace Full

open FAssn Wrap

variable {FL : FLogic} {vt : RawVTable} {ctx : Ptr} {J : FAllocInv} {I : AllocInv} {O : FAssn}

theorem FAllocSpec.allocBytes_spec (h : FAllocSpec FL vt ctx J) (hJ : LegacyTokens J I O)
    (k : Nat) (n ra : BitVec 64) (hk : k < 64) (hfit : Fits I n.toNat k) :
    FL.T (O ⋆ up I.own) (Wrap.allocBytes vt ctx k n ra)
      (fun v => O ⋆ up (allocResult I k n.toNat v)) :=
  Wrap.allocBytes_spec (h.toLegacy hJ) k n ra hk hfit

theorem FAllocSpec.allocSlice_spec (h : FAllocSpec FL vt ctx J) (hJ : LegacyTokens J I O)
    (size k : Nat) (n : BitVec 64) (hk : k < 64) (hs : size < 2 ^ 64)
    (hfit : Fits I (size * n.toNat) k) :
    FL.T (O ⋆ up I.own) (Wrap.allocSlice vt ctx size k n)
      (fun v => O ⋆ up (sliceResult I k n (size * n.toNat) v)) :=
  Wrap.allocSlice_spec (h.toLegacy hJ) size k n hk hs hfit

theorem FAllocSpec.create_spec (h : FAllocSpec FL vt ctx J) (hJ : LegacyTokens J I O)
    (size k : Nat) (hk : k < 64) (hs : size < 2 ^ 64) (hfit : Fits I size k) :
    FL.T (O ⋆ up I.own) (Wrap.create vt ctx size k) (fun v => O ⋆ up (allocResult I k size v)) :=
  Wrap.create_spec (h.toLegacy hJ) size k hk hs hfit

theorem FAllocSpec.destroy_spec (h : FAllocSpec FL vt ctx J) (hJ : LegacyTokens J I O)
    (size k : Nat) (p : Ptr) (bs : Array Byte) (hk : k < 64) (hsz : bs.size = size)
    (hs : size < 2 ^ 64) :
    FL.T (O ⋆ up (I.own ∗ owned I k p bs)) (Wrap.destroy vt ctx size k p)
      (fun _ => O ⋆ up I.own) :=
  Wrap.destroy_spec (h.toLegacy hJ) size k p bs hk hsz hs

theorem FAllocSpec.free_spec (h : FAllocSpec FL vt ctx J) (hJ : LegacyTokens J I O)
    (size k : Nat) (s : Slice) (bs : Array Byte) (hk : k < 64)
    (hsz : bs.size = s.len.toNat * size) (hs : bs.size < 2 ^ 64) :
    FL.T (O ⋆ up (I.own ∗ owned I k s.ptr bs)) (Wrap.free vt ctx size k s)
      (fun _ => O ⋆ up I.own) :=
  Wrap.free_spec (h.toLegacy hJ) size k s bs hk hsz hs

theorem FAllocSpec.realloc_spec (h : FAllocSpec FL vt ctx J) (hJ : LegacyTokens J I O)
    (size k : Nat) (old : Slice) (newN : BitVec 64) (bs : Array Byte) (hk : k < 64)
    (hsize : 0 < size) (hs : size < 2 ^ 64) (hsz : bs.size = old.len.toNat * size)
    (hbs : bs.size < 2 ^ 64) (hfit : Fits I (size * newN.toNat) k) (hsep : GrantSep I k) :
    FL.T (O ⋆ up (I.own ∗ owned I k old.ptr bs)) (Wrap.realloc vt ctx size k old newN)
      (fun v => O ⋆ up (reallocResult I k size old newN bs v)) :=
  Wrap.realloc_spec (h.toLegacy hJ) size k old newN bs hk hsize hs hsz hbs hfit hsep

end Full
end Zig
