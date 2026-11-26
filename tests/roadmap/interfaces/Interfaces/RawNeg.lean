import Interfaces.RawSpec

/-!
# Negative check: a raw call outside the contract's preconditions has no proof (M04)

Each theorem below is a statement of `Interfaces/RawSpec.lean` without one precondition of
`CAllocSpec`, with the same proof. None of them elaborates: `interfaces/check.sh` requires an
error in every one, and that the walk stops at the missing precondition (the goal it leaves, or
the vtable call it has no rule for). This file is not part of a build.

* `take_zero`: `rawAlloc` of a length that may be 0 (`0 < len`);
* `fit_zero`, `move_zero`: `rawResize`/`rawRemap` to a length that may be 0;
* `give_other_length`: `rawFree` of a slice whose length is not known to be the grant's;
* `give_other_alignment`, `fit_other_alignment`: `rawFree`/`rawResize` at alignment 4 of a grant
  at alignment 1.
-/

namespace Interfaces.RawNeg

open Zig Zig.Full Zig.Full.FAssn Interfaces.Raw Interfaces.RawSpec

variable [Ext] (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (φ : Frac)

theorem take_zero (n : BitVec 64) (hfit : I.fits n.toNat 2)
    (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) (take ⟨ctx, vtp⟩ n)
      (fun r => I.allocPost n.toNat 2 φ r ⋆ vtR vtp fns.toList) := by
  fsym [CAllocSpec.alloc h]

theorem fit_zero (m : Slice) (n : BitVec 64) (bs : Array Byte) (hlen : m.len.toNat = bs.size)
    (hpos : 0 < bs.size) (hfit : I.fits n.toNat 2)
    (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted m.ptr 2 φ bs ⋆ vtR vtp fns.toList)) (fit ⟨ctx, vtp⟩ m n)
      (fun r => I.resizePost m.ptr 2 φ bs n.toNat r ⋆ vtR vtp fns.toList) := by
  fsym [CAllocSpec.resize_granted h]

theorem move_zero (m : Slice) (n : BitVec 64) (bs : Array Byte) (hlen : m.len.toNat = bs.size)
    (hpos : 0 < bs.size) (hfit : I.fits n.toNat 2)
    (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted m.ptr 2 φ bs ⋆ vtR vtp fns.toList)) (move ⟨ctx, vtp⟩ m n)
      (fun r => I.remapPost m.ptr 2 φ bs n.toNat r ⋆ vtR vtp fns.toList) := by
  fsym [CAllocSpec.remap h]

theorem give_other_length (m : Slice) (bs : Array Byte) (hpos : 0 < bs.size)
    (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted m.ptr 2 φ bs ⋆ vtR vtp fns.toList)) (give ⟨ctx, vtp⟩ m)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  fsym [CAllocSpec.free' h]

theorem give_other_alignment (m : Slice) (bs : Array Byte) (hlen : m.len.toNat = bs.size)
    (hpos : 0 < bs.size) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted m.ptr 0 φ bs ⋆ vtR vtp fns.toList)) (give ⟨ctx, vtp⟩ m)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  fsym [CAllocSpec.free' h]

theorem fit_other_alignment (m : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : m.len.toNat = bs.size) (hpos : 0 < bs.size) (hn : 0 < n.toNat)
    (hfit : I.fits n.toNat 2) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted m.ptr 0 φ bs ⋆ vtR vtp fns.toList)) (fit ⟨ctx, vtp⟩ m n)
      (fun r => I.resizePost m.ptr 0 φ bs n.toNat r ⋆ vtR vtp fns.toList) := by
  fsym [CAllocSpec.resize_granted h]

end Interfaces.RawNeg
