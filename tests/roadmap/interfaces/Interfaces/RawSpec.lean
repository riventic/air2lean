import Interfaces.Raw
import ZigLean.Mem.WidthLemmas
import ZigLean.Sep.Full.Wrappers
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Block
import ZigLean.Sep.Full.AutoPrim
import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Try
import ZigLean.Sep.Full.Region
import ZigLean.Sep.Full.Slice

/-!
# The lower-level allocator entry points, for every allocator (M04)

`tests/roadmap/interfaces/raw.zig` calls the lower-level entry points of a caller-supplied
`std.mem.Allocator` directly: `rawAlloc` (`take`), `rawResize` (`fit`), `rawRemap` (`move`) and
`rawFree` (`give`), at alignment 4, and the in-place `resize` of a `[]u32` (`refit`). The raw
calls are the vtable calls with the byte length and the alignment as the client gives them, so
the contract's preconditions are the client's premises, and its postconditions the client's
(`FAllocInv.allocPost`, `resizePost`, `remapPost`):

* `take_spec`: `0 < n` bytes that the allocator takes (`fits`): a grant of `n` bytes at
  alignment `2 ^ 2`, or `null` and the fee back;
* `fit_spec`, `move_spec`: the memory is a grant at alignment `2 ^ 2` and at its own length, and
  `0 < n`: the grant of `n` bytes that keeps the common prefix (in place; in place or moved), or
  `false`/`null` and the old grant unchanged;
* `give_spec`: the memory is a grant at alignment `2 ^ 2` and at its own length: the fee back;
* `refit_spec`: the in-place `resize` of a nonempty `[]u32` to `0 < n` items is `fit` at
  `n * 4` bytes; a byte count that does not fit a `usize` is `false`.

`Interfaces/RawNeg.lean` has the same statements without one precondition each (a length of 0,
another alignment or length than the grant's); `interfaces/check.sh` requires that each stops at
that precondition. As in `SentinelSpec`, the entries are the environment's (`Ext`, premise
EXT-05), and the theorems assume only `CAllocSpec`. These are `CTriple`s (partial correctness, no
panic): the contract is one. They hold over the translations of Zig 0.17.1, 0.16.0, 0.15.2 and
0.14.1.
-/

namespace Interfaces.RawSpec

open Zig Zig.Full Zig.Full.FAssn Interfaces.Raw

/-- The alignment argument of the generated entries, from its log2. -/
def al (k : Nat) : mem_Alignment := ⟨BitVec.ofNat 6 k⟩

variable [Ext]

/-- The environment's allocator entries: `Ext.call0` (`alloc`), `Ext.call1` (`resize`),
`Ext.call2` (`remap`) and `Ext.call3` (`free`). -/
def env : AllocEnv Tgt where
  alloc := fun f a => Ext.call0 f a.1 a.2.1 (al a.2.2.1) a.2.2.2
  resize := fun f a => Ext.call1 f a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2
  remap := fun f a => Ext.call2 f a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2
  free := fun f a => Ext.call3 f a.1 a.2.1 (al a.2.2.1) a.2.2.2

variable (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (φ : Frac)

/-- **`take`** (`rawAlloc` of `n` bytes at alignment 4) for every allocator. -/
theorem take_spec (n : BitVec 64) (hn : 0 < n.toNat) (hfit : I.fits n.toNat 2)
    (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) (take ⟨ctx, vtp⟩ n)
      (fun r => I.allocPost n.toNat 2 φ r ⋆ vtR vtp fns.toList) := by
  fsym [CAllocSpec.alloc h]

/-- **`fit`** (`rawResize` of a grant to `n` bytes) for every allocator. -/
theorem fit_spec (m : Slice) (n : BitVec 64) (bs : Array Byte) (hlen : m.len.toNat = bs.size)
    (hpos : 0 < bs.size) (hn : 0 < n.toNat) (hfit : I.fits n.toNat 2)
    (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted m.ptr 2 φ bs ⋆ vtR vtp fns.toList)) (fit ⟨ctx, vtp⟩ m n)
      (fun r => I.resizePost m.ptr 2 φ bs n.toNat r ⋆ vtR vtp fns.toList) := by
  fsym [CAllocSpec.resize_granted h]

/-- **`move`** (`rawRemap` of a grant to `n` bytes) for every allocator. -/
theorem move_spec (m : Slice) (n : BitVec 64) (bs : Array Byte) (hlen : m.len.toNat = bs.size)
    (hpos : 0 < bs.size) (hn : 0 < n.toNat) (hfit : I.fits n.toNat 2)
    (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted m.ptr 2 φ bs ⋆ vtR vtp fns.toList)) (move ⟨ctx, vtp⟩ m n)
      (fun r => I.remapPost m.ptr 2 φ bs n.toNat r ⋆ vtR vtp fns.toList) := by
  fsym [CAllocSpec.remap h]

/-- **`give`** (`rawFree` of a grant) for every allocator: the fee back. -/
theorem give_spec (m : Slice) (bs : Array Byte) (hlen : m.len.toNat = bs.size)
    (hpos : 0 < bs.size) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted m.ptr 2 φ bs ⋆ vtR vtp fns.toList)) (give ⟨ctx, vtp⟩ m)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  fsym [CAllocSpec.free' h]

/-- **`refit`** (the in-place `resize` of a nonempty `[]u32` to `0 < n` items) for every
allocator: `fit` at `n * 4` bytes. -/
theorem refit_spec (m : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : m.len.toNat * 4 = bs.size) (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size)
    (hn : 0 < n.toNat) (hfit : I.fits (n.toNat * 4) 2)
    (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted m.ptr 2 φ bs ⋆ vtR vtp fns.toList)) (refit ⟨ctx, vtp⟩ m n)
      (fun r => I.resizePost m.ptr 2 φ bs (n.toNat * 4) r ⋆ vtR vtp fns.toList) := by
  unfold refit mem_Allocator_resize__anon_270641f5f95c
  fsym [CAllocSpec.resize_granted h]

end Interfaces.RawSpec
