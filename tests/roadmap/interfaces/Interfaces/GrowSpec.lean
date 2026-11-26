import Interfaces.Grow
import ZigLean.Mem.WidthLemmas
import ZigLean.Sep.Full.SentinelBuf
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Block
import ZigLean.Sep.Full.AutoPrim
import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Try
import ZigLean.Sep.Full.Region
import ZigLean.Sep.Full.Slice

/-!
# Growth of a sentinel slice itself, for every allocator (M04)

`tests/roadmap/interfaces/grow.zig` calls `realloc`, `remap` and the in-place `resize` of a
`std.mem.Allocator` with a `[:0]T` itself, for `T` = `u8` and `u32`, and stores the sentinel at
the new length. Zig 0.17's std counts the sentinel item of the old slice in each of them
(`mem.absorbSentinel`): the memory it hands to the vtable is the whole grant of
`(len + 1) * sz` bytes. The statements are the generic ones of
`ZigLean/Sep/Full/SentinelBuf.lean` (`appended`, `resized`, `moved`, `fitted`, for every item
size, alignment and sentinel bytes); an instance supplies the size of its encoding and the walk of
its code by `fsym`. As in `SentinelSpec`, every call through the allocator reaches the environment
(`Ext`, premise EXT-05), so the theorems assume only the contract `CAllocSpec` of the
environment's allocator at the vtable `fns` (`CVTable.env`) with invariant `I`, here with all
four entries.

* `append*_grant`, `resize*_grant` (`realloc`): as `SentinelSpec`'s, for a nonempty slice; on
  `error.OutOfMemory` the old grant unchanged;
* `move*_grant` (`remap`): `n` items and the sentinel, in place or moved, or `null` and the old
  grant unchanged;
* `fit*_grant` (the in-place `resize`, the contract's `resize` entry): `true` and `n` items and
  the sentinel at the same pointer, or `false` and the old grant unchanged.

**An empty sentinel slice leaks in `realloc`** (`realloc*_empty`): `reallocAdvanced` takes
`old_mem.len == 0` for "nothing allocated" and allocates anew, but an empty `[:0]T` is a grant of
one item (its sentinel). The theorem states what the code does: the new buffer, and the old grant
still held. So `append*_grant` and `resize*_grant` ask for a nonempty slice.

**Versions.** These proofs hold over the Zig 0.17.1 translation only. Zig 0.16.0 rejects the
calls at compile time. Zig 0.15.2 and 0.14.1 compile them, and their std hands the vtable
`mem.sliceAsBytes(old_mem)`: `len * sz` bytes of a grant of `(len + 1) * sz` bytes. That is
outside the contract (`CAllocSpec.remap`, `resize`, `free`: the memory is the grant, at its
length), so there is no proof from `CAllocSpec` there. It is a bug of that std: the
size-checking `std.testing.allocator` of stock 0.15.2 and 0.14.1 reports the mismatch
(`docs/upstream/realloc-empty-sentinel-leak.md`, "Related"). `interfaces/check.sh` pins that these
proofs stop at that precondition on both versions.

These are `CTriple`s (partial correctness, no panic): the contract `CAllocSpec` is one.
-/

namespace Interfaces.GrowSpec

open Zig Zig.Full Zig.Full.FAssn Zig.Full.SentinelBuf Interfaces.Grow

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

/-! ## `u8`: 1 byte at alignment `2 ^ 0` -/

/-- `a.free(s)` of a `[:0]u8`: the grant of `len + 1` bytes goes back. -/
theorem free8_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat + 1 = bs.size)
    (hs : bs.size < 2 ^ 64) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_0ba161b45e0a ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_0ba161b45e0a
  fsym [CAllocSpec.free' h]

/-- `a.realloc(s, n)` of a nonempty `[:0]u8` (`reallocAdvanced` over the absorbed slice: `remap`,
else `alloc`, copy, `free`; `n = 0` frees): `n` bytes that keep the common prefix of the
`len + 1` old ones. -/
theorem realloc8_spec (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat + 1 = bs.size) (hs : bs.size < 2 ^ 64) (hpos : 0 < s.len.toNat)
    (hfit : I.fits n.toNat 0) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_585fc7d079fa ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.reallocResult 0 φ s.ptr bs n n.toNat r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  unfold mem_Allocator_realloc__anon_585fc7d079fa mem_Allocator_reallocAdvanced__anon_b1876625f38f
  fsym [CAllocSpec.alloc h, CAllocSpec.remap h, free8_spec ctx vtp fns I φ (h := h),
    CAllocSpec.free' h, Norm.mulWithOverflow_one]

/-- **The leak**: `a.realloc(s, n)` of an empty `[:0]u8` allocates `n` bytes and leaves the old
grant (the sentinel byte) as it was. -/
theorem realloc8_empty (s : Slice) (n : BitVec 64) (bs : Array Byte) (hlen : s.len.toNat = 0)
    (hfit : I.fits n.toNat 0) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_585fc7d079fa ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ (I.sliceResult 0 φ n n.toNat r ⋆
        vtR vtp fns.toList)) ⋆ plain) := by
  unfold mem_Allocator_realloc__anon_585fc7d079fa mem_Allocator_reallocAdvanced__anon_b1876625f38f
  fsym [CAllocSpec.alloc h, Norm.mulWithOverflow_one]

/-- **`append`** through `realloc` of the `[:0]u8` itself, for every allocator: one more item `c`,
the sentinel after it; or the old buffer. -/
theorem append8_grant (s : Slice) (c : BitVec 8) (bs : Array Byte)
    (hlen : s.len.toNat + 1 = bs.size) (hs : s.len.toNat + 2 < 2 ^ 64) (hpos : 0 < s.len.toNat)
    (hfit : I.fits (s.len.toNat + 2) 0) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u8_append ⟨ctx, vtp⟩ s c)
      (fun r => I.own ⋆ (appended I φ 0 1 (Enc.encode (0 : BitVec 8)) (Enc.encode c) s.ptr bs
        s.len.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  append_grant (by fsym_arith) (by fsym_arith) (by omega) (by
    fsym [realloc8_spec ctx vtp fns I φ (h := h)])

/-- **`resize`** through `realloc` of the `[:0]u8` itself, for every allocator: `n` items, the
retained bytes, the sentinel at `n`; or the old buffer. -/
theorem resize8_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat + 1 = bs.size) (hs : bs.size < 2 ^ 64) (hpos : 0 < s.len.toNat)
    (hn : n.toNat + 1 < 2 ^ 64) (hfit : I.fits (n.toNat + 1) 0)
    (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u8_resize ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (resized I φ 0 1 (Enc.encode (0 : BitVec 8)) s.ptr bs s.len.toNat n r ⋆
        vtR vtp fns.toList) ⋆ plain) :=
  resize_grant (by fsym_arith) (by omega) (by
    fsym [realloc8_spec ctx vtp fns I φ (h := h)])

/-- **`move`** (`remap` of the `[:0]u8` itself) for every allocator: `n` items and the sentinel,
in place or moved; or `null` and the old buffer. -/
theorem move8_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat + 1 = bs.size) (hs : bs.size < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits (n.toNat + 1) 0) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ vtR vtp fns.toList) ⋆ plain)
      (Buf_u8_move ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (moved I φ 0 1 (Enc.encode (0 : BitVec 8)) s.ptr bs s.len.toNat n r ⋆
        vtR vtp fns.toList) ⋆ plain) :=
  move_grant (by fsym_arith) (by omega) (by
    unfold Buf_u8_move mem_Allocator_remap__anon_3903ca12077f
    fsym [CAllocSpec.remap h, Norm.mulWithOverflow_one])

/-- **`fit`** (the in-place `resize` of the `[:0]u8` itself) for every allocator: `true` and `n`
items and the sentinel at the same pointer; or `false` and the old buffer. -/
theorem fit8_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat + 1 = bs.size) (hs : bs.size < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits (n.toNat + 1) 0) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ vtR vtp fns.toList) ⋆ plain)
      (Buf_u8_fit ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (fitted I φ 0 1 (Enc.encode (0 : BitVec 8)) s.ptr bs s.len.toNat n.toNat
        r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  fit_grant (by fsym_arith) (by omega) (by
    unfold Buf_u8_fit mem_Allocator_resize__anon_d7f27f70af0f
    fsym [CAllocSpec.resize_granted h, Norm.mulWithOverflow_one])

/-! ## `u32`: 4 bytes at alignment `2 ^ 2` -/

/-- `a.free(s)` of a `[:0]u32`: the grant of `(len + 1) * 4` bytes goes back. -/
theorem free32_spec (s : Slice) (bs : Array Byte) (hlen : (s.len.toNat + 1) * 4 = bs.size)
    (hs : bs.size < 2 ^ 64) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_85944fd5a0eb ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_85944fd5a0eb
  fsym [CAllocSpec.free' h]

/-- `a.realloc(s, n)` of a nonempty `[:0]u32`: `n * 4` bytes that keep the common prefix of the
`(len + 1) * 4` old ones. -/
theorem realloc32_spec (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 4 = bs.size) (hs : bs.size < 2 ^ 64) (hpos : 0 < s.len.toNat)
    (hfit : I.fits (n.toNat * 4) 2) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_9cee5a678d80 ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.reallocResult 2 φ s.ptr bs n (n.toNat * 4) r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  unfold mem_Allocator_realloc__anon_9cee5a678d80 mem_Allocator_reallocAdvanced__anon_0e4c9b513eeb
  fsym [CAllocSpec.alloc h, CAllocSpec.remap h, free32_spec ctx vtp fns I φ (h := h),
    CAllocSpec.free' h]

/-- **The leak**: `a.realloc(s, n)` of an empty `[:0]u32` allocates `n` items and leaves the old
grant (the sentinel item) as it was. -/
theorem realloc32_empty (s : Slice) (n : BitVec 64) (bs : Array Byte) (hlen : s.len.toNat = 0)
    (hfit : I.fits (n.toNat * 4) 2) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_9cee5a678d80 ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ (I.sliceResult 2 φ n (n.toNat * 4) r ⋆
        vtR vtp fns.toList)) ⋆ plain) := by
  unfold mem_Allocator_realloc__anon_9cee5a678d80 mem_Allocator_reallocAdvanced__anon_0e4c9b513eeb
  fsym [CAllocSpec.alloc h]

/-- **`append`** of a `u32` through `realloc` of the `[:0]u32` itself, for every allocator. -/
theorem append32_grant (s : Slice) (c : BitVec 32) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 4 = bs.size) (hs : bs.size < 2 ^ 64) (hpos : 0 < s.len.toNat)
    (hfit : I.fits ((s.len.toNat + 2) * 4) 2) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u32_append ⟨ctx, vtp⟩ s c)
      (fun r => I.own ⋆ (appended I φ 2 4 (Enc.encode (0 : BitVec 32)) (Enc.encode c) s.ptr bs
        s.len.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  append_grant (by fsym_arith) (by fsym_arith) hlen (by
    fsym [realloc32_spec ctx vtp fns I φ (h := h)])

/-- **`resize`** through `realloc` of the `[:0]u32` itself, for every allocator. -/
theorem resize32_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 4 = bs.size) (hs : bs.size < 2 ^ 64) (hpos : 0 < s.len.toNat)
    (hn : n.toNat + 1 < 2 ^ 64) (hfit : I.fits ((n.toNat + 1) * 4) 2)
    (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u32_resize ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (resized I φ 2 4 (Enc.encode (0 : BitVec 32)) s.ptr bs s.len.toNat n r ⋆
        vtR vtp fns.toList) ⋆ plain) :=
  resize_grant (by fsym_arith) hlen (by
    fsym [realloc32_spec ctx vtp fns I φ (h := h)])

/-- **`move`** (`remap` of the `[:0]u32` itself) for every allocator; a byte count
`(n + 1) * 4` that does not fit a `usize` is `null`. -/
theorem move32_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 4 = bs.size) (hs : bs.size < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 4) 2) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ vtR vtp fns.toList) ⋆ plain)
      (Buf_u32_move ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (moved I φ 2 4 (Enc.encode (0 : BitVec 32)) s.ptr bs s.len.toNat n r ⋆
        vtR vtp fns.toList) ⋆ plain) :=
  move_grant (by fsym_arith) hlen (by
    unfold Buf_u32_move mem_Allocator_remap__anon_b5ccb0b97340
    fsym [CAllocSpec.remap h])

/-- **`fit`** (the in-place `resize` of the `[:0]u32` itself) for every allocator; a byte count
that does not fit a `usize` is `false`. -/
theorem fit32_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 4 = bs.size) (hs : bs.size < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 4) 2) (h : CAllocSpec (CVTable.env env fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ vtR vtp fns.toList) ⋆ plain)
      (Buf_u32_fit ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (fitted I φ 2 4 (Enc.encode (0 : BitVec 32)) s.ptr bs s.len.toNat n.toNat
        r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  fit_grant (by fsym_arith) hlen (by
    unfold Buf_u32_fit mem_Allocator_resize__anon_d87227067220
    fsym [CAllocSpec.resize_granted h])

end Interfaces.GrowSpec
