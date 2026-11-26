import Interfaces.Wide
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
# Sentinel buffers of a wider item type, for every allocator (M04)

`tests/roadmap/interfaces/wide.zig` keeps a `[:0]T` through a caller-supplied
`std.mem.Allocator`, for `T` = `u16`, `u32` and `u64`: `make` (`allocSentinel`), `append` and
`resize` (a `realloc` of the absorbed `len + 1`-item buffer, then the sentinel stored at the new
length) and `release` (`free` of the sentinel slice). `n` items and the sentinel are
`(n + 1) * sz` bytes at alignment `2 ^ k`, with `sz = @sizeOf(T)` and `2 ^ k = @alignOf(T)`.

The statements and the theorems of `append` and `resize` are generic
(`ZigLean/Sep/Full/SentinelBuf.lean`: `made`, `appended`, `resized`; `append_grant`,
`resize_grant`, for every item size, alignment and sentinel bytes). An instance, one copy of the
generated client and of its `std.mem.Allocator` wrappers per `T`, supplies its facts only: the
size of its encoding and the walk of its code by `fsym` (`free*_spec`, `realloc*_spec`, and the
shape of each client). As in `SentinelSpec` (the `u8` instance), every call through the allocator
reaches the environment (`Ext`, premise EXT-05), so the theorems assume only the contract
`CAllocSpec` of the environment's allocator at the vtable `fns` (`CVTable.env`) with invariant
`I`, and hold for every allocator that meets it.

A sentinel buffer of `len` items is a grant of `I`'s allocator for the fee `φ` of
`(len + 1) * sz` bytes at alignment `2 ^ k`, the sentinel item counted:

* `make*_spec`: `n` undefined items and the sentinel after them (`made`), or
  `error.OutOfMemory` and the fee back;
* `append*_grant`: `len + 1` items: the old payload, `c` at item `len`, the sentinel at item
  `len + 1` (`Appended`), and the second fee back; on `error.OutOfMemory` the old grant unchanged;
* `resize*_grant`: `n` items: every old item below `min n (len + 1)` (on growth the old sentinel
  too), the sentinel at item `n` (`Resized`); on `error.OutOfMemory` the old grant unchanged;
* `release*_spec`: the whole `(len + 1) * sz`-byte grant goes back, sentinel included.

A request whose byte count `(n + 1) * sz` does not fit a `usize` is `error.OutOfMemory`
(`math.mul` in the wrappers), the old grant unchanged. These are `CTriple`s (partial correctness,
no panic): the contract `CAllocSpec` is one.
-/

namespace Interfaces.WideSpec

open Zig Zig.Full Zig.Full.FAssn Zig.Full.SentinelBuf Interfaces.Wide

/-- The alignment argument of the generated entries, from its log2. -/
def al (k : Nat) : mem_Alignment := ⟨BitVec.ofNat 6 k⟩

variable [Ext]

/-- The environment's allocator entries: `Ext.call0` (`alloc`), `Ext.call1` (`remap`) and
`Ext.call2` (`free`); `e`'s `resize`, which the program never calls. -/
def env (e : AllocEnv Tgt) : AllocEnv Tgt :=
  { e with
    alloc := fun f a => Ext.call0 f a.1 a.2.1 (al a.2.2.1) a.2.2.2
    remap := fun f a => Ext.call1 f a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2
    free := fun f a => Ext.call2 f a.1 a.2.1 (al a.2.2.1) a.2.2.2 }

variable (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac)

/-! ## `u16`: 2 bytes at alignment `2 ^ 1` -/

/-- `a.free(s)` of a `[]u16`: the grant goes back. -/
theorem free16_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat * 2 = bs.size)
    (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 1 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_906bba868805 ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_906bba868805
  fsym [CAllocSpec.free' h]

/-- `a.realloc(s, n)` of a nonempty granted `[]u16` (`reallocAdvanced`: `remap`, else `alloc`,
copy, `free`; `n = 0` frees): `n * 2` bytes. -/
theorem realloc16_spec (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat * 2 = bs.size) (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size)
    (hfit : I.fits (n.toNat * 2) 1) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 1 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_0848537da7a2 ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.reallocResult 1 φ s.ptr bs n (n.toNat * 2) r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  unfold mem_Allocator_realloc__anon_0848537da7a2 mem_Allocator_reallocAdvanced__anon_37f73f8446a2
  fsym [CAllocSpec.alloc h, CAllocSpec.remap h, free16_spec ctx vtp fns I e φ (h := h),
    CAllocSpec.free' h]

/-- **`make`** (`allocSentinel(u16, n, 0)`) for every allocator. -/
theorem make16_spec (n : BitVec 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 2) 1) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (Buf_u16_make ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (made I φ 1 2 (Enc.encode (0 : BitVec 16)) n r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  fsym [CAllocSpec.alloc h]

/-- **`append`** of a `u16` for every allocator: one more item `c`, the sentinel after it; or the
old buffer. -/
theorem append16_grant (s : Slice) (c : BitVec 16) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 2 = bs.size) (hs : bs.size < 2 ^ 64)
    (hfit : I.fits ((s.len.toNat + 2) * 2) 1)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 1 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u16_append ⟨ctx, vtp⟩ s c)
      (fun r => I.own ⋆ (appended I φ 1 2 (Enc.encode (0 : BitVec 16)) (Enc.encode c) s.ptr bs
        s.len.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  append_grant (by fsym_arith) (by fsym_arith) hlen (by
    fsym [realloc16_spec ctx vtp fns I e φ (h := h)])

/-- **`resize`** of a `[:0]u16` for every allocator: `n` items, the retained items, the sentinel
at item `n`; or the old buffer. -/
theorem resize16_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 2 = bs.size) (hs : bs.size < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 2) 1) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 1 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u16_resize ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (resized I φ 1 2 (Enc.encode (0 : BitVec 16)) s.ptr bs s.len.toNat n r ⋆
        vtR vtp fns.toList) ⋆ plain) :=
  resize_grant (by fsym_arith) hlen (by
    fsym [realloc16_spec ctx vtp fns I e φ (h := h)])

/-- **`release`** (`free` of a `[:0]u16`) for every allocator: the grant of `(len + 1) * 2` bytes,
the sentinel included, goes back. -/
theorem release16_spec (s : Slice) (bs : Array Byte) (hlen : (s.len.toNat + 1) * 2 = bs.size)
    (hs : bs.size < 2 ^ 64) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 1 φ bs ⋆ vtR vtp fns.toList)) (Buf_u16_release ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold Buf_u16_release mem_Allocator_free__anon_ef346418a252
  fsym [CAllocSpec.free' h]

/-! ## `u32`: 4 bytes at alignment `2 ^ 2` -/

/-- `a.free(s)` of a `[]u32`: the grant goes back. -/
theorem free32_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat * 4 = bs.size)
    (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_10fd68fdc68d ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_10fd68fdc68d
  fsym [CAllocSpec.free' h]

/-- `a.realloc(s, n)` of a nonempty granted `[]u32`: `n * 4` bytes. -/
theorem realloc32_spec (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat * 4 = bs.size) (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size)
    (hfit : I.fits (n.toNat * 4) 2) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_c895a53644a2 ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.reallocResult 2 φ s.ptr bs n (n.toNat * 4) r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  unfold mem_Allocator_realloc__anon_c895a53644a2 mem_Allocator_reallocAdvanced__anon_f9642f2d8f58
  fsym [CAllocSpec.alloc h, CAllocSpec.remap h, free32_spec ctx vtp fns I e φ (h := h),
    CAllocSpec.free' h]

/-- **`make`** (`allocSentinel(u32, n, 0)`) for every allocator. -/
theorem make32_spec (n : BitVec 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 4) 2) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (Buf_u32_make ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (made I φ 2 4 (Enc.encode (0 : BitVec 32)) n r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  fsym [CAllocSpec.alloc h]

/-- **`append`** of a `u32` for every allocator. -/
theorem append32_grant (s : Slice) (c : BitVec 32) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 4 = bs.size) (hs : bs.size < 2 ^ 64)
    (hfit : I.fits ((s.len.toNat + 2) * 4) 2)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u32_append ⟨ctx, vtp⟩ s c)
      (fun r => I.own ⋆ (appended I φ 2 4 (Enc.encode (0 : BitVec 32)) (Enc.encode c) s.ptr bs
        s.len.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  append_grant (by fsym_arith) (by fsym_arith) hlen (by
    fsym [realloc32_spec ctx vtp fns I e φ (h := h)])

/-- **`resize`** of a `[:0]u32` for every allocator. -/
theorem resize32_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 4 = bs.size) (hs : bs.size < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 4) 2) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u32_resize ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (resized I φ 2 4 (Enc.encode (0 : BitVec 32)) s.ptr bs s.len.toNat n r ⋆
        vtR vtp fns.toList) ⋆ plain) :=
  resize_grant (by fsym_arith) hlen (by
    fsym [realloc32_spec ctx vtp fns I e φ (h := h)])

/-- **`release`** (`free` of a `[:0]u32`) for every allocator: the grant of `(len + 1) * 4` bytes,
the sentinel included, goes back. -/
theorem release32_spec (s : Slice) (bs : Array Byte) (hlen : (s.len.toNat + 1) * 4 = bs.size)
    (hs : bs.size < 2 ^ 64) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ vtR vtp fns.toList)) (Buf_u32_release ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold Buf_u32_release mem_Allocator_free__anon_85944fd5a0eb
  fsym [CAllocSpec.free' h]

/-! ## `u64`: 8 bytes at alignment `2 ^ 3` -/

/-- `a.free(s)` of a `[]u64`: the grant goes back. -/
theorem free64_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat * 8 = bs.size)
    (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_f1de31ec7442 ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_f1de31ec7442
  fsym [CAllocSpec.free' h]

/-- `a.realloc(s, n)` of a nonempty granted `[]u64`: `n * 8` bytes. -/
theorem realloc64_spec (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat * 8 = bs.size) (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size)
    (hfit : I.fits (n.toNat * 8) 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_db3a5630f4fc ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.reallocResult 3 φ s.ptr bs n (n.toNat * 8) r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  unfold mem_Allocator_realloc__anon_db3a5630f4fc mem_Allocator_reallocAdvanced__anon_1b00930347b4
  fsym [CAllocSpec.alloc h, CAllocSpec.remap h, free64_spec ctx vtp fns I e φ (h := h),
    CAllocSpec.free' h]

/-- **`make`** (`allocSentinel(u64, n, 0)`) for every allocator. -/
theorem make64_spec (n : BitVec 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 8) 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (Buf_u64_make ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (made I φ 3 8 (Enc.encode (0 : BitVec 64)) n r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  fsym [CAllocSpec.alloc h]

/-- **`append`** of a `u64` for every allocator. -/
theorem append64_grant (s : Slice) (c : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 8 = bs.size) (hs : bs.size < 2 ^ 64)
    (hfit : I.fits ((s.len.toNat + 2) * 8) 3)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u64_append ⟨ctx, vtp⟩ s c)
      (fun r => I.own ⋆ (appended I φ 3 8 (Enc.encode (0 : BitVec 64)) (Enc.encode c) s.ptr bs
        s.len.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  append_grant (by fsym_arith) (by fsym_arith) hlen (by
    fsym [realloc64_spec ctx vtp fns I e φ (h := h)])

/-- **`resize`** of a `[:0]u64` for every allocator. -/
theorem resize64_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 8 = bs.size) (hs : bs.size < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 8) 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u64_resize ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (resized I φ 3 8 (Enc.encode (0 : BitVec 64)) s.ptr bs s.len.toNat n r ⋆
        vtR vtp fns.toList) ⋆ plain) :=
  resize_grant (by fsym_arith) hlen (by
    fsym [realloc64_spec ctx vtp fns I e φ (h := h)])

/-- **`release`** (`free` of a `[:0]u64`) for every allocator: the grant of `(len + 1) * 8` bytes,
the sentinel included, goes back. -/
theorem release64_spec (s : Slice) (bs : Array Byte) (hlen : (s.len.toNat + 1) * 8 = bs.size)
    (hs : bs.size < 2 ^ 64) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ vtR vtp fns.toList)) (Buf_u64_release ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold Buf_u64_release mem_Allocator_free__anon_dddca57af15b
  fsym [CAllocSpec.free' h]

end Interfaces.WideSpec
