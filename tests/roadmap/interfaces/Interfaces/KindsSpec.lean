import Interfaces.Kinds
import ZigLean.Mem.WidthLemmas
import ZigLean.Sep.Full.SentinelBuf
import ZigLean.Sep.Full.RegionEnc
import ZigLean.Sep.Full.Dispatch
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Block
import ZigLean.Sep.Full.AutoPrim
import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.Try
import ZigLean.Sep.Full.Region
import ZigLean.Sep.Full.Slice

/-!
# Sentinel buffers of other item kinds, for every allocator (M04)

`tests/roadmap/interfaces/kinds.zig` keeps a `[:z]align(A) T` through a caller-supplied
`std.mem.Allocator` for four item kinds that are not an unsigned integer with sentinel `0` at its
natural alignment:

* `Ff`: `[:0xff]u8`, a non-zero sentinel (`sz = 1`, `k = 0`);
* `Opt`: `[:null]?*u8`, an optional pointer item with the sentinel `null` (`sz = 8`, `k = 3`);
* `Flt`: `[:0]f32`, a float item (`sz = 4`, `k = 2`);
* `Over`: `[:0]align(16) u16`, an over-aligned slice made by `allocWithOptions` (`sz = 2`,
  `k = 4`).

They are instances of the generic statements and theorems of
`ZigLean/Sep/Full/SentinelBuf.lean` (`made`, `appended`, `resized`; `append_grant`,
`resize_grant`), as `Interfaces/SentinelSpec.lean` (`u8`) and `Interfaces/WideSpec.lean` (`u16`,
`u32`, `u64`) are: each supplies the walk of its own copy of the generated code (`fsym`) and the
size of its encoding. Every call through the allocator reaches the environment (`Ext`, premise
EXT-05), so the theorems assume only the contract `CAllocSpec` of the environment's allocator and
hold for every allocator that meets it. They are `CTriple`s (partial correctness, no panic).
-/

namespace Interfaces.KindsSpec

open Zig Zig.Full Zig.Full.FAssn Zig.Full.SentinelBuf Interfaces.Kinds

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

/-! ## `Ff`: `[:0xff]u8`, 1 byte at alignment `2 ^ 0`, sentinel `0xff` -/

/-- `a.free(s)` of a `[]u8`: the grant goes back. -/
theorem freeFf_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat = bs.size)
    (hpos : 0 < bs.size) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_1e60e7ef40f5 ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_1e60e7ef40f5
  fsym [free_undef h]

/-- `a.realloc(s, n)` of a nonempty granted `[]u8`. -/
theorem reallocFf_spec (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) (hfit : I.fits n.toNat 0)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_af0c43114565 ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.reallocResult 0 φ s.ptr bs n n.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) := by
  unfold mem_Allocator_realloc__anon_af0c43114565 mem_Allocator_reallocAdvanced__anon_0df1ef68623e
  fsym [CAllocSpec.alloc h, CAllocSpec.remap h, Norm.mulWithOverflow_one,
    freeFf_spec ctx vtp fns I e φ (h := h), free_undef h]

/-- **`make`** (`allocSentinel(u8, n, 0xff)`) for every allocator. -/
theorem makeFf_spec (n : BitVec 64) (hn : n.toNat + 1 < 2 ^ 64) (hfit : I.fits (n.toNat + 1) 0)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (Buf_u8_1_255_make ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (made I φ 0 1 (Enc.encode (255 : BitVec 8)) n r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  fsym [CAllocSpec.alloc h, Norm.mulWithOverflow_one]

/-- **`append`** to a `[:0xff]u8` for every allocator. -/
theorem appendFf_grant (s : Slice) (c : BitVec 8) (bs : Array Byte)
    (hlen : s.len.toNat + 1 = bs.size) (hs : s.len.toNat + 2 < 2 ^ 64)
    (hfit : I.fits (s.len.toNat + 2) 0) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u8_1_255_append ⟨ctx, vtp⟩ s c)
      (fun r => I.own ⋆ (appended I φ 0 1 (Enc.encode (255 : BitVec 8)) (Enc.encode c) s.ptr bs
        s.len.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  append_grant (by fsym_arith) (by fsym_arith) (by omega) (by
    fsym [reallocFf_spec ctx vtp fns I e φ (h := h)])

/-- **`resize`** of a `[:0xff]u8` for every allocator. -/
theorem resizeFf_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat + 1 = bs.size) (hs : s.len.toNat + 1 < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits (n.toNat + 1) 0) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u8_1_255_resize ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (resized I φ 0 1 (Enc.encode (255 : BitVec 8)) s.ptr bs s.len.toNat n r ⋆
        vtR vtp fns.toList) ⋆ plain) :=
  resize_grant (by fsym_arith) (by omega) (by
    fsym [reallocFf_spec ctx vtp fns I e φ (h := h)])

/-- **`release`** (`free` of a `[:0xff]u8`) for every allocator. -/
theorem releaseFf_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat + 1 = bs.size)
    (hs : bs.size < 2 ^ 64) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ vtR vtp fns.toList))
      (Buf_u8_1_255_release ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold Buf_u8_1_255_release mem_Allocator_free__anon_ec26f105dbd9
  fsym [free_undef h]

/-! ## `Opt`: `[:null]?*u8`, 8 bytes at alignment `2 ^ 3`, sentinel `null` -/

/-- `a.free(s)` of a `[]?*u8`: the grant goes back. -/
theorem freeOpt_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat * 8 = bs.size)
    (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_f3a890f4b1d1 ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_f3a890f4b1d1
  fsym [CAllocSpec.free' h]

/-- `a.realloc(s, n)` of a nonempty granted `[]?*u8`: `n * 8` bytes. -/
theorem reallocOpt_spec (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat * 8 = bs.size) (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size)
    (hfit : I.fits (n.toNat * 8) 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_a4f13023a362 ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.reallocResult 3 φ s.ptr bs n (n.toNat * 8) r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  unfold mem_Allocator_realloc__anon_a4f13023a362 mem_Allocator_reallocAdvanced__anon_8367c9b39ce8
  fsym [CAllocSpec.alloc h, CAllocSpec.remap h, freeOpt_spec ctx vtp fns I e φ (h := h),
    CAllocSpec.free' h]

/-- **`make`** (`allocSentinel(?*u8, n, null)`) for every allocator. -/
theorem makeOpt_spec (n : BitVec 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 8) 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (Buf___u8_8_null_make ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (made I φ 3 8 (Enc.encode (none : Option Ptr)) n r ⋆
        vtR vtp fns.toList) ⋆ plain) := by
  fsym [CAllocSpec.alloc h]

/-- **`append`** of a `?*u8` for every allocator. -/
theorem appendOpt_grant (s : Slice) (c : Option Ptr) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 8 = bs.size) (hs : bs.size < 2 ^ 64)
    (hfit : I.fits ((s.len.toNat + 2) * 8) 3)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf___u8_8_null_append ⟨ctx, vtp⟩ s c)
      (fun r => I.own ⋆ (appended I φ 3 8 (Enc.encode (none : Option Ptr)) (Enc.encode c) s.ptr bs
        s.len.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  append_grant (by fsym_arith) (by fsym_arith) hlen (by
    fsym [reallocOpt_spec ctx vtp fns I e φ (h := h)])

/-- **`resize`** of a `[:null]?*u8` for every allocator. -/
theorem resizeOpt_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 8 = bs.size) (hs : bs.size < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 8) 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf___u8_8_null_resize ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (resized I φ 3 8 (Enc.encode (none : Option Ptr)) s.ptr bs s.len.toNat n
        r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  resize_grant (by fsym_arith) hlen (by
    fsym [reallocOpt_spec ctx vtp fns I e φ (h := h)])

/-- **`release`** (`free` of a `[:null]?*u8`) for every allocator. -/
theorem releaseOpt_spec (s : Slice) (bs : Array Byte) (hlen : (s.len.toNat + 1) * 8 = bs.size)
    (hs : bs.size < 2 ^ 64) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ vtR vtp fns.toList))
      (Buf___u8_8_null_release ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold Buf___u8_8_null_release mem_Allocator_free__anon_79b5404fb5ec
  fsym [CAllocSpec.free' h]

/-! ## `Flt`: `[:0]f32`, 4 bytes at alignment `2 ^ 2`, sentinel `0.0` -/

/-- The sentinel of `Flt`: the float with the bits `0`. -/
abbrev zeroF32 : Zig.F32 := Zig.Float.ofBits (0 : BitVec 32)

/-- `a.free(s)` of a `[]f32`: the grant goes back. -/
theorem freeFlt_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat * 4 = bs.size)
    (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_370a618e6221 ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_370a618e6221
  fsym [CAllocSpec.free' h]

/-- `a.realloc(s, n)` of a nonempty granted `[]f32`: `n * 4` bytes. -/
theorem reallocFlt_spec (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat * 4 = bs.size) (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size)
    (hfit : I.fits (n.toNat * 4) 2) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_b0aac85a3215 ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.reallocResult 2 φ s.ptr bs n (n.toNat * 4) r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  unfold mem_Allocator_realloc__anon_b0aac85a3215 mem_Allocator_reallocAdvanced__anon_49dee7edffe7
  fsym [CAllocSpec.alloc h, CAllocSpec.remap h, freeFlt_spec ctx vtp fns I e φ (h := h),
    CAllocSpec.free' h]

/-- **`make`** (`allocSentinel(f32, n, 0)`) for every allocator. -/
theorem makeFlt_spec (n : BitVec 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 4) 2) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (Buf_f32_4_0_make ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (made I φ 2 4 (Enc.encode zeroF32) n r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  fsym [CAllocSpec.alloc h, FTotalTriple.regionStoreEnc, FTotalTriple.regionLoadEnc]

/-- **`append`** of an `f32` for every allocator. -/
theorem appendFlt_grant (s : Slice) (c : Zig.F32) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 4 = bs.size) (hs : bs.size < 2 ^ 64)
    (hfit : I.fits ((s.len.toNat + 2) * 4) 2)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_f32_4_0_append ⟨ctx, vtp⟩ s c)
      (fun r => I.own ⋆ (appended I φ 2 4 (Enc.encode zeroF32) (Enc.encode c) s.ptr bs
        s.len.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  append_grant (by fsym_arith) (by fsym_arith) hlen (by
    fsym [reallocFlt_spec ctx vtp fns I e φ (h := h), FTotalTriple.regionStoreEnc,
      FTotalTriple.regionLoadEnc])

/-- **`resize`** of a `[:0]f32` for every allocator. -/
theorem resizeFlt_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 4 = bs.size) (hs : bs.size < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 4) 2) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_f32_4_0_resize ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (resized I φ 2 4 (Enc.encode zeroF32) s.ptr bs s.len.toNat n r ⋆
        vtR vtp fns.toList) ⋆ plain) :=
  resize_grant (by fsym_arith) hlen (by
    fsym [reallocFlt_spec ctx vtp fns I e φ (h := h), FTotalTriple.regionStoreEnc,
      FTotalTriple.regionLoadEnc])

/-- **`release`** (`free` of a `[:0]f32`) for every allocator. -/
theorem releaseFlt_spec (s : Slice) (bs : Array Byte) (hlen : (s.len.toNat + 1) * 4 = bs.size)
    (hs : bs.size < 2 ^ 64) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ vtR vtp fns.toList))
      (Buf_f32_4_0_release ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold Buf_f32_4_0_release mem_Allocator_free__anon_0f60a910cb1e
  fsym [CAllocSpec.free' h]

/-! ## `Over`: `[:0]align(16) u16`, 2 bytes at alignment `2 ^ 4` -/

/-- `a.free(s)` of a `[]align(16) u16`: the grant goes back. -/
theorem freeOver_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat * 2 = bs.size)
    (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 4 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_41d335cc856a ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_41d335cc856a
  fsym [CAllocSpec.free' h]

/-- `a.realloc(s, n)` of a nonempty granted `[]align(16) u16`: `n * 2` bytes at alignment 16. -/
theorem reallocOver_spec (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat * 2 = bs.size) (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size)
    (hfit : I.fits (n.toNat * 2) 4) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 4 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_c129341ebc17 ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.reallocResult 4 φ s.ptr bs n (n.toNat * 2) r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  unfold mem_Allocator_realloc__anon_c129341ebc17 mem_Allocator_reallocAdvanced__anon_bbf7731c5936
  fsym [CAllocSpec.alloc h, CAllocSpec.remap h, freeOver_spec ctx vtp fns I e φ (h := h),
    CAllocSpec.free' h]

/-- **`make`** (`allocWithOptions(u16, n, .@"16", 0)`) for every allocator: the grant is at
alignment 16. -/
theorem makeOver_spec (n : BitVec 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 2) 4) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (Buf_u16_16_0_make ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (made I φ 4 2 (Enc.encode (0 : BitVec 16)) n r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  fsym [CAllocSpec.alloc h]

/-- **`append`** to a `[:0]align(16) u16` for every allocator. -/
theorem appendOver_grant (s : Slice) (c : BitVec 16) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 2 = bs.size) (hs : bs.size < 2 ^ 64)
    (hfit : I.fits ((s.len.toNat + 2) * 2) 4)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 4 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u16_16_0_append ⟨ctx, vtp⟩ s c)
      (fun r => I.own ⋆ (appended I φ 4 2 (Enc.encode (0 : BitVec 16)) (Enc.encode c) s.ptr bs
        s.len.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  append_grant (by fsym_arith) (by fsym_arith) hlen (by
    fsym [reallocOver_spec ctx vtp fns I e φ (h := h)])

/-- **`resize`** of a `[:0]align(16) u16` for every allocator. -/
theorem resizeOver_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 2 = bs.size) (hs : bs.size < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 2) 4) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 4 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u16_16_0_resize ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (resized I φ 4 2 (Enc.encode (0 : BitVec 16)) s.ptr bs s.len.toNat n r ⋆
        vtR vtp fns.toList) ⋆ plain) :=
  resize_grant (by fsym_arith) hlen (by
    fsym [reallocOver_spec ctx vtp fns I e φ (h := h)])

/-- **`release`** (`free` of a `[:0]align(16) u16`) for every allocator. -/
theorem releaseOver_spec (s : Slice) (bs : Array Byte) (hlen : (s.len.toNat + 1) * 2 = bs.size)
    (hs : bs.size < 2 ^ 64) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 4 φ bs ⋆ vtR vtp fns.toList))
      (Buf_u16_16_0_release ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold Buf_u16_16_0_release mem_Allocator_free__anon_a2c4c1310d94
  fsym [CAllocSpec.free' h]

/-! ## `copy`: a sentinel copy of a slice (`dupeSentinel`, `dupeZ` before Zig 0.17) -/

/-- **`copy`** (`a.dupeSentinel(u8, s, 0)`) of a nonempty readable source region of any
provenance, for every allocator: a grant of `s.len + 1` bytes that holds the source's bytes and
the sentinel `0` after them, or `error.OutOfMemory` and nothing; the source stays. The source is
nonempty (`hpos`) as for `dupe` (`AllocFba.Wrappers.dupe_spec`): `@memcpy`'s aliasing check
compares the two regions' addresses, and an empty region has no block to place. -/
theorem copy_spec (s : Slice) {A Sz : Nat} {K : BlockKind} {a : Nat} (bs : Array Byte)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) (hn : s.len.toNat + 1 < 2 ^ 64)
    (hfit : I.fits (s.len.toNat + 1) 0) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ (up (regionIn s.ptr A Sz K a bs) ⋆ vtR vtp fns.toList)) ⋆ plain)
      (copy ⟨ctx, vtp⟩ s)
      (fun r => I.own ⋆ (I.bytesResult 0 φ s.len (bs ++ Enc.encode (0 : BitVec 8)) r ⋆
        (up (regionIn s.ptr A Sz K a bs) ⋆ vtR vtp fns.toList)) ⋆ plain) :=
  copy_grant (m := s.len.toNat + 1) hlen (by fsym_arith) (by
    fsym [CAllocSpec.alloc h, Norm.mulWithOverflow_one])

end Interfaces.KindsSpec
