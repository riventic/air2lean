import Interfaces.Sentinel
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
# Sentinel buffers through `realloc`, for every allocator (M04)

`tests/roadmap/sentinel-realloc/source.zig` keeps a `[:0]u8` through a caller-supplied
`std.mem.Allocator`: `make` (`allocSentinel`), `append` and `resize` (a `realloc` of the absorbed
`len + 1`-byte buffer, then the sentinel stored at the new length) and `release` (`free` of the
sentinel slice). In the open translation (`Interfaces/Sentinel.lean`) every call through the
allocator reaches the environment (`Ext`, premise EXT-05), so the theorems assume only the
contract `CAllocSpec` of the environment's allocator at the vtable `fns` (`CVTable.env`) with
invariant `I`, and hold for every allocator that meets it. The generated code (the client and the
`std.mem.Allocator` wrappers) is walked by `fsym`.

This is the instance `sz = 1`, `k = 0`, sentinel `0` of the generic statements and theorems
(`ZigLean/Sep/Full/SentinelBuf.lean`: `made`, `appended`, `resized`; `append_grant`,
`resize_grant`); `Interfaces/WideSpec.lean` has the instances of wider items. A sentinel buffer
of `len` items is a grant of `I`'s allocator for the fee `φ` of `len + 1` bytes, the sentinel
byte counted:

* `make_spec`: `n` undefined items and the sentinel `0` after them, or `error.OutOfMemory` and
  the fee back;
* `append_grant`: `len + 1` items: the old payload, `c` at `len`, the sentinel at `len + 1`
  (`Appended`), and the second fee back; on `error.OutOfMemory` the old grant unchanged;
* `resize_grant`: `n` items: every old byte below `min n (len + 1)` (on growth the old sentinel
  byte too), the sentinel at `n` (`Resized`); on `error.OutOfMemory` the old grant unchanged;
* `release_spec`: the whole `len + 1`-byte grant goes back, sentinel included.

The sentinel invariant thus holds on success and on failure, for every allocation, remap and
failure behaviour that the contract allows. The bytes a growth adds hold any value
(`keepsPrefix`): the contract does not fix them. These are `CTriple`s (partial correctness, no
panic): the contract `CAllocSpec` is one.
-/

namespace Interfaces.SentinelSpec

open Zig Zig.Full Zig.Full.FAssn Interfaces.Sentinel

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

/-- `a.free(s)` of a `[]u8`: the grant goes back. -/
theorem free_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_1e60e7ef40f5 ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_1e60e7ef40f5
  fsym [SentinelBuf.free_undef h]

/-- `a.realloc(s, n)` of a nonempty granted `[]u8` (`reallocAdvanced`: `remap`, else `alloc`,
copy, `free`; `n = 0` frees). Its result slot is a stack local, so it runs in the plain mode. -/
theorem realloc_spec (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) (hfit : I.fits n.toNat 0)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_af0c43114565 ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.reallocResult 0 φ s.ptr bs n n.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) := by
  unfold mem_Allocator_realloc__anon_af0c43114565 mem_Allocator_reallocAdvanced__anon_0df1ef68623e
  fsym [CAllocSpec.alloc h, CAllocSpec.remap h, Norm.mulWithOverflow_one,
    free_spec ctx vtp fns I e φ (h := h), SentinelBuf.free_undef h]

/-- **`make`** (`allocSentinel(u8, n, 0)`) for every allocator. -/
theorem make_spec (n : BitVec 64) (hn : n.toNat + 1 < 2 ^ 64) (hfit : I.fits (n.toNat + 1) 0)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (make ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (SentinelBuf.made I φ 0 1 (Enc.encode (0 : BitVec 8)) n r ⋆
        vtR vtp fns.toList) ⋆ plain) := by
  fsym [CAllocSpec.alloc h, Norm.mulWithOverflow_one]

/-- **`append`** for every allocator: one more item `c`, the sentinel after it; or the old buffer. -/
theorem append_grant (s : Slice) (c : BitVec 8) (bs : Array Byte)
    (hlen : s.len.toNat + 1 = bs.size) (hs : s.len.toNat + 2 < 2 ^ 64)
    (hfit : I.fits (s.len.toNat + 2) 0) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (append ⟨ctx, vtp⟩ s c)
      (fun r => I.own ⋆ (SentinelBuf.appended I φ 0 1 (Enc.encode (0 : BitVec 8)) (Enc.encode c)
        s.ptr bs s.len.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  SentinelBuf.append_grant (by fsym_arith) (by fsym_arith) (by omega) (by
    fsym [realloc_spec ctx vtp fns I e φ (h := h)])

/-- **`resize`** for every allocator: `n` items, the retained bytes, the sentinel at `n`; or the
old buffer. -/
theorem resize_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat + 1 = bs.size) (hs : s.len.toNat + 1 < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits (n.toNat + 1) 0) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (resize ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (SentinelBuf.resized I φ 0 1 (Enc.encode (0 : BitVec 8)) s.ptr bs
        s.len.toNat n r ⋆ vtR vtp fns.toList) ⋆ plain) :=
  SentinelBuf.resize_grant (by fsym_arith) (by omega) (by
    fsym [realloc_spec ctx vtp fns I e φ (h := h)])

/-- **`release`** (`free` of a `[:0]u8`) for every allocator: the grant of `len + 1` bytes, the
sentinel included, goes back. -/
theorem release_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat + 1 = bs.size)
    (hs : bs.size < 2 ^ 64) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ vtR vtp fns.toList)) (release ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold release mem_Allocator_free__anon_0ba161b45e0a
  fsym [SentinelBuf.free_undef h]

end Interfaces.SentinelSpec
