import Interfaces.Wide
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
# Sentinel buffers of a wider item type, for every allocator (M04)

`tests/roadmap/interfaces/wide.zig` keeps a `[:0]T` through a caller-supplied
`std.mem.Allocator`, for `T` = `u16`, `u32` and `u64`: `make` (`allocSentinel`), `append` and
`resize` (a `realloc` of the absorbed `len + 1`-item buffer, then the sentinel stored at the new
length) and `release` (`free` of the sentinel slice). It is `Interfaces/SentinelSpec.lean` (the
`u8` instance) for items whose byte count and alignment differ from the item count: `n` items and
the sentinel are `(n + 1) * sz` bytes at alignment `2 ^ k`, with `sz = @sizeOf(T)` and
`2 ^ k = @alignOf(T)`.

The statements are made once, for every item size `sz`, log2 alignment `k` and sentinel bytes `z`
(`sentinelBytes`, `Appended`, `Resized`; `made`, `appended`, `resized`); each instance of the
generated code (the client and its `std.mem.Allocator` wrappers, one copy per `T`) proves them
at its `sz`, `k` and `z`, walked by `fsym`. As in `SentinelSpec`, every call through the allocator
reaches the environment (`Ext`, premise EXT-05), so the theorems assume only the contract
`CAllocSpec` of the environment's allocator at the vtable `fns` (`CVTable.env`) with invariant
`I`, and hold for every allocator that meets it.

A sentinel buffer of `len` items is a grant of `I`'s allocator for the fee `φ` of
`(len + 1) * sz` bytes at alignment `2 ^ k`, the sentinel item counted:

* `make*_spec`: `n` undefined items and the sentinel after them (`sentinelBytes`), or
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

open Zig Zig.Full Zig.Full.FAssn Interfaces.Wide

/-- The alignment argument of the generated entries, from its log2. -/
def al (k : Nat) : mem_Alignment := ⟨BitVec.ofNat 6 k⟩

/-! ## The bytes, for every item size -/

/-- The bytes of a new sentinel buffer of `n` items of `sz` bytes: undefined items, then the
sentinel `z`. -/
abbrev sentinelBytes (sz : Nat) (z : Array Byte) (n : Nat) : Array Byte :=
  writeBytes (Array.replicate ((n + 1) * sz) .undef) (n * sz) z

/-- The bytes of `append`'s grant: `len + 2` items of `sz` bytes, the old payload (items
`[0, len)`), then the item `c`, then the sentinel `z`. -/
def Appended (sz : Nat) (z c bs bs' : Array Byte) (len : Nat) : Prop :=
  bs'.size = (len + 2) * sz ∧ bs'.extract 0 (len * sz) = bs.extract 0 (len * sz) ∧
    bs'.extract (len * sz) ((len + 1) * sz) = c ∧ bs'.extract ((len + 1) * sz) ((len + 2) * sz) = z

/-- The bytes of `resize`'s grant to `n` items of `sz` bytes: `n + 1` items, the old items below
`min n (len + 1)`, the sentinel `z` at item `n`. -/
def Resized (sz : Nat) (z bs bs' : Array Byte) (len n : Nat) : Prop :=
  bs'.size = (n + 1) * sz ∧
    bs'.extract 0 (min n (len + 1) * sz) = bs.extract 0 (min n (len + 1) * sz) ∧
    bs'.extract (n * sz) ((n + 1) * sz) = z

section Bytes

variable {a z c : Array Byte} {sz len n o o1 o2 : Nat}

/-- `append` stores the item `c` at the old length. -/
theorem appended_item (hc : c.size = sz) (hz : z.size = sz) (hs : a.size = (len + 2) * sz)
    (h1 : o1 = len * sz) (h2 : o2 = (len + 1) * sz) :
    (writeBytes (writeBytes a o1 c) o2 z).extract (len * sz) ((len + 1) * sz) = c := by
  subst h1 h2
  simp only [Nat.add_mul, Nat.one_mul] at hs ⊢
  have hw := writeBytes_size a (len * sz) c (by omega)
  have e := extract_writeBytes_disjoint (writeBytes a (len * sz) c) (len * sz + sz) z (len * sz) sz
    (by omega) (by omega) (by right; omega)
  rw [e]
  have e' := extract_writeBytes a (len * sz) c (by omega)
  rwa [hc] at e'

/-- `append` stores the sentinel after it. -/
theorem appended_sentinel (hc : c.size = sz) (hz : z.size = sz) (hs : a.size = (len + 2) * sz)
    (h1 : o1 = len * sz) (h2 : o2 = (len + 1) * sz) :
    (writeBytes (writeBytes a o1 c) o2 z).extract ((len + 1) * sz) ((len + 2) * sz) = z := by
  subst h1 h2
  have hw := writeBytes_size a (len * sz) c (by simp only [Nat.add_mul] at hs; omega)
  have e := extract_writeBytes (writeBytes a (len * sz) c) ((len + 1) * sz) z
    (by simp only [Nat.add_mul, Nat.one_mul] at hs ⊢; omega)
  rwa [hz, show (len + 1) * sz + sz = (len + 2) * sz by simp only [Nat.add_mul]; omega] at e

/-- `resize` stores the sentinel at the new length. -/
theorem resized_sentinel (hz : z.size = sz) (hs : a.size = (n + 1) * sz) (ho : o = n * sz) :
    (writeBytes a o z).extract (n * sz) ((n + 1) * sz) = z := by
  subst ho
  have e := extract_writeBytes a (n * sz) z (by simp only [Nat.add_mul, Nat.one_mul] at hs; omega)
  rwa [hz, show n * sz + sz = (n + 1) * sz by simp only [Nat.add_mul, Nat.one_mul]] at e

end Bytes

private theorem enc16 (v : BitVec 16) : (Enc.encode v).size = 2 := by
  simpa [Enc.size, intSize, intAlign, alignUp] using LawfulEnc.size_encode v

private theorem enc32 (v : BitVec 32) : (Enc.encode v).size = 4 := by
  simpa [Enc.size, intSize, intAlign, alignUp] using LawfulEnc.size_encode v

private theorem enc64 (v : BitVec 64) : (Enc.encode v).size = 8 := by
  simpa [Enc.size, intSize, intAlign, alignUp] using LawfulEnc.size_encode v

/-! ## The allocator -/

variable [Ext]

/-- The environment's allocator entries: `Ext.call0` (`alloc`), `Ext.call1` (`remap`) and
`Ext.call2` (`free`); `e`'s `resize`, which the program never calls. -/
def env (e : AllocEnv Tgt) : AllocEnv Tgt :=
  { e with
    alloc := fun f a => Ext.call0 f a.1 a.2.1 (al a.2.2.1) a.2.2.2
    remap := fun f a => Ext.call1 f a.1 a.2.1 (al a.2.2.1) a.2.2.2.1 a.2.2.2.2
    free := fun f a => Ext.call2 f a.1 a.2.1 (al a.2.2.1) a.2.2.2 }

variable (ctx vtp : Ptr) (fns : VTableFns) (I : FAllocInv) (e : AllocEnv Tgt) (φ : Frac)

/-- The vtable's `free`, at any alignment `2 ^ k`, of a slice that a `free` wrapper has made
undefined: the fee back. -/
theorem free_entry (h : CAllocSpec (CVTable.env (env e) fns) ctx I) (k : Nat) (hk : k < 64)
    (s : Slice) (ra : BitVec 64) (hs : 0 < s.len.toNat) :
    CTriple (I.own ⋆ I.granted s.ptr k φ (Array.replicate s.len.toNat .undef))
      ((CVTable.env (env e) fns).free ctx s k ra) (fun _ => I.own ⋆ I.fee φ) :=
  CAllocSpec.free' h s k ra φ _ hk (by simp) (by simpa using hs)

/-! ## What the clients return, for every item size and alignment -/

/-- What `make` returns: `n` items and the sentinel, or `error.OutOfMemory` and the fee back. -/
def made (k sz : Nat) (z : Array Byte) (n : BitVec 64) : Except ErrName Slice → FAssn
  | .ok r => ⟪r.len = n⟫ ⋆ I.granted r.ptr k φ (sentinelBytes sz z n.toNat)
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ I.fee φ

/-- What `append` of the item `c` to a buffer of `len` items (the grant `bs` at `old`) returns. -/
def appended (k sz : Nat) (z c : Array Byte) (old : Ptr) (bs : Array Byte) (len : Nat) :
    Except ErrName Slice → FAssn
  | .ok r => ⟪r.len.toNat = len + 1⟫ ⋆ ((FAssn.ex fun bs' => ⟪Appended sz z c bs bs' len⟫ ⋆
      I.granted r.ptr k φ bs') ⋆ I.fee φ)
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ (I.granted old k φ bs ⋆ I.fee φ)

/-- What `resize` of a buffer of `len` items (the grant `bs` at `old`) to `n` items returns. -/
def resized (k sz : Nat) (z : Array Byte) (old : Ptr) (bs : Array Byte) (len : Nat) (n : BitVec 64) :
    Except ErrName Slice → FAssn
  | .ok r => ⟪r.len = n⟫ ⋆ ((FAssn.ex fun bs' => ⟪Resized sz z bs bs' len n.toNat⟫ ⋆
      I.granted r.ptr k φ bs') ⋆ I.fee φ)
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ (I.granted old k φ bs ⋆ I.fee φ)

/-! ## `u16`: 2 bytes at alignment `2 ^ 1` -/

/-- `a.free(s)` of a `[]u16`: the grant goes back. -/
theorem free16_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat * 2 = bs.size)
    (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 1 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_906bba868805 ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_906bba868805
  fsym [free_entry ctx fns I e φ h 1 (by decide)]

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
    free_entry ctx fns I e φ h 1 (by decide)]

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
    (hn : s.len.toNat + 2 < 2 ^ 64) (hfit : I.fits ((s.len.toNat + 2) * 2) 1)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 1 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u16_append ⟨ctx, vtp⟩ s c)
      (fun r => I.own ⋆ (appended I φ 1 2 (Enc.encode (0 : BitVec 16)) (Enc.encode c) s.ptr bs
        s.len.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) := by
  fsym [realloc16_spec ctx vtp fns I e φ (h := h)]
  · exact appended_item (enc16 c) (enc16 0) (by fsym_arith) (by fsym_arith) (by fsym_arith)
  · exact appended_sentinel (enc16 c) (enc16 0) (by fsym_arith) (by fsym_arith) (by fsym_arith)

/-- **`resize`** of a `[:0]u16` for every allocator: `n` items, the retained items, the sentinel
at item `n`; or the old buffer. -/
theorem resize16_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 2 = bs.size) (hs : bs.size < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 2) 1) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 1 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u16_resize ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (resized I φ 1 2 (Enc.encode (0 : BitVec 16)) s.ptr bs s.len.toNat n r ⋆
        vtR vtp fns.toList) ⋆ plain) := by
  fsym [realloc16_spec ctx vtp fns I e φ (h := h)]
  · exact resized_sentinel (enc16 0) (by fsym_arith) (by fsym_arith)

/-- **`release`** (`free` of a `[:0]u16`) for every allocator: the grant of `(len + 1) * 2` bytes,
the sentinel included, goes back. -/
theorem release16_spec (s : Slice) (bs : Array Byte) (hlen : (s.len.toNat + 1) * 2 = bs.size)
    (hs : bs.size < 2 ^ 64) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 1 φ bs ⋆ vtR vtp fns.toList)) (Buf_u16_release ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold Buf_u16_release mem_Allocator_free__anon_ef346418a252
  fsym [free_entry ctx fns I e φ h 1 (by decide)]

/-! ## `u32`: 4 bytes at alignment `2 ^ 2` -/

/-- `a.free(s)` of a `[]u32`: the grant goes back. -/
theorem free32_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat * 4 = bs.size)
    (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_10fd68fdc68d ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_10fd68fdc68d
  fsym [free_entry ctx fns I e φ h 2 (by decide)]

/-- `a.realloc(s, n)` of a nonempty granted `[]u32` (`reallocAdvanced`: `remap`, else `alloc`,
copy, `free`; `n = 0` frees): `n * 4` bytes. -/
theorem realloc32_spec (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat * 4 = bs.size) (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size)
    (hfit : I.fits (n.toNat * 4) 2) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_c895a53644a2 ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.reallocResult 2 φ s.ptr bs n (n.toNat * 4) r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  unfold mem_Allocator_realloc__anon_c895a53644a2 mem_Allocator_reallocAdvanced__anon_f9642f2d8f58
  fsym [CAllocSpec.alloc h, CAllocSpec.remap h, free32_spec ctx vtp fns I e φ (h := h),
    free_entry ctx fns I e φ h 2 (by decide)]

/-- **`make`** (`allocSentinel(u32, n, 0)`) for every allocator. -/
theorem make32_spec (n : BitVec 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 4) 2) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (Buf_u32_make ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (made I φ 2 4 (Enc.encode (0 : BitVec 32)) n r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  fsym [CAllocSpec.alloc h]

/-- **`append`** of a `u32` for every allocator: one more item `c`, the sentinel after it; or the
old buffer. -/
theorem append32_grant (s : Slice) (c : BitVec 32) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 4 = bs.size) (hs : bs.size < 2 ^ 64)
    (hn : s.len.toNat + 2 < 2 ^ 64) (hfit : I.fits ((s.len.toNat + 2) * 4) 2)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u32_append ⟨ctx, vtp⟩ s c)
      (fun r => I.own ⋆ (appended I φ 2 4 (Enc.encode (0 : BitVec 32)) (Enc.encode c) s.ptr bs
        s.len.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) := by
  fsym [realloc32_spec ctx vtp fns I e φ (h := h)]
  · exact appended_item (enc32 c) (enc32 0) (by fsym_arith) (by fsym_arith) (by fsym_arith)
  · exact appended_sentinel (enc32 c) (enc32 0) (by fsym_arith) (by fsym_arith) (by fsym_arith)

/-- **`resize`** of a `[:0]u32` for every allocator: `n` items, the retained items, the sentinel
at item `n`; or the old buffer. -/
theorem resize32_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 4 = bs.size) (hs : bs.size < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 4) 2) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u32_resize ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (resized I φ 2 4 (Enc.encode (0 : BitVec 32)) s.ptr bs s.len.toNat n r ⋆
        vtR vtp fns.toList) ⋆ plain) := by
  fsym [realloc32_spec ctx vtp fns I e φ (h := h)]
  · exact resized_sentinel (enc32 0) (by fsym_arith) (by fsym_arith)

/-- **`release`** (`free` of a `[:0]u32`) for every allocator: the grant of `(len + 1) * 4` bytes,
the sentinel included, goes back. -/
theorem release32_spec (s : Slice) (bs : Array Byte) (hlen : (s.len.toNat + 1) * 4 = bs.size)
    (hs : bs.size < 2 ^ 64) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 2 φ bs ⋆ vtR vtp fns.toList)) (Buf_u32_release ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold Buf_u32_release mem_Allocator_free__anon_85944fd5a0eb
  fsym [free_entry ctx fns I e φ h 2 (by decide)]

/-! ## `u64`: 8 bytes at alignment `2 ^ 3` -/

/-- `a.free(s)` of a `[]u64`: the grant goes back. -/
theorem free64_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat * 8 = bs.size)
    (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_f1de31ec7442 ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_f1de31ec7442
  fsym [free_entry ctx fns I e φ h 3 (by decide)]

/-- `a.realloc(s, n)` of a nonempty granted `[]u64` (`reallocAdvanced`: `remap`, else `alloc`,
copy, `free`; `n = 0` frees): `n * 8` bytes. -/
theorem realloc64_spec (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat * 8 = bs.size) (hs : bs.size < 2 ^ 64) (hpos : 0 < bs.size)
    (hfit : I.fits (n.toNat * 8) 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_db3a5630f4fc ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.reallocResult 3 φ s.ptr bs n (n.toNat * 8) r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  unfold mem_Allocator_realloc__anon_db3a5630f4fc mem_Allocator_reallocAdvanced__anon_1b00930347b4
  fsym [CAllocSpec.alloc h, CAllocSpec.remap h, free64_spec ctx vtp fns I e φ (h := h),
    free_entry ctx fns I e φ h 3 (by decide)]

/-- **`make`** (`allocSentinel(u64, n, 0)`) for every allocator. -/
theorem make64_spec (n : BitVec 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 8) 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (Buf_u64_make ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (made I φ 3 8 (Enc.encode (0 : BitVec 64)) n r ⋆ vtR vtp fns.toList) ⋆
        plain) := by
  fsym [CAllocSpec.alloc h]

/-- **`append`** of a `u64` for every allocator: one more item `c`, the sentinel after it; or the
old buffer. -/
theorem append64_grant (s : Slice) (c : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 8 = bs.size) (hs : bs.size < 2 ^ 64)
    (hn : s.len.toNat + 2 < 2 ^ 64) (hfit : I.fits ((s.len.toNat + 2) * 8) 3)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u64_append ⟨ctx, vtp⟩ s c)
      (fun r => I.own ⋆ (appended I φ 3 8 (Enc.encode (0 : BitVec 64)) (Enc.encode c) s.ptr bs
        s.len.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) := by
  fsym [realloc64_spec ctx vtp fns I e φ (h := h)]
  · exact appended_item (enc64 c) (enc64 0) (by fsym_arith) (by fsym_arith) (by fsym_arith)
  · exact appended_sentinel (enc64 c) (enc64 0) (by fsym_arith) (by fsym_arith) (by fsym_arith)

/-- **`resize`** of a `[:0]u64` for every allocator: `n` items, the retained items, the sentinel
at item `n`; or the old buffer. -/
theorem resize64_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : (s.len.toNat + 1) * 8 = bs.size) (hs : bs.size < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits ((n.toNat + 1) * 8) 3) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (Buf_u64_resize ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (resized I φ 3 8 (Enc.encode (0 : BitVec 64)) s.ptr bs s.len.toNat n r ⋆
        vtR vtp fns.toList) ⋆ plain) := by
  fsym [realloc64_spec ctx vtp fns I e φ (h := h)]
  · exact resized_sentinel (enc64 0) (by fsym_arith) (by fsym_arith)

/-- **`release`** (`free` of a `[:0]u64`) for every allocator: the grant of `(len + 1) * 8` bytes,
the sentinel included, goes back. -/
theorem release64_spec (s : Slice) (bs : Array Byte) (hlen : (s.len.toNat + 1) * 8 = bs.size)
    (hs : bs.size < 2 ^ 64) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 3 φ bs ⋆ vtR vtp fns.toList)) (Buf_u64_release ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold Buf_u64_release mem_Allocator_free__anon_dddca57af15b
  fsym [free_entry ctx fns I e φ h 3 (by decide)]

end Interfaces.WideSpec
