import Interfaces.Sentinel
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
# Sentinel buffers through `realloc`, for every allocator (M04)

`tests/roadmap/sentinel-realloc/source.zig` keeps a `[:0]u8` through a caller-supplied
`std.mem.Allocator`: `make` (`allocSentinel`), `append` and `resize` (a `realloc` of the absorbed
`len + 1`-byte buffer, then the sentinel stored at the new length) and `release` (`free` of the
sentinel slice). In the open translation (`Interfaces/Sentinel.lean`) every call through the
allocator reaches the environment (`Ext`, premise EXT-05), so the theorems assume only the
contract `CAllocSpec` of the environment's allocator at the vtable `fns` (`CVTable.env`) with
invariant `I`, and hold for every allocator that meets it. The generated code (the client and the
`std.mem.Allocator` wrappers) is walked by `fsym`.

A sentinel buffer of `len` items is a grant of `I`'s allocator for the fee `φ` of `len + 1` bytes,
the sentinel byte counted:

* `make_spec`: `n` undefined items and the sentinel `0` after them (`sentinelBytes`), or
  `error.OutOfMemory` and the fee back;
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

-- fsym does not evaluate the pure helper on its literal (engine ledger #21a)
theorem fromByteUnits_1 : mem_Alignment_fromByteUnits 1 = pure mem_Alignment.«1» := by
  have h : (1 : BitVec 64).ctz = 0 := Zig.ctz_twoPow (k := 0) (by decide)
  unfold mem_Alignment_fromByteUnits math_isPowerOfTwo__anon_38853e1fe316 debug_assert
  simp only [Zig.ctz, h]
  rfl

theorem mulWithOverflow_one (x : BitVec 64) :
    Zig.mulWithOverflow false (1#64) x = (x, 0#1) := by
  simp [Zig.mulWithOverflow, BitVec.umulOverflow, x.isLt]

/-! ## The bytes -/

/-- The bytes of `append`'s grant: `len + 2` bytes, the old payload `bs[0, len)`, then `c`, then
the sentinel `0`. -/
def Appended (bs bs' : Array Byte) (len : Nat) (c : BitVec 8) : Prop :=
  bs'.size = len + 2 ∧ bs'.extract 0 len = bs.extract 0 len ∧
    bs'.extract len (len + 1) = Enc.encode c ∧ bs'.extract (len + 1) (len + 2) = Enc.encode (0 : BitVec 8)

/-- The bytes of `resize`'s grant to `n` items: `n + 1` bytes, the old bytes below
`min n (len + 1)`, the sentinel `0` at `n`. -/
def Resized (bs bs' : Array Byte) (len n : Nat) : Prop :=
  bs'.size = n + 1 ∧ bs'.extract 0 (min n (len + 1)) = bs.extract 0 (min n (len + 1)) ∧
    bs'.extract n (n + 1) = Enc.encode (0 : BitVec 8)

/-- The bytes of a new sentinel buffer of `n` items: undefined, then the sentinel `0`. -/
abbrev sentinelBytes (n : Nat) : Array Byte :=
  writeBytes (Array.replicate (n + 1) .undef) n (Enc.encode (0 : BitVec 8))

section Bytes

variable {a bs : Array Byte} {len n o o1 o2 : Nat}

private theorem enc8 (v : BitVec 8) : (Enc.encode v).size = 1 := by
  simpa [Enc.size, intSize, intAlign, alignUp] using LawfulEnc.size_encode v

private theorem written_size (c : BitVec 8) (hs : a.size = len + 2) :
    (writeBytes a len (Enc.encode c)).size = len + 2 := by
  rw [writeBytes_size _ _ _ (by rw [enc8]; omega)]; exact hs

/-- The two stores of `append` keep the old payload. -/
theorem appended_prefix (c : BitVec 8) (hs : a.size = len + 2) (hb : bs.size = len + 1)
    (hk : keepsPrefix bs a) (h1 : o1 = len) (h2 : o2 = len + 1) :
    (writeBytes (writeBytes a o1 (Enc.encode c)) o2 (Enc.encode (0 : BitVec 8))).extract 0 len =
      bs.extract 0 len := by
  rw [h1, h2]
  have hw := written_size c hs
  have e2 := extract_writeBytes_disjoint (writeBytes a len (Enc.encode c)) (len + 1)
    (Enc.encode (0 : BitVec 8)) 0 len (by rw [enc8, hw]; omega) (by omega) (by right; omega)
  have e1 := extract_writeBytes_disjoint a len (Enc.encode c) 0 len (by rw [enc8]; omega)
    (by omega) (by right; omega)
  simp only [Nat.zero_add] at e1 e2
  rw [e2, e1]
  have ek : a.extract 0 (len + 1) = bs.extract 0 (len + 2) := by rw [← hb, ← hs]; exact hk
  have := congrArg (fun x : Array Byte => x.extract 0 len) ek
  simp only [Array.extract_extract, Nat.zero_add] at this
  rwa [show min len (len + 1) = len by omega, show min len (len + 2) = len by omega] at this

/-- `append` stores `c` at the old length. -/
theorem appended_byte (c : BitVec 8) (hs : a.size = len + 2) (h1 : o1 = len) (h2 : o2 = len + 1) :
    (writeBytes (writeBytes a o1 (Enc.encode c)) o2 (Enc.encode (0 : BitVec 8))).extract len
      (len + 1) = Enc.encode c := by
  rw [h1, h2]
  have hw := written_size c hs
  rw [extract_writeBytes_disjoint _ _ _ len 1 (by rw [enc8, hw]; omega) (by omega) (by right; omega)]
  have e := extract_writeBytes a len (Enc.encode c) (by rw [enc8]; omega)
  rwa [enc8] at e

/-- `append` stores the sentinel after it. -/
theorem appended_sentinel (c : BitVec 8) (hs : a.size = len + 2) (h1 : o1 = len)
    (h2 : o2 = len + 1) :
    (writeBytes (writeBytes a o1 (Enc.encode c)) o2 (Enc.encode (0 : BitVec 8))).extract (len + 1)
      (len + 2) = Enc.encode (0 : BitVec 8) := by
  rw [h1, h2]
  have hw := written_size c hs
  have e := extract_writeBytes (writeBytes a len (Enc.encode c)) (len + 1)
    (Enc.encode (0 : BitVec 8)) (by rw [enc8, hw]; omega)
  rwa [enc8] at e

/-- The sentinel store of `resize` keeps every retained byte below the new length. -/
theorem resized_prefix (hs : a.size = n + 1) (hb : bs.size = len + 1) (hk : keepsPrefix bs a)
    (ho : o = n) :
    (writeBytes a o (Enc.encode (0 : BitVec 8))).extract 0 (min n (len + 1)) =
      bs.extract 0 (min n (len + 1)) := by
  rw [ho]
  have e := extract_writeBytes_disjoint a n (Enc.encode (0 : BitVec 8)) 0 (min n (len + 1))
    (by rw [enc8]; omega) (by omega) (by right; omega)
  simp only [Nat.zero_add] at e
  rw [e]
  have ek : a.extract 0 (len + 1) = bs.extract 0 (n + 1) := by rw [← hb, ← hs]; exact hk
  have := congrArg (fun x : Array Byte => x.extract 0 (min n (len + 1))) ek
  simp only [Array.extract_extract, Nat.zero_add] at this
  rwa [show min (min n (len + 1)) (len + 1) = min n (len + 1) by omega,
    show min (min n (len + 1)) (n + 1) = min n (len + 1) by omega] at this

/-- `resize` stores the sentinel at the new length. -/
theorem resized_sentinel (hs : a.size = n + 1) (ho : o = n) :
    (writeBytes a o (Enc.encode (0 : BitVec 8))).extract n (n + 1) = Enc.encode (0 : BitVec 8) := by
  rw [ho]
  have e := extract_writeBytes a n (Enc.encode (0 : BitVec 8)) (by rw [enc8]; omega)
  rwa [enc8] at e

end Bytes

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

/-- `a.free(s)` of a `[]u8`: the grant goes back. -/
theorem free_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ vtR vtp fns.toList))
      (mem_Allocator_free__anon_1e60e7ef40f5 ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold mem_Allocator_free__anon_1e60e7ef40f5
  simp only [fromByteUnits_1]
  fsym [fun (s : Slice) ra (h' : 0 < s.len.toNat) =>
    CAllocSpec.free' h s 0 ra φ (Array.replicate s.len.toNat .undef) (by decide) (by simp) (by simpa using h')]

/-- `a.realloc(s, n)` of a nonempty granted `[]u8` (`reallocAdvanced`: `remap`, else `alloc`,
copy, `free`; `n = 0` frees). Its result slot is a stack local, so it runs in the plain mode. -/
theorem realloc_spec (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat = bs.size) (hpos : 0 < bs.size) (hfit : I.fits n.toNat 0)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (mem_Allocator_realloc__anon_af0c43114565 ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (I.reallocResult 0 φ s.ptr bs n n.toNat r ⋆ vtR vtp fns.toList) ⋆ plain) := by
  unfold mem_Allocator_realloc__anon_af0c43114565 mem_Allocator_reallocAdvanced__anon_0df1ef68623e
  simp only [fromByteUnits_1]
  fsym [CAllocSpec.alloc h, CAllocSpec.remap h, mulWithOverflow_one,
    free_spec ctx vtp fns I e φ (h := h),
    fun (s : Slice) ra (h' : 0 < s.len.toNat) =>
      CAllocSpec.free' h s 0 ra φ (Array.replicate s.len.toNat .undef) (by decide) (by simp) (by simpa using h')]

/-! ## The client -/

/-- What `make` returns: `n` items and the sentinel, or `error.OutOfMemory` and the fee back. -/
def made (n : BitVec 64) : Except ErrName Slice → FAssn
  | .ok r => ⟪r.len = n⟫ ⋆ I.granted r.ptr 0 φ (sentinelBytes n.toNat)
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ I.fee φ

/-- **`make`** (`allocSentinel(u8, n, 0)`) for every allocator. -/
theorem make_spec (n : BitVec 64) (hn : n.toNat + 1 < 2 ^ 64) (hfit : I.fits (n.toNat + 1) 0)
    (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList) ⋆ plain) (make ⟨ctx, vtp⟩ n)
      (fun r => I.own ⋆ (made I φ n r ⋆ vtR vtp fns.toList) ⋆ plain) := by
  fsym [CAllocSpec.alloc h, mulWithOverflow_one]

/-- What `append` of `c` to a buffer of `len` items (the grant `bs` at `old`) returns. -/
def appended (old : Ptr) (bs : Array Byte) (len : Nat) (c : BitVec 8) :
    Except ErrName Slice → FAssn
  | .ok r => ⟪r.len.toNat = len + 1⟫ ⋆ ((FAssn.ex fun bs' => ⟪Appended bs bs' len c⟫ ⋆
      I.granted r.ptr 0 φ bs') ⋆ I.fee φ)
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ (I.granted old 0 φ bs ⋆ I.fee φ)

/-- **`append`** for every allocator: one more item `c`, the sentinel after it; or the old buffer. -/
theorem append_grant (s : Slice) (c : BitVec 8) (bs : Array Byte)
    (hlen : s.len.toNat + 1 = bs.size) (hs : s.len.toNat + 2 < 2 ^ 64)
    (hfit : I.fits (s.len.toNat + 2) 0) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (append ⟨ctx, vtp⟩ s c)
      (fun r => I.own ⋆ (appended I φ s.ptr bs s.len.toNat c r ⋆ vtR vtp fns.toList) ⋆ plain) := by
  fsym [realloc_spec ctx vtp fns I e φ (h := h)]
  · exact appended_prefix c (by fsym_arith) (by fsym_arith) ‹_› (by fsym_arith) (by fsym_arith)
  · exact appended_byte c (by fsym_arith) (by fsym_arith) (by fsym_arith)
  · exact appended_sentinel c (by fsym_arith) (by fsym_arith) (by fsym_arith)

/-- What `resize` of a buffer of `len` items (the grant `bs` at `old`) to `n` items returns. -/
def resized (old : Ptr) (bs : Array Byte) (len : Nat) (n : BitVec 64) :
    Except ErrName Slice → FAssn
  | .ok r => ⟪r.len = n⟫ ⋆ ((FAssn.ex fun bs' => ⟪Resized bs bs' len n.toNat⟫ ⋆
      I.granted r.ptr 0 φ bs') ⋆ I.fee φ)
  | .error e => ⟪e = "OutOfMemory"⟫ ⋆ (I.granted old 0 φ bs ⋆ I.fee φ)

/-- **`resize`** for every allocator: `n` items, the retained bytes, the sentinel at `n`; or the
old buffer. -/
theorem resize_grant (s : Slice) (n : BitVec 64) (bs : Array Byte)
    (hlen : s.len.toNat + 1 = bs.size) (hs : s.len.toNat + 1 < 2 ^ 64) (hn : n.toNat + 1 < 2 ^ 64)
    (hfit : I.fits (n.toNat + 1) 0) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) ⋆ plain)
      (resize ⟨ctx, vtp⟩ s n)
      (fun r => I.own ⋆ (resized I φ s.ptr bs s.len.toNat n r ⋆ vtR vtp fns.toList) ⋆ plain) := by
  fsym [realloc_spec ctx vtp fns I e φ (h := h)]
  · exact resized_prefix (by fsym_arith) (by fsym_arith) ‹_› (by fsym_arith)
  · exact resized_sentinel (by fsym_arith) (by fsym_arith)

/-- **`release`** (`free` of a `[:0]u8`) for every allocator: the grant of `len + 1` bytes, the
sentinel included, goes back. -/
theorem release_spec (s : Slice) (bs : Array Byte) (hlen : s.len.toNat + 1 = bs.size)
    (hs : bs.size < 2 ^ 64) (h : CAllocSpec (CVTable.env (env e) fns) ctx I) :
    CTriple (I.own ⋆ (I.granted s.ptr 0 φ bs ⋆ vtR vtp fns.toList)) (release ⟨ctx, vtp⟩ s)
      (fun _ => I.own ⋆ (I.fee φ ⋆ vtR vtp fns.toList)) := by
  unfold release mem_Allocator_free__anon_0ba161b45e0a
  simp only [fromByteUnits_1]
  fsym [fun (s : Slice) ra (h' : 0 < s.len.toNat) =>
    CAllocSpec.free' h s 0 ra φ (Array.replicate s.len.toNat .undef) (by decide) (by simp) (by simpa using h')]

end Interfaces.SentinelSpec
