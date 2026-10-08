import ZigLean.Mem.Width
import ZigLean.Mem.Lemmas

/-!
# Pointer-width encodings: round trips and bounds (T02)

Proof-only (`ZigLean/Mem/Lemmas.lean`), so outside `ZigLean.lean`. For both widths: a pointer,
an optional pointer and a slice decode to what was encoded, with `PtrWidth.bytes`-sized
pointers; a decoded slice length, and so every byte count of a slice, is below
`PtrWidth.bound`.
-/

namespace Zig

theorem ptrFrags_size (w : PtrWidth) (p : Ptr) : (ptrFrags w p).size = w.bytes := by
  cases w <;> simp [ptrFrags, PtrWidth.bytes]

theorem ptrEnc_size_encode (w : PtrWidth) (p : Ptr) : ((ptrEnc w).encode p).size = w.bytes :=
  ptrFrags_size w p

theorem ptrEnc_roundtrip (w : PtrWidth) (p : Ptr) : (ptrEnc w).decode ((ptrEnc w).encode p) = pure p := by
  delta ptrEnc ptrFrags
  cases w
  · have hr : (Array.finRange 8).extract 0 4 = #[0, 1, 2, 3] := by decide
    simp [PtrWidth.bytes, hr, pure, ExceptT.pure, ExceptT.mk]
  · have hr : (Array.finRange 8).extract 0 8 = #[0, 1, 2, 3, 4, 5, 6, 7] := by decide
    simp [PtrWidth.bytes, hr, pure, ExceptT.pure, ExceptT.mk]

theorem optPtrEnc_roundtrip (w : PtrWidth) (v : Option Ptr) :
    (optPtrEnc w).decode ((optPtrEnc w).encode v) = pure v := by
  delta optPtrEnc ptrEnc ptrFrags
  cases v with
  | none => cases w <;> simp [PtrWidth.bytes, pure, ExceptT.pure, ExceptT.mk]
  | some p =>
    cases w
    · have hr : (Array.finRange 8).extract 0 4 = #[0, 1, 2, 3] := by decide
      simp [PtrWidth.bytes, hr, pure, ExceptT.pure, ExceptT.mk, Functor.map, ExceptT.map]
      intro h
      have := congrArg (·[0]?) h
      simp at this
    · have hr : (Array.finRange 8).extract 0 8 = #[0, 1, 2, 3, 4, 5, 6, 7] := by decide
      simp [PtrWidth.bytes, hr, pure, ExceptT.pure, ExceptT.mk, Functor.map, ExceptT.map]
      intro h
      have := congrArg (·[0]?) h
      simp at this

/-- The length bytes of a `usize` of the width: `bytes` bytes, decoding to the value. -/
theorem usizeEnc_lawful (w : PtrWidth) (n : BitVec w.bits) :
    (Enc.encode n).size = w.bytes ∧ Enc.decode (Enc.encode n) = pure n := by
  cases w
  · exact ⟨LawfulEnc.size_encode (α := BitVec 32) n, LawfulEnc.decode_encode (α := BitVec 32) n⟩
  · exact ⟨LawfulEnc.size_encode (α := BitVec 64) n, LawfulEnc.decode_encode (α := BitVec 64) n⟩

theorem sliceEnc_size_encode (w : PtrWidth) (s : SliceOf w.bits) :
    ((sliceEnc w).encode s).size = 2 * w.bytes := by
  show ((ptrEnc w).encode s.ptr ++ Enc.encode s.len).size = _
  rw [Array.size_append, ptrEnc_size_encode, (usizeEnc_lawful w s.len).1]
  omega

/-- A slice of either width decodes to what was encoded: the pointer's `bytes` fragments,
then the length's `bytes` little-endian bytes. -/
theorem sliceEnc_roundtrip (w : PtrWidth) (s : SliceOf w.bits) :
    (sliceEnc w).decode ((sliceEnc w).encode s) = pure s := by
  have hp := ptrEnc_roundtrip w s.ptr
  have hs := ptrEnc_size_encode w s.ptr
  obtain ⟨hls, hl⟩ := usizeEnc_lawful w s.len
  show (do pure (⟨← (ptrEnc w).decode
      (((ptrEnc w).encode s.ptr ++ Enc.encode s.len).extract 0 w.bytes),
    ← (Enc.decode (((ptrEnc w).encode s.ptr ++ Enc.encode s.len).extract w.bytes (2 * w.bytes)) :
      Result (BitVec w.bits))⟩ : SliceOf w.bits)) = pure s
  have h1 : ((ptrEnc w).encode s.ptr ++ Enc.encode s.len).extract 0 w.bytes = (ptrEnc w).encode s.ptr := by
    rw [Array.extract_append, ← hs, Array.extract_size]
    simp
  have h2 : ((ptrEnc w).encode s.ptr ++ Enc.encode s.len).extract w.bytes (2 * w.bytes) =
      Enc.encode s.len := by
    rw [Array.extract_append, hs, show 2 * w.bytes - w.bytes = (Enc.encode s.len).size by omega]
    simp only [Nat.sub_self, Array.extract_size]
    have : ((ptrEnc w).encode s.ptr).extract w.bytes (2 * w.bytes) = #[] := by
      simp [hs, Nat.min_le_right]
    rw [this, Array.empty_append]
  simp only [h1, h2, hp, hl, pure_bind]

instance : LawfulEnc Slice32 where
  size_encode s := by
    delta instEncSlice32
    exact sliceEnc_size_encode .w32 s
  decode_encode s := by
    delta instEncSlice32
    exact sliceEnc_roundtrip .w32 s

/-- A decoded slice length, and so the byte count of every slice of items of at most 1 byte,
is below `2 ^ bits`. -/
theorem sliceEnc_len_lt (w : PtrWidth) {bs : Array Byte} {s : SliceOf w.bits}
    (_ : (sliceEnc w).decode bs = pure s) : s.len.toNat < w.bound :=
  s.len.isLt

/-! ## The `.w64` definitions are the 64-bit model

Moved from `ZigLean/Mem/Width.lean`, which `ZigLean.lean` imports: these equations unfold
the 64-bit runtime definitions, so a differential mutation of one of them (`scripts/mutate.sh`)
must not break the runtime build. -/

theorem ptrFrags_w64 (p : Ptr) : ptrFrags .w64 p = (Array.finRange 8).map (.ptrFrag p) := by
  simp only [ptrFrags, PtrWidth.bytes]
  rw [show (Array.finRange 8).extract 0 8 = Array.finRange 8 by decide]

/-- The 64-bit instance is the existing `Enc Ptr` (`ZigLean/Mem/Enc.lean`). -/
theorem ptrEnc_w64 : ptrEnc .w64 = (inferInstance : Enc Ptr) := by
  have h : ∀ p, ptrFrags .w64 p = (Array.finRange 8).map (.ptrFrag p) := ptrFrags_w64
  simp only [ptrEnc, h]
  rfl

/-- The 64-bit instance is the existing `Enc (Option Ptr)`. -/
theorem optPtrEnc_w64 : optPtrEnc .w64 = (inferInstance : Enc (Option Ptr)) := by
  have h : ∀ p, ptrFrags .w64 p = (Array.finRange 8).map (.ptrFrag p) := ptrFrags_w64
  have he : ptrEnc .w64 = (inferInstance : Enc Ptr) := ptrEnc_w64
  simp only [optPtrEnc, h]
  rfl

/-- At `.w64`, a slice has the bytes of the existing `Enc Slice`. -/
theorem sliceEnc_w64_encode (s : Slice) : (sliceEnc .w64).encode s.toOf = Enc.encode s := by
  have he : ptrEnc .w64 = (inferInstance : Enc Ptr) := ptrEnc_w64
  show (ptrEnc .w64).encode s.ptr ++ Enc.encode s.len = _
  rw [he]
  rfl

theorem sliceEnc_w64_decode (bs : Array Byte) :
    (sliceEnc .w64).decode bs = Slice.toOf <$> (Enc.decode bs : Result Slice) := by
  have he : ptrEnc .w64 = (inferInstance : Enc Ptr) := ptrEnc_w64
  show (do pure (⟨← (ptrEnc .w64).decode (bs.extract 0 8),
      ← (Enc.decode (bs.extract 8 16) : Result (BitVec 64))⟩ : SliceOf 64)) = _
  rw [he]
  show _ = Slice.toOf <$> (do pure (⟨← (Enc.decode (bs.extract 0 8) : Result Ptr),
      ← (Enc.decode (bs.extract 8 16) : Result (BitVec 64))⟩ : Slice))
  simp only [map_bind, map_pure]
  rfl

theorem sliceEnc_w64_size : (sliceEnc .w64).size = Enc.size Slice := rfl

theorem sliceEnc_w64_align : (sliceEnc .w64).align = Enc.align Slice := rfl

theorem allocatorEnc_w64 : allocatorEnc .w64 = (inferInstance : Enc Allocator) := rfl

theorem Ptr.elemOf_64 (p : Ptr) (size : Nat) (i : BitVec 64) : p.elemOf size i = p.elem size i := rfl

theorem Ptr.elemSubOf_64 (p : Ptr) (size : Nat) (i : BitVec 64) :
    p.elemSubOf size i = p.elemSub size i := rfl

theorem indexOf_64 {α : Type} (a : Array α) (i : BitVec 64) : indexOf a i = index a i := rfl

theorem vindexOf_64 {α : Type} {k : Nat} (a : Vector α k) (i : BitVec 64) :
    vindexOf a i = vindex a i := rfl

theorem lenOf_64 {α : Type} (a : Array α) : lenOf 64 a = len a := rfl

theorem memsetOf_64 {α : Type} [Enc α] (align : Nat) (p : Ptr) (k : BitVec 64) (v : Option α) :
    memsetOf align p k v = memset align p k v := rfl

theorem memmoveOf_64 (size dstAlign srcAlign : Nat) (dst src : Ptr) (k : BitVec 64) :
    memmoveOf size dstAlign srcAlign dst src k = memmove size dstAlign srcAlign dst src k := rfl

theorem readSliceOf_64 (α : Type) [Enc α] (align : Nat) (s : Slice) :
    readSliceOf α align s.toOf = readSlice α align s := rfl

theorem zeroAllocPtrOf_w64 (align : Nat) : zeroAllocPtrOf .w64 align = zeroAllocPtr align := rfl

theorem allocBytesOf_w64 (align n : Nat) : allocBytesOf .w64 align n = allocBytes align n := rfl

theorem Allocator.createOf_w64 (a : Allocator) (size align : Nat) :
    a.createOf .w64 size align = a.create size align := rfl

theorem Allocator.freeOf_64 (a : Allocator) (size : Nat) (s : Slice) :
    a.freeOf size s.toOf = a.free size s := rfl

/-- At `.w64`, `allocOf` is the existing `Allocator.alloc` (its slice as `SliceOf 64`). -/
theorem Allocator.allocOf_w64 (a : Allocator) (size align : Nat) (n : BitVec 64) :
    a.allocOf .w64 size align n = (Except.map Slice.toOf) <$> a.alloc size align n := by
  simp only [Allocator.allocOf, Allocator.alloc, allocBytesOf_w64, PtrWidth.bound_w64,
    Nat.reducePow]
  by_cases h : 18446744073709551616 ≤ size * n.toNat
  · simp only [h, ite_true, map_pure]
    rfl
  · simp only [h, ite_false, map_bind]
    congr 1
    funext r
    cases r <;> simp [Except.map, Slice.toOf]

namespace Wasm32
open scoped Zig.Wasm32

/-- The 4-byte encodings that a 32-bit translation opens are lawful. -/
instance : LawfulEnc Ptr where
  size_encode p := ptrEnc_size_encode .w32 p
  decode_encode p := ptrEnc_roundtrip .w32 p

instance : LawfulEnc (Option Ptr) where
  size_encode v := by cases v <;> simp [Enc.encode, Enc.size, ptrFrags_size]
  decode_encode v := optPtrEnc_roundtrip .w32 v

example : Enc.size Ptr = 4 := rfl
example : Enc.size (Option Ptr) = 4 := rfl
example : Enc.size Slice32 = 8 := rfl
example : Enc.size (Option Slice32) = 8 := rfl
example : Enc.size Allocator = 8 := rfl

end Wasm32

end Zig
