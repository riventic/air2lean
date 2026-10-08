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
