import ZigLean.Endian
import ZigLean.ReprCast
import ZigLean.PackedLemmas

/-!
# Byte order: round trips (T03)

Proof-only (it imports `ZigLean/Mem/Lemmas.lean` through `ZigLean.ReprCast`), so outside
`ZigLean.lean`. For both byte orders (`Zig.ByteOrder`):

* `intEncOf_lawful`, `floatEncOf_lawful`, `sliceEncOf_lawful`, `optSliceEncOf_lawful`: integers
  of every width, floats of every format, slices and optional slices read back as stored;
* `Vec.packedEncOf_lawful`: a vector reads back as stored, whenever its lanes' bits do;
* `readBits_arrange_writeField_same`/`_disjoint`: a bit-pointer store at either order reads back
  through a bit-pointer load, and leaves a disjoint field unchanged;
* `intBytesOf_big`: the big-endian value bytes are the little-endian ones reversed, and
  `intEncOf_big_u32`/`intEncOf_little_u32` give the concrete bytes of `0x01020304`.

The `.little` instances are the existing little-endian definitions by `rfl`
(`intEncOf_little`, …, `ZigLean/Endian.lean`), so their existing proofs apply unchanged.
-/

namespace Zig

/-- The value bytes of `v` at order `o` read back at order `o`. -/
theorem intOfBytesOf_padTo (o : ByteOrder) {n : Nat} (v : BitVec n) (size : Nat) :
    intOfBytesOf o n (padTo size (intBytesOf o v)) false = pure v := by
  have hb := intBytes_size v
  cases o with
  | little => exact intOfBytes_of_extract v (by simp [intBytesOf, padTo, ← hb])
  | big =>
    show intOfBytes n ((padTo size (intBytes v).reverse).extract 0 ((n + 7) / 8)).reverse false = _
    have : (padTo size (intBytes v).reverse).extract 0 ((n + 7) / 8) = (intBytes v).reverse := by
      simp [padTo, Array.extract_append, hb]
    rw [this, Array.reverse_reverse]
    exact intOfBytes_intBytes v

/-- Integers of every width read back as stored, at both orders. -/
theorem intEncOf_lawful (o : ByteOrder) (n : Nat) : @LawfulEnc (BitVec n) (intEncOf o n) := by
  letI := intEncOf o n
  refine ⟨fun v => ?_, fun v => intOfBytesOf_padTo o v _⟩
  show (padTo (intSize n) (intBytesOf o v)).size = intSize n
  simp [padTo, intBytesOf, intBytes_size]
  have := intBytes_le_intSize n
  omega

/-- Floats of every format read back as stored (their bits), at both orders. -/
theorem floatEncOf_lawful (o : ByteOrder) (fmt : FloatFmt) :
    @LawfulEnc (Float fmt) (floatEncOf o fmt) := by
  letI := floatEncOf o fmt
  have hl := intEncOf_lawful o fmt.width
  refine ⟨fun v => @LawfulEnc.size_encode _ (intEncOf o fmt.width) hl v.bits, fun v => ?_⟩
  show (do pure (⟨← intOfBytesOf o fmt.width (padTo (intSize fmt.width) (intBytesOf o v.bits)) false⟩ :
    Float fmt)) = pure v
  rw [intOfBytesOf_padTo]
  rfl

/-- A slice reads back as stored: its pointer, then its length at order `o`. -/
theorem sliceEncOf_lawful (o : ByteOrder) : @LawfulEnc Slice (sliceEncOf o) := by
  letI := sliceEncOf o
  have hl := intEncOf_lawful o 64
  have hps : ∀ p : Ptr, (Enc.encode p).size = 8 := fun p => LawfulEnc.size_encode p
  have hls : ∀ v : BitVec 64, ((intEncOf o 64).encode v).size = 8 := fun v =>
    @LawfulEnc.size_encode _ (intEncOf o 64) hl v
  refine ⟨fun s => ?_, fun s => ?_⟩
  · show (Enc.encode s.ptr ++ (intEncOf o 64).encode s.len).size = 16
    simp [hps, hls]
  · show (do pure (⟨← Enc.decode ((Enc.encode s.ptr ++ (intEncOf o 64).encode s.len).extract 0 8),
      ← (intEncOf o 64).decode ((Enc.encode s.ptr ++ (intEncOf o 64).encode s.len).extract 8 16)⟩ :
        Slice)) = pure s
    have h1 : (Enc.encode s.ptr ++ (intEncOf o 64).encode s.len).extract 0 8 = Enc.encode s.ptr := by
      rw [Array.extract_append, ← hps s.ptr, Array.extract_size]; simp [hps]
    have h2 : (Enc.encode s.ptr ++ (intEncOf o 64).encode s.len).extract 8 16 =
        (intEncOf o 64).encode s.len := by
      rw [Array.extract_append, hps s.ptr,
        show 16 - 8 = ((intEncOf o 64).encode s.len).size by rw [hls]]
      simp only [Nat.sub_self, Array.extract_size]
      have : (Enc.encode s.ptr).extract 8 16 = #[] := by simp [hps]
      rw [this, Array.empty_append]
    rw [h1, h2, LawfulEnc.decode_encode, @LawfulEnc.decode_encode _ (intEncOf o 64) hl]
    rfl

/-- `?[]T` reads back as stored at both orders. -/
theorem optSliceEncOf_lawful (o : ByteOrder) : @LawfulEnc (Option Slice) (optSliceEncOf o) := by
  letI := optSliceEncOf o
  have hl := sliceEncOf_lawful o
  refine ⟨fun v => ?_, fun v => ?_⟩
  · cases v with
    | none => rfl
    | some s => exact @LawfulEnc.size_encode _ (sliceEncOf o) hl s
  · cases v with
    | none => rfl
    | some s =>
      show (if ((sliceEncOf o).encode s).extract 0 8 == Array.replicate 8 (.int 0) then pure none
        else some <$> (sliceEncOf o).decode ((sliceEncOf o).encode s)) = pure (some s)
      have hne : (((sliceEncOf o).encode s).extract 0 8 == Array.replicate 8 (.int 0)) = false := by
        have hn : ((sliceEncOf o).encode s).extract 0 8 ≠ Array.replicate 8 (.int 0) := by
          intro h
          have := congrArg (·[0]?) h
          have hr : Array.finRange 8 = #[0, 1, 2, 3, 4, 5, 6, 7] := by decide
          simp [Enc.encode, hr] at this
        exact beq_false_of_ne hn
      rw [hne, @LawfulEnc.decode_encode _ (sliceEncOf o) hl]
      rfl

/-! ## Vectors -/

/-- A vector reads back as stored at both orders, whenever its lanes' bits do. -/
theorem Vec.packedEncOf_lawful (o : ByteOrder) {α : Type} (n w : Nat) (toBits : α → BitVec w)
    (ofBits : BitVec w → α) (h : ∀ x, ofBits (toBits x) = x) :
    @LawfulEnc (Vec α n) (Vec.packedEncOf o n w toBits ofBits) := by
  cases o with
  | little =>
    rw [Vec.packedEncOf_little]
    exact Vec.packedEnc_lawful n w toBits ofBits h
  | big =>
    letI := Vec.packedEncOf .big n w toBits ofBits
    refine ⟨fun v => ?_, fun v => ?_⟩
    · have := le_ceilPow2 ((n * w + 7) / 8)
      simp [Enc.encode, Enc.size, padTo, intBytesOf, intBytes, packedVecLayout]
      omega
    · have hx := intOfBytesOf_padTo .big (Vec.packBitsOf .big w toBits v) (packedVecLayout n w)
      simp only [Enc.decode, Enc.encode, hx, bind, ExceptT.bind, pure, ExceptT.pure, ExceptT.mk,
        ExceptT.bindCont, Option.bind_some]
      congr
      rcases v with ⟨lanes⟩
      simp only [Vec.unpackBitsOf, Vec.packBitsOf]
      congr 1
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_reverse, Vector.getElem_ofFn, Vec.packBits_toNat]
      rw [laneOf_packLanes _ _ (by simp; omega)]
      simp only [List.getElem_map, Vector.getElem_toList, Vector.getElem_reverse, h,
        show n - 1 - (n - 1 - i) = i by omega]

instance {w n : Nat} : @LawfulEnc (Vec (BitVec w) n) (Vec.packedEncOf .big n w id id) :=
  Vec.packedEncOf_lawful .big n w id id fun _ => rfl

/-! ## Bit-pointers

A bit-pointer access at order `o` reads or writes the field in the host bytes put in
little-endian order (`o.arrange`), so the little-endian frame lemmas of
`ZigLean/PackedLemmas.lean` hold at both orders. -/

/-- A field store at either order reads back. -/
theorem readBits_arrange_writeField_same (o : ByteOrder) {n : Nat} (bs : Array Byte) (off : Nat)
    (v : BitVec n) (hs : off + n ≤ 8 * bs.size) :
    readBits (o.arrange (o.arrange (writeField (o.arrange bs) off (some v)))) off n = some v := by
  rw [ByteOrder.arrange_arrange]
  exact readBits_writeField_same _ off v (by simpa using hs)

/-- A field store at either order leaves a disjoint field as it was. -/
theorem readBits_arrange_writeField_disjoint (o : ByteOrder) {n n' : Nat} (bs : Array Byte)
    (off off' : Nat) (v : Option (BitVec n)) (h : off' + n' ≤ off ∨ off + n ≤ off') :
    readBits (o.arrange (o.arrange (writeField (o.arrange bs) off v))) off' n' =
      readBits (o.arrange bs) off' n' := by
  rw [ByteOrder.arrange_arrange]
  exact readBits_writeField_disjoint _ off off' v h

/-! ## Concrete bytes -/

theorem intBytesOf_big {n : Nat} (v : BitVec n) : intBytesOf .big v = (intBytes v).reverse := rfl

/-- `0x01020304 : u32` is `01 02 03 04` at big endian and `04 03 02 01` at little endian. -/
theorem intEncOf_big_u32 :
    (intEncOf .big 32).encode 0x01020304#32 = #[.int 1, .int 2, .int 3, .int 4] := by decide +kernel

theorem intEncOf_little_u32 :
    (intEncOf .little 32).encode 0x01020304#32 = #[.int 4, .int 3, .int 2, .int 1] := by decide +kernel

/-- A `u12` at big endian: its partly used byte (the high 4 bits) comes first. -/
theorem intEncOf_big_u12 :
    (intEncOf .big 12).encode 0xABC#12 = #[.part 4 0xA#8, .int 0xBC#8] := by decide +kernel

end Zig
