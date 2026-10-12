import ZigLean.EndianLemmas

/-! One regression row per value kind of the memory model (`docs/architecture-audit/enc-exactness.md`
§Regression rows): each kind's encoding reads back exactly (`decode ∘ encode`), and the bits the
compiler does not determine (padding, a NaN's bits, an absent payload, a pointer's or an error's
bytes as an integer) are `.unspecified` (or `.illegal`), never a value the model chose. Every row is
a closed term checked by the kernel; the general statements are `lawfulEnc_bitVec`,
`intEncOf_lawful`, `intEncExt_decode_encode`, `floatEncOf_decode_encode`, `floatEncOf_nan_int`
(`ZigLean/ReprCast.lean`, `ZigLean/EndianLemmas.lean`). A new value kind adds its row here. -/

open Zig

namespace EncRows

/-- `decode` of `bs` as `α`. -/
def dec (α : Type) [Enc α] (bs : Array Byte) : Option (Except Error α) := (Enc.decode bs : Result α).run

/-- The bytes of `v`, decoded as `β` (padded with undefined bytes to `β`'s size). -/
def view (β : Type) {α : Type} [Enc α] [Enc β] (v : α) : Option (Except Error β) :=
  dec β (padTo (Enc.size β) (Enc.encode v))

/-! ## Integers -/

-- `u32`: exact; an undefined byte is no value.
theorem row_u32_exact : dec (BitVec 32) (Enc.encode (0xdeadbeef : BitVec 32)) = some (.ok 0xdeadbeef) := by
  decide +kernel
theorem row_u32_undef : dec (BitVec 32) #[.int 1, .int 2, .undef, .int 4] = some (.error .unspecified) := by
  decide +kernel

-- `u10`/`i24` up to 0.16.0 (`intEncOf`): exact; the padding is undefined, a set padding bit is no value.
theorem row_u10_exact : dec (BitVec 10) (Enc.encode (0x2ab : BitVec 10)) = some (.ok 0x2ab) := by
  decide +kernel
theorem row_u10_padding : view (BitVec 16) (0x2ab : BitVec 10) = some (.error .unspecified) := by
  decide +kernel
theorem row_u10_set_padding : dec (BitVec 10) #[.int 0xab, .int 0x06] = some (.error .unspecified) := by
  decide +kernel

-- `i10`/`u24` from 0.17.0 (`intEncExt`): exact with the extension; padding that is not it is no value.
theorem row_i10_ext_exact :
    ((intEncExt .little true 10).decode ((intEncExt .little true 10).encode (-3))).run = some (.ok (-3)) := by
  decide +kernel
theorem row_i10_ext_bytes :
    ((intEncExt .little true 10).encode (-1)) = #[.int 0xff, .int 0xff] := by decide +kernel
theorem row_i10_ext_zero_padding :
    ((intEncExt .little true 10).decode #[.int 0x00, .int 0x02]).run = some (.error .unspecified) := by
  decide +kernel
theorem row_u24_ext_undef_padding :
    ((intEncExt .little false 24).decode #[.int 5, .int 0, .int 0, .undef]).run =
      some (.error .unspecified) := by
  decide +kernel

/-! ## `bool` -/

theorem row_bool_exact : dec Bool (Enc.encode true) = some (.ok true) := by decide +kernel
theorem row_bool_two : dec Bool #[.int 2] = some (.error .illegal) := by decide +kernel
theorem row_bool_undef : dec Bool #[.undef] = some (.error .unspecified) := by decide +kernel

/-! ## Floats -/

theorem row_f32_exact :
    dec F32 (Enc.encode (Zig.Float.ofBits 0x3eaaaaab : F32)) = some (.ok (Zig.Float.ofBits 0x3eaaaaab)) := by
  decide +kernel
/-- A NaN's bits are undefined: no integer and no float reads them back (`Float.detMask`). -/
theorem row_f32_nan_int : view (BitVec 32) (Zig.Float.ofBits 0x7fc00000 : F32) = some (.error .unspecified) := by
  decide +kernel
/-- `f80`: ten value bytes, then six bytes of padding. -/
theorem row_f80_padding : view (BitVec 128) (Zig.Float.ofBits 1 : F80) = some (.error .unspecified) := by
  decide +kernel

/-! ## Pointers -/

/-- A pointer's bytes are no integer at the decoder (a load exposes them as the address, MM-11). -/
theorem row_ptr_int : view (BitVec 64) (⟨some 0, 8⟩ : Ptr) = some (.error .unspecified) := by
  decide +kernel
theorem row_ptr_exact : dec Ptr (Enc.encode (⟨some 3, 8⟩ : Ptr)) = some (.ok ⟨some 3, 8⟩) := by
  decide +kernel
/-- `?*T`: null is address 0, eight zero bytes (the target's null). -/
theorem row_optptr_null : dec (Option Ptr) (Enc.encode (none : Option Ptr)) = some (.ok none) := by
  decide +kernel
theorem row_optptr_null_int : view (BitVec 64) (none : Option Ptr) = some (.ok 0) := by decide +kernel

/-! ## Optionals, slices, arrays -/

/-- `?u32` null: the payload bytes are undefined, the flag is 0. -/
theorem row_opt_null_payload : view (BitVec 32) (none : Option (BitVec 32)) = some (.error .unspecified) := by
  decide +kernel
theorem row_opt_exact :
    dec (Option (BitVec 32)) (Enc.encode (some (7 : BitVec 32))) = some (.ok (some 7)) := by
  decide +kernel
/-- A flag byte other than 0 or 1: `.illegal` (an over-approximation: native code tests `≠ 0`). -/
theorem row_opt_flag_two :
    dec (Option (BitVec 32)) #[.int 7, .int 0, .int 0, .int 0, .int 2, .undef, .undef, .undef] =
      some (.error .illegal) := by
  decide +kernel
/-- `?[]T` null: the length bytes are undefined. -/
theorem row_optslice_null_len :
    dec (BitVec 64) ((Enc.encode (none : Option Slice)).extract 8 16) = some (.error .unspecified) := by
  decide +kernel
theorem row_array_exact :
    dec (Vector (BitVec 24) 2) (Enc.encode (#v[1, 2] : Vector (BitVec 24) 2)) = some (.ok #v[1, 2]) := by
  decide +kernel

/-! ## Errors -/

/-- An error code's bytes are the error's name, never a compiler ordinal: no integer. -/
theorem row_err_int : dec (BitVec 16) (errBytes (some "Oops")) = some (.error .unspecified) := by
  decide +kernel
/-- `E!u32` holding an error: the payload bytes are undefined. -/
theorem row_errunion_payload :
    dec (BitVec 32) ((Enc.encode (Except.error "Oops" : Except ErrName (BitVec 32))).extract 0 4) =
      some (.error .unspecified) := by
  decide +kernel

/-! ## Vectors and unions -/

theorem row_vec_u24_exact :
    dec (Vec (BitVec 24) 2) (Enc.encode (⟨#v[1, 2]⟩ : Vec (BitVec 24) 2)) = some (.ok ⟨#v[1, 2]⟩) := by
  decide +kernel
/-- `@Vector(3, bool)`: 3 bits in a 1-byte integer; the bits above are padding. -/
theorem row_vec_bool_padding : view (BitVec 8) (⟨#v[true, false, true]⟩ : Vec Bool 3) =
    some (.error .unspecified) := by
  decide +kernel
/-- An `extern union` initialized through a `u8` field: its other bytes are undefined. -/
theorem row_extern_union_rest : (Raw.get (BitVec 32) (Raw.init 4 (5 : BitVec 8))).run =
    some (.error .unspecified) := by
  decide +kernel
/-- A `packed union` initialized through a `u3` field: the bits above it are undefined. -/
theorem row_packed_union_rest : (PackedU.get (BitVec 8) (PackedU.init 1 (5 : BitVec 3))).run =
    some (.error .unspecified) := by
  decide +kernel

end EncRows
