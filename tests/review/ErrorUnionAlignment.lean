import ZigLean.Mem
import ZigLean.Mem.Lemmas

open Zig

namespace ErrorUnionAlignment

-- Kernel-reduced ABI expectations, independent of encode/decode round trips.
example : errUnionOffsets 1 1 = (0, 2) := by decide
example : errUnionOffsets 2 2 = (2, 0) := by decide
example : errUnionOffsets 4 2 = (4, 0) := by decide
example : errUnionOffsets 8 8 = (8, 0) := by decide
example : errUnionOffsets 0 8 = (0, 0) := by decide
example : errUnionSize 0 8 = 8 := by decide
example : errUnionSize 2 2 = 4 := by decide

example : Enc.encode (.ok (0x1234 : BitVec 16) : Except ErrName (BitVec 16)) =
    #[.int 0x34, .int 0x12, .int 0, .int 0] := by
  have hr : Array.range 2 = #[0, 1] := by decide
  simp [Enc.encode, Enc.size, Enc.align, intSize, intAlign, alignUp, intBytes, padTo,
    errUnionOffsets, errUnionSize, errBytes, writeBytes, hr,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
example : Enc.encode (.error "Bad" : Except ErrName (BitVec 16)) =
    #[.undef, .undef, .errFrag "Bad" 0, .errFrag "Bad" 1] := by decide
example : (Enc.decode #[.int 0x34, .int 0x12, .int 0, .int 0] :
    Result (Except ErrName (BitVec 16))) = pure (.ok 0x1234) := by rfl
example : (Enc.decode #[.undef, .undef, .errFrag "Bad" 0, .errFrag "Bad" 1] :
    Result (Except ErrName (BitVec 16))) = pure (.error "Bad") := by rfl

-- The generic proof must still elaborate through the changed layout bounds.
example {α : Type} [Enc α] [LawfulEnc α] (v : Except ErrName α) :
    Enc.decode (Enc.encode v) = (pure v : Result (Except ErrName α)) :=
  LawfulEnc.decode_encode v

example (p : Ptr) : errPayloadPtr (BitVec 16) p = p := by
  simp [errPayloadPtr, errUnionOffsets, Enc.size, Enc.align, intSize, intAlign, alignUp, Ptr.add]
example (p : Ptr) : errPayloadPtr (Vector (BitVec 64) 0) p = p := by
  simp [errPayloadPtr, errUnionOffsets, Enc.size, Ptr.add]
example : Enc.size (Except ErrName (Vector (BitVec 64) 0)) = 8 ∧
    Enc.align (Except ErrName (Vector (BitVec 64) 0)) = 8 := by decide

end ErrorUnionAlignment
