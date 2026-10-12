import PackedCasts.Gen
import Show

/-! `packed_casts.zig` from the translation of one Zig version's export (`check.sh` puts it at
`PackedCasts.Gen`, for each of 0.14.1, 0.15.2, 0.16.0 and 0.17.0): kernel-checked results, then
`main` prints the lines of `native.zig`'s cases. -/

open Zig PackedCasts PackedCastsShow

def f16 (b : Nat) : Zig.F16 := Zig.Float.ofBits (BitVec.ofNat 16 b)
def f32 (b : Nat) : Zig.F32 := Zig.Float.ofBits (BitVec.ofNat 32 b)

/-- The result of running `f` from the translation's initial memory. -/
def result {α : Type} (f : MemM α) : Option (Except Error α) :=
  ((f.run (mem0 .fresh)).run).map (·.map Prod.fst)

/-! ## Bit-pointer accesses: a packed union and floats as packed-struct fields (L08) -/

theorem setUnion_ok : result setUnion = some (.ok 0x1234) := by decide +kernel
theorem unionKeepsA_ok : result unionKeepsA = some (.ok 9) := by decide +kernel
theorem unionHalfHi_ok : result unionHalfHi = some (.ok 0x22) := by decide +kernel
theorem unionFloatView_ok : result unionFloatView = some (.ok 0x3c00) := by decide +kernel
theorem setFloat_ok : result setFloat = some (.ok 0x3e00) := by decide +kernel
theorem floatKeepsNeighbours_ok : result floatKeepsNeighbours = some (.ok 5) := by decide +kernel
theorem floatInPlace_ok : result (floatInPlace (f16 0x3d00)) = some (.ok (f16 0x4100)) := by
  decide +kernel
theorem wideFloat_ok : result (wideFloat (f32 0x40600000)) = some (.ok (f32 0x40600000)) := by
  decide +kernel

/-! ## Whole-value casts (L07, L08) -/

theorem rToInt_intToR : (intToR 0x1234567890#40 >>= rToInt).run = some (.ok 0x1234567890#40) := by
  decide +kernel
theorem makeR_ok : (makeR 0xA (f16 0x3c00)).run = some (.ok 0x23c003c00a#40) := by decide +kernel
/-- A NaN field has no determined bits: its struct's bits are `.unspecified`. -/
theorem floatField_nan : (floatField (f16 0x7e00)).run = some (.error .unspecified) := by
  decide +kernel
theorem uToBytes_ok : ((uToBytes (Zig.Packed.ofBits 0xABCD#16)).map (·.toList)).run =
    some (.ok [0xcd, 0xab]) := by decide +kernel
theorem bytesToU_uToHalf : (bytesToU #v[0x34, 0x12] >>= uToHalf).run =
    some (.ok { lo := 0x34, hi := 0x12 }) := by decide +kernel
theorem halfToF16_ok : (halfToF16 { lo := 0x00, hi := 0x3C }).run = some (.ok (f16 0x3c00)) := by
  decide +kernel
theorem floatsToInt_ok : (floatsToInt #v[f32 0x3f800000, f32 0xc0000000]).run =
    some (.ok 0xc00000003f800000#64) := by decide +kernel
theorem intToFloats_ok : ((intToFloats 0x40400000BF800000#64).map (·.toList)).run =
    some (.ok [f32 0xbf800000, f32 0x40400000]) := by decide +kernel
theorem vecToInt_ok : (vecToInt ⟨#v[f32 0x3f000000, f32 0x40800000]⟩).run =
    some (.ok 0x408000003f000000#64) := by decide +kernel

def main : IO Unit := do
  let m := mem0 .fresh
  lineM "setUnion" m setUnion
  lineM "unionKeepsA" m unionKeepsA
  lineM "unionHalfHi" m unionHalfHi
  lineM "unionFloatView" m unionFloatView
  lineM "setFloat" m setFloat
  lineM "floatKeepsNeighbours" m floatKeepsNeighbours
  lineM "floatInPlace" m (floatInPlace (f16 0x3d00))
  lineM "wideFloat" m (wideFloat (f32 0x40600000))
  line "wToInt" (wToInt (Zig.Packed.ofBits 0x00000E5F3F800000#64))
  line "rToInt" (rToInt (Zig.Packed.ofBits 0x5A3C001234#40))
  line "intToR" (intToR 0x1234567890#40 >>= rToInt)
  line "makeR" (makeR 0xA (f16 0x3c00))
  line "floatField" (floatField (f16 0xb800))
  line "floatFieldNaN" (floatField (f16 0x7e00))
  line "uToBytes" (uToBytes (Zig.Packed.ofBits 0xABCD#16))
  line "bytesToU" (bytesToU #v[0x34, 0x12])
  line "uToHalf" (uToHalf (Zig.Packed.ofBits 0xBEEF#16))
  line "halfToF16" (halfToF16 { lo := 0x00, hi := 0x3C })
  line "f16ToU" (f16ToU (f16 0xbc00))
  line "floatsToInt" (floatsToInt #v[f32 0x3f800000, f32 0xc0000000])
  line "intToFloats" (intToFloats 0x40400000BF800000#64)
  line "vecToInt" (vecToInt ⟨#v[f32 0x3f000000, f32 0x40800000]⟩)
  line "intToVec" (intToVec 0x3F800000C0000000#64)
