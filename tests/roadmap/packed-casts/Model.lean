import PackedCasts.Gen
import Show

/-! The model's lines for `native.zig`'s cases of `packed_casts.zig`, from the translation of one
Zig version's export (`check.sh` puts it at `PackedCasts.Gen`). -/

open Zig PackedCasts PackedCastsShow

def f16 (b : Nat) : Zig.F16 := Zig.Float.ofBits (BitVec.ofNat 16 b)
def f32 (b : Nat) : Zig.F32 := Zig.Float.ofBits (BitVec.ofNat 32 b)

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
