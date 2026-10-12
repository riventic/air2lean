import Logical017.Gen
import Show

/-! The model's lines for `native.zig`'s cases of `logical017.zig` (Zig 0.17.0 only). -/

open Zig Logical017 PackedCastsShow

def f16 (b : Nat) : Zig.F16 := Zig.Float.ofBits (BitVec.ofNat 16 b)

def main : IO Unit := do
  line "nestedToInt" (nestedToInt #v[#v[1, 2, 3], #v[4, 5, 6]])
  line "intToNested0" ((·[0]) <$> intToNested 0xFEDCBA#24)
  line "intToNested1" ((·[1]) <$> intToNested 0xFEDCBA#24)
  line "modesToInt" (modesToInt #v[.low, .high, .off, .low])
  line "intToModes" (intToModes 0x26#8)
  line "nibsToInt" (nibsToInt #v[{ a := 1, m := .high, b := 3 }, { a := 2, m := .low, b := 0 },
    { a := 3, m := .off, b := 1 }])
  line "intToNibs" (intToNibs 0x21A5B#18)
  line "unionsToInt" (unionsToInt #v[Zig.Packed.ofBits 0x1234#16, Zig.Packed.ofBits 0x3c00#16])
  line "uToNibbles" (uToNibbles (Zig.Packed.ofBits 0xC0DE#16))
  line "nibblesToU" (nibblesToU #v[0xD, 0xE, 0xA, 0xF])
  line "halvesToVec" (halvesToVec #v[f16 0x3c00, f16 0xc000])
  line "vecToHalves" (vecToHalves ⟨#v[f16 0x3800, f16 0x4000]⟩)
  line "floatsToNested0" ((·[0]) <$> floatsToNested #v[f16 0x3c00, f16 0x8000])
  line "floatsToNested1" ((·[1]) <$> floatsToNested #v[f16 0x3c00, f16 0x8000])
