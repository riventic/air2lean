import Logical017.Gen
import Show

/-! `logical017.zig` (Zig 0.17.0 only): kernel-checked results, then `main` prints the lines of
`native.zig`'s cases. -/

open Zig Logical017 PackedCastsShow

def f16 (b : Nat) : Zig.F16 := Zig.Float.ofBits (BitVec.ofNat 16 b)

namespace Logical017Model

theorem nestedToInt_ok : (nestedToInt #v[#v[1, 2, 3], #v[4, 5, 6]]).run = some (.ok 0x654321#24) := by
  decide +kernel
theorem nested_roundtrip : (intToNested 0xFEDCBA#24 >>= nestedToInt).run = some (.ok 0xFEDCBA#24) := by
  decide +kernel
theorem modesToInt_ok : (modesToInt #v[.low, .high, .off, .low]).run = some (.ok 0x49#8) := by
  decide +kernel
/-- An item tag without a name: Zig 0.17 checks only a scalar enum result, so this is unchecked
illegal behaviour. -/
theorem intToModes_unnamed : (intToModes 0x03#8).run = some (.error .illegal) := by decide +kernel
theorem nibs_roundtrip : (intToNibs 0x21A5B#18 >>= nibsToInt).run = some (.ok 0x21A5B#18) := by
  decide +kernel
theorem unionsToInt_ok :
    (unionsToInt #v[Zig.Packed.ofBits 0x1234#16, Zig.Packed.ofBits 0x3c00#16]).run =
      some (.ok 0x3c001234#32) := by decide +kernel
theorem uToNibbles_ok : ((uToNibbles (Zig.Packed.ofBits 0xC0DE#16)).map (·.toList)).run =
    some (.ok [0xe, 0xd, 0x0, 0xc]) := by decide +kernel
theorem halvesToVec_ok : ((halvesToVec #v[f16 0x3c00, f16 0xc000]).map (·.lanes.toList)).run =
    some (.ok [0x00, 0x3c, 0x00, 0xc0]) := by decide +kernel
/-- A NaN lane has no determined bits. -/
theorem vecToHalves_nan : (vecToHalves ⟨#v[f16 0x7e00, f16 0x4000]⟩).run = some (.error .unspecified) := by
  decide +kernel

/-- A NaN field of a packed struct has no determined bits. -/
theorem fhToBytes_nan : (fhToBytes { lo := f16 0x7e00, hi := 0x1234 }).run = some (.error .unspecified) := by
  decide +kernel

end Logical017Model

open Logical017Model

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
  line "fhToBytes" (fhToBytes { lo := f16 0xc000, hi := 0x1234 })
