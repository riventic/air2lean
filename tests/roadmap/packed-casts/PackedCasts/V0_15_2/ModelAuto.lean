import PackedCasts.V0_15_2.AutoItems
import PackedCasts.Show

/-! `auto_items.zig` (Zig 0.14.1, 0.15.2): kernel-checked results, then `main` prints the lines of
`native.zig`'s cases. It is written for Zig 0.15.2; the module of 0.14.1 is that one with the
version renamed (`check.sh`, `scripts/fixtures.py instance`). -/

open Zig PackedCasts.V0_15_2.AutoItems PackedCastsShow

namespace PackedCasts.V0_15_2.ModelAuto

theorem structsToInt_ok : (structsToInt #v[{ a := 1, b := 2 }, { a := 3, b := 4 }]).run =
    some (.ok 0x0004000300020001#64) := by decide +kernel
theorem structB1_ok : (structB1 0x0004000300020001#64).run = some (.ok 4) := by decide +kernel
theorem unionPayload1_ok : (unionPayload1 0x0000BEEF00011234#64).run = some (.ok 0xBEEF) := by
  decide +kernel
/-- Item 1's tag byte holds 5: bits above the 1-bit tag are set, so the byte holds no tag. -/
theorem unionPayload1_badTag : (unionPayload1 0x0005BEEF00011234#64).run =
    some (.error .unspecified) := by
  decide +kernel
/-- The tagged unions' padding bytes are undefined: their integer is `.unspecified`. -/
theorem unionsToInt_padding : (unionsToInt #v[.a 0x1234, .b 0x56]).run = some (.error .unspecified) := by
  decide +kernel

def main : IO Unit := do
  line "structsToInt" (structsToInt #v[{ a := 1, b := 2 }, { a := 3, b := 4 }])
  line "structB1" (structB1 0x0004000300020001#64)
  line "unionPayload1" (unionPayload1 0x0000BEEF00011234#64)
  line "unionsToInt" (unionsToInt #v[.a 0x1234, .b 0x56])

end PackedCasts.V0_15_2.ModelAuto
