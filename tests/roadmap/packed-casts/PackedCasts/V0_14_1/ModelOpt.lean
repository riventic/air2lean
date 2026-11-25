import PackedCasts.V0_14_1.OptItems
import PackedCasts.Show

/-! `opt_items.zig` (Zig 0.14.1, 0.15.2; LLVM backend): kernel-checked results, then `main` prints
the lines of `native.zig`'s cases. It is written for Zig 0.15.2; the module of 0.14.1 is that one
with the version renamed (`check.sh`, `scripts/fixtures.py instance`). -/

open Zig PackedCasts.V0_14_1.OptItems PackedCastsShow

namespace PackedCasts.V0_14_1.ModelOpt

theorem u8sToInt_ok : (u8sToInt #v[some 0x12, some 0x34]).run = some (.ok 0x01340112#32) := by
  decide +kernel
/-- A null item's payload byte is undefined: the integer is `.unspecified`. -/
theorem u8sToInt_null : (u8sToInt #v[none, some 0x34]).run = some (.error .unspecified) := by
  decide +kernel
theorem intToU8s_ok : (intToU8s 0x01340012#32).run = some (.ok 0x34) := by decide +kernel
theorem intToU8s_null : (intToU8s 0x00340112#32).run = some (.ok 0x100) := by decide +kernel
/-- Item 1's flag byte holds 2: no flag, `.illegal` (native code reads it as non-null: the
model over-approximates, `README.md` §Scope). -/
theorem intToU8s_badFlag : (intToU8s 0x02340012#32).run = some (.error .illegal) := by
  decide +kernel
/-- `?u16`'s padding byte is undefined. -/
theorem u16sToInt_padding : (u16sToInt #v[some 0x1234, some 0x5678]).run =
    some (.error .unspecified) := by
  decide +kernel
theorem intToU16s_ok : (intToU16s 0xEE015678FF011234#64).run = some (.ok 0x5678) := by
  decide +kernel
theorem zerosToInt_ok : (zerosToInt #v[some 0, none, some 0, some 0]).run =
    some (.ok 0x01010001#32) := by
  decide +kernel
theorem intToZeros_ok : (intToZeros 0x01000101#32).run = some (.ok 3) := by decide +kernel
/-- Set bits above the `u12` in its payload bytes: `.unspecified`. -/
theorem intToU12s_highBits : (intToU12s 0xAA01FABC#64).run = some (.error .unspecified) := by
  decide +kernel
/-- The LLVM backend ignores the padding byte of a `u24` payload (`ModelOptX64`: the
self-hosted x86_64 backend does not). -/
theorem intToU24s_padding : (intToU24s 0x00000001771234560000000000000000#128).run =
    some (.ok 0x123456) := by
  decide +kernel
theorem intToBools_ok : (intToBools 0x01000101#32).run = some (.ok 7) := by decide +kernel
theorem arraysToInt_ok : (arraysToInt #v[some #v[1, 2, 3], some #v[4, 5, 6]]).run =
    some (.ok 0x0106050401030201#64) := by
  decide +kernel
theorem intToNested_inner : (intToNested 0x0100AA000000#48).run = some (.ok 0x100) := by
  decide +kernel

def main : IO Unit := do
  line "opt_u8sToInt" (u8sToInt #v[some 0x12, some 0x34])
  line "opt_nullToInt" (u8sToInt #v[none, some 0x34])
  line "opt_intToU8s" (intToU8s 0x01340012#32)
  line "opt_intToU8sNull" (intToU8s 0x00340112#32)
  line "opt_u16sToInt" (u16sToInt #v[some 0x1234, some 0x5678])
  line "opt_intToU16s" (intToU16s 0xEE015678FF011234#64)
  line "opt_zerosToInt" (zerosToInt #v[some 0, none, some 0, some 0])
  line "opt_intToZeros" (intToZeros 0x01000101#32)
  line "opt_intToU12s" (intToU12s 0xAA010ABC#64)
  line "opt_intToU24s" (intToU24s 0x00000001001234560000000000000000#128)
  line "opt_intToI8s" (intToI8s 0x01800000#32)
  line "opt_intToU64" (intToU64 0x10123456789ABCDEF#128)
  line "opt_intToU128" (intToU128 (BitVec.ofNat 256 (2 ^ 128 + 0x0123456789ABCDEFFEDCBA9876543210)))
  line "opt_boolsToInt" (boolsToInt #v[some true, some false])
  line "opt_intToBools" (intToBools 0x01000101#32)
  line "opt_intToF16" (intToF16 0x00013C00#32)
  line "opt_intToF32" (intToF32 0x13F800000#64)
  line "opt_intToF64" (intToF64 (BitVec.ofNat 128 (2 ^ 64 + 0x3FF0000000000000)))
  line "opt_intToF80" (intToF80 (BitVec.ofNat 256 (2 ^ 128 + 0x3FFF8000000000000000)))
  line "opt_intToF128" (intToF128 (BitVec.ofNat 256 (2 ^ 128 + 0x3FFF0000000000000000000000000000)))
  line "opt_enumsToInt" (enumsToInt #v[some .c, some .b])
  line "opt_intToEnums" (intToEnums 0x01020000#32)
  line "opt_arraysToInt" (arraysToInt #v[some #v[1, 2, 3], some #v[4, 5, 6]])
  line "opt_intToArrays" (intToArrays 0x0106050400030201#64)
  line "opt_gridToInt" (gridToInt #v[#v[some 1, some 2], #v[some 3, some 4]])
  line "opt_intToGrid" (intToGrid 0x0000010900000000#64)
  line "opt_nestedToInt" (nestedToInt #v[some (some 0x11), some (some 0x22)])
  line "opt_intToNested" (intToNested 0x010122000000#48)
  line "opt_intToNestedInner" (intToNested 0x0100AA000000#48)
  line "opt_intToExtern" (intToExtern 0x013412000000#48)
  line "opt_intToPacked" (intToPacked 0x0001ABC500000000#64)
  line "opt_intToAuto" (intToAuto 0x000100050010000000000000#96)
  line "opt_intToVector" (intToVector (BitVec.ofNat 256 (2 ^ 128 + 0x44444444333333332222222211111111)))

end PackedCasts.V0_14_1.ModelOpt
