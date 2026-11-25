import PackedCasts.V0_15_2.SentinelArrays
import PackedCasts.Show

/-! `sentinel_arrays.zig` (Zig 0.14.1, 0.15.2, 0.16.0): kernel-checked results, then `main`
prints the lines of `native.zig`'s cases. A sentinel-terminated array `[n:s]T` is `n + 1` items
(`Vector T (n+1)`): the sentinel is the last item of the value, of its memory image and of its
bits. It is written for Zig 0.16.0; the modules of 0.15.2 and 0.14.1 are that one with the
version renamed (`check.sh`, `scripts/fixtures.py instance`). The versions' translations differ
in where a local lives (`PackedCastsShow.Runs`). -/

open Zig PackedCasts.V0_15_2.SentinelArrays PackedCastsShow

namespace PackedCasts.V0_15_2.ModelSentinel

/-- The sentinel 7 is the top byte. -/
theorem sentToInt_ok : Runs.result (sentToInt #v[0x11, 2, 3, 7]) = some (.ok 0x07030211#32) := by
  decide +kernel
/-- The last item is in the bits whatever it is: the cast does not read the type's sentinel. -/
theorem sentToInt_lastItem : Runs.result (sentToInt #v[0x11, 2, 3, 0xFF]) =
    some (.ok 0xFF030211#32) := by decide +kernel
theorem wideToInt_ok : Runs.result (wideToInt #v[0x77, 2, 3, 0x1234]) =
    some (.ok 0x1234000300020077#64) := by decide +kernel
/-- Each inner array has its own sentinel item. -/
theorem nestedToInt_ok : Runs.result (nestedToInt #v[#v[0x11, 2, 3, 5], #v[4, 5, 6, 5]]) =
    some (.ok 0x0506050405030211#64) := by decide +kernel
theorem sentItem3_ok : Runs.result (sentItem3 #v[0x11, 2, 3, 9]) = some (.ok 9) := by
  decide +kernel
theorem intToSentAt_first : Runs.result (intToSentAt 0xAABBCCDD 0) = some (.ok 0xDD) := by
  decide +kernel
/-- The result's last item is the top byte of the integer, not the type's sentinel 0. -/
theorem intToSentAt_last : Runs.result (intToSentAt 0xAABBCCDD 3) = some (.ok 0xAA) := by
  decide +kernel
/-- The round trip keeps every bit: no padding, every byte defined
(`ZigLean.ReprCast.reprCast_roundtrip`'s condition). -/
theorem roundTrip_ok : Runs.result (roundTrip 0xAABBCCDD) = some (.ok 0xAABBCCDD) := by
  decide +kernel

def main : IO Unit := do
  lineR "sentToInt" (sentToInt #v[0x11, 2, 3, 7])
  lineR "wideToInt" (wideToInt #v[0x77, 2, 3, 0x1234])
  lineR "nestedToInt" (nestedToInt #v[#v[0x11, 2, 3, 5], #v[4, 5, 6, 5]])
  lineR "sentItem3" (sentItem3 #v[0x11, 2, 3, 9])
  lineR "intToSentAt0" (intToSentAt 0xAABBCCDD 0)
  lineR "intToSentAt3" (intToSentAt 0xAABBCCDD 3)
  lineR "roundTrip" (roundTrip 0xAABBCCDD)
  -- Zig 0.14.1 leaves the sentinel of this runtime initialization unwritten: `unspecified`.
  lineR "sentInit" (sentInit 0x11)

end PackedCasts.V0_15_2.ModelSentinel
