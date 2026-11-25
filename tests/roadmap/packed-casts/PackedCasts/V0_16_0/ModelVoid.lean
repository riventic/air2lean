import PackedCasts.V0_16_0.VoidCasts
import PackedCasts.Show

/-! `void_casts.zig` (every version): kernel-checked results, then `main` prints the lines of
`native.zig`'s cases. Sema folds a cast of a zero-bit type, so these translations hold its
result as a constant; `ModelVoidCast` has the instruction. It is written for Zig 0.17.1; the
modules of 0.16.0, 0.15.2 and 0.14.1 are that one with the version renamed (`check.sh`,
`scripts/fixtures.py instance`). -/

open Zig PackedCasts.V0_16_0.VoidCasts PackedCastsShow

namespace PackedCasts.V0_16_0.ModelVoid

theorem voidsToInt_ok : Runs.result (voidsToInt #v[(), (), (), ()]) = some (.ok 0) := by
  decide +kernel
theorem intToVoids_ok : Runs.result (intToVoids 0) = some (.ok 4) := by decide +kernel
theorem emptyToInt_ok : Runs.result (emptyToInt #v[]) = some (.ok 0) := by decide +kernel

def main : IO Unit := do
  lineR "voidsToInt" (voidsToInt #v[(), (), (), ()])
  lineR "intToVoids" (intToVoids 0)
  lineR "emptyToInt" (emptyToInt #v[])

end PackedCasts.V0_16_0.ModelVoid
