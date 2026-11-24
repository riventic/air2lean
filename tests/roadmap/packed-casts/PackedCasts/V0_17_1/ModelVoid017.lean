import PackedCasts.V0_17_1.Void017
import PackedCasts.Show

/-! `void017.zig` (Zig 0.17.1 only: `void` itself in a `@bitCast`): kernel-checked results, then
`main` prints the lines of `native.zig`'s cases. Sema folds these casts (`ModelVoidCast` has the
instruction). -/

open Zig PackedCasts.V0_17_1.Void017 PackedCastsShow

namespace PackedCasts.V0_17_1.ModelVoid017

theorem voidToInt_ok : Runs.result (voidToInt ()) = some (.ok 0) := by decide +kernel
theorem intToVoid_ok : Runs.result (intToVoid 0) = some (.ok ()) := by decide +kernel
theorem emptyToVoid_ok : Runs.result (emptyToVoid #v[]) = some (.ok ()) := by decide +kernel
theorem voidToVoids_ok : Runs.result (voidToVoids ()) = some (.ok 3) := by decide +kernel

def main : IO Unit := do
  lineR "voidToInt" (voidToInt ())
  lineR "intToVoid" (intToVoid 0)
  lineR "emptyToVoid" (emptyToVoid #v[])
  lineR "voidToVoids" (voidToVoids ())

end PackedCasts.V0_17_1.ModelVoid017
