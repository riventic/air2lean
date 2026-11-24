import PackedCasts.V0_16_0.VoidCast

/-! The Zig ≤0.16 memory `@bitCast` of zero-bit types as an instruction
(`air-handwritten/0.16.0/void_cast`: Sema folds such a cast, so no compiler emits it). An array
of `void` and `u0` have no bytes; `Zig.reprCast` decodes the one from the other's empty image.
Kernel-checked results. -/

open Zig PackedCasts.V0_16_0.VoidCast

namespace PackedCasts.V0_16_0.ModelVoidCast

/-- `[4]void` to `u0`. -/
theorem voidsToInt_ok : voidsToInt.run = some (.ok 0#0) := by decide +kernel
/-- `u0` to `[4]void`. -/
theorem intToVoids_ok : intToVoids.run = some (.ok #v[(), (), (), ()]) := by decide +kernel

end PackedCasts.V0_16_0.ModelVoidCast
