import PackedCasts.V0_17_1.VoidCast

/-! The Zig 0.17 logical `@bitCast` of zero-bit types as an instruction
(`air-handwritten/0.17.1/void_cast`: Sema folds such a cast, so no compiler emits it). `void`
has no bits (`Zig.Packed Unit 0`), alone and as an array element; the cast goes through
`BitVec 0`. Kernel-checked results. -/

open Zig PackedCasts.V0_17_1.VoidCast

namespace PackedCasts.V0_17_1.ModelVoidCast

/-- `[4]void` to `u0`. -/
theorem voidsToInt_ok : voidsToInt.run = some (.ok 0#0) := by decide +kernel
/-- `u0` to `[4]void`. -/
theorem intToVoids_ok : intToVoids.run = some (.ok #v[(), (), (), ()]) := by decide +kernel
/-- `void` to `u0`. -/
theorem voidToInt_ok : voidToInt.run = some (.ok 0#0) := by decide +kernel
/-- `void` to `[4]void`. -/
theorem voidToVoids_ok : voidToVoids.run = some (.ok #v[(), (), (), ()]) := by decide +kernel

end PackedCasts.V0_17_1.ModelVoidCast
