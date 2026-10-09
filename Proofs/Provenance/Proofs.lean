import Proofs.Provenance.Gen

/-!
# Proofs about `assurance/provenance/src/provenance.zig`

`add` is wrapping 32-bit addition and `double x = add x x`. These are small total-correctness
statements; the point of this module is that its theorem names, the fresh schema-12 `Gen.lean`
and the audited receipt are chained by `assurance/provenance/manifest.json` (docs/artifact-manifest.md).
-/

open Provenance

theorem add_eq (a b : BitVec 32) : add a b = pure (a + b) := by
  simp [add, zig_unfold, Zig.addWrap]

theorem double_eq (x : BitVec 32) : double x = pure (x + x) := by
  simp [double, add, zig_unfold, Zig.addWrap, Zig.call]
