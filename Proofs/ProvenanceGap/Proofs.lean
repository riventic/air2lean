import Proofs.ProvenanceGap.Gen

/-!
# Proofs about `assurance/provenance-gap/src/gap.zig`

`gap a b` is the unsigned distance between two 32-bit values and `within a b t` tests that
distance against a tolerance. Both are total-correctness statements about the generated code. The
point of this module is that its theorem names, the fresh schema-12 aarch64-macos `Gen.lean` and the
audited receipt are chained by `assurance/provenance-gap/manifest.json` (docs/artifact-manifest.md).
-/

open ProvenanceGap

theorem gap_eq (a b : BitVec 32) :
    gap a b = pure (if b.toNat < a.toNat then a - b else b - a) := by
  by_cases h : b.toNat < a.toNat
  · have : ¬ a.toNat < b.toNat := by omega
    simp [gap, zig_unfold, h, this]
  · simp [gap, zig_unfold, h]

theorem within_eq (a b t : BitVec 32) :
    within a b t =
      pure (decide ((if b.toNat < a.toNat then a - b else b - a).toNat ≤ t.toNat)) := by
  simp [within, gap_eq, zig_unfold, Zig.call, Zig.le, BitVec.ule]
