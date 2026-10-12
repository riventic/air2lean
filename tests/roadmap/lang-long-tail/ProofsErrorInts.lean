import LangLongTail.ErrorInts
import ZigLean.Mem.ErrWidthLemmas

/-!
# L10: integer/error casts, on the retained translation

`LangLongTail.ErrorInts` is the translation of `air/error_ints/0.16.0`, the compilation of
`probe_error_ints.zig`. `errorTable` is the numbering the patched compiler wrote after analysis
(`error-table.air2lean`), the numbering of the native program (`ModelErrorInts.lean` compares
the codes and names). The theorems hold for every code and every numbered error, not for sampled
ones: the casts invert each other, the safety check before `@errorFromInt` rejects exactly the
codes without an error, and a code survives a store and a load in memory.
-/

open ErrorInts Zig

namespace ErrorIntsClients

/-- The exported numbering names each error once and fits the 16-bit error integer. -/
theorem errorTable_nodup : errorTable.toList.Nodup := by decide +kernel

theorem errorTable_fits : errorTable.size ≤ errCapacity 16 := by decide +kernel

/-- `@errorFromInt` of every valid code is the error of that code. -/
theorem back_valid (c : BitVec 16) (h0 : 0 < c.toNat) (hle : c.toNat ≤ errorTable.size) :
    back c = pure errorTable[c.toNat - 1] := by
  have hne : c ≠ 0#16 := by intro h; subst h; simp at h0
  simp [back, hle, hne, errorFromIntIn_valid _ c h0 hle, zig_unfold]

/-- Code 0 and every code past the error count are the safety panic `invalid error code`. -/
theorem back_invalid (c : BitVec 16) (h : c.toNat = 0 ∨ errorTable.size < c.toNat) :
    back c = throw .panic := by
  rcases h with h | h
  · have : c = 0 := BitVec.eq_of_toNat_eq (by simpa using h)
    subst this; simp [back, zig_unfold]
  · have : ¬ c.toNat ≤ errorTable.size := by omega
    simp [back, this, zig_unfold]

/-- The round trip through the integer keeps every error of the numbering. -/
theorem roundTrip_spec (e : ErrName) (he : e ∈ errorTable) : roundTrip e = pure true := by
  obtain ⟨c, hc, h0, hle, hback⟩ := intFromErrorIn_spec errorTable errorTable_nodup errorTable_fits he
  have hne : c ≠ 0#16 := by intro h; subst h; simp at h0
  simp [roundTrip, hc, hle, hne, hback, zig_unfold]

/-- `@intFromError` on `E`: the codes of the native program (`native/error_ints-0.16.0.txt`). -/
theorem code_values : (code "Alpha").run = some (.ok 166) ∧ (code "Beta").run = some (.ok 167) ∧
    (code "Gamma").run = some (.ok 168) := by
  decide +kernel

end ErrorIntsClients
