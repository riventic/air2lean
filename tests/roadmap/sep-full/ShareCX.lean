import ZigLean.Sep.Full.Extent

/-!
# Read shares: regressions (`ZigLean/Sep/Full/Res.lean` §Read shares)

1. `halves_read`: two halves of one cell compose (validly) and both read that cell.
2. `disagree_invalid`: shares of two different cells of one byte do not compose, at any fractions.
3. `over_invalid`: fractions of one cell summing above `1` do not compose.
4. `whole_excludes`: next to the whole fraction a valid frame holds nothing.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Zig.Full.ShareCX

open Zig Zig.Full

/-- **Two halves of one cell compose and read it.** -/
theorem halves_read (c : FCell) :
    ((SCell.of c Frac.one.half).add (SCell.of c Frac.one.half)).Valid ∧
      ((SCell.of c Frac.one.half).add (SCell.of c Frac.one.half)).cell = some c := by
  rw [SCell.of_add, Frac.half_add_half]
  have hv : (SCell.of c Frac.one).Valid := SCell.valid_of (by decide)
  refine ⟨hv, SCell.cell_eq_some hv ?_⟩
  rw [SCell.of_self]; decide

/-- **Shares of different cells of one byte do not compose.** -/
theorem disagree_invalid {c c' : FCell} (h : c ≠ c') {q q' : Frac} (hq : 0 < q.val)
    (hq' : 0 < q'.val) : ¬ ((SCell.of c q).add (SCell.of c' q')).Valid := fun hv =>
  h (hv.1 c c' (SCell.pos_add _ (by rw [SCell.of_self]; exact hq))
    (SCell.pos_add' _ (by rw [SCell.of_self]; exact hq')))

/-- **More than the whole of a cell does not compose.** -/
theorem over_invalid (c : FCell) : ¬ ((SCell.of c Frac.one).add (SCell.of c Frac.one.half)).Valid :=
  fun hv => by
    have h := hv.2 c
    rw [SCell.add_val, SCell.of_self, SCell.of_self] at h
    simp only [Frac.one, Frac.half] at h; grind

/-- **The whole fraction leaves a valid frame nothing.** -/
theorem whole_excludes (c : FCell) {b : SCell} (hv : ((SCell.of c Frac.one).add b).Valid) :
    b.Empty :=
  hv.whole (by rw [SCell.of_self]; rfl)

#print axioms halves_read
#print axioms disagree_invalid
#print axioms over_invalid
#print axioms whole_excludes

end Zig.Full.ShareCX
