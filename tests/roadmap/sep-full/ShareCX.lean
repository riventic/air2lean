import ZigLean.Sep.Full.Extent
import ZigLean.Sep.Full.Share

/-!
# Read shares: regressions (`ZigLean/Sep/Full/Res.lean` §Read shares)

1. `halves_read`: two halves of one cell compose (validly) and both read that cell.
2. `disagree_invalid`: shares of two different cells of one byte do not compose, at any fractions.
3. `over_invalid`: fractions of one cell summing above `1` do not compose.
4. `whole_excludes`: next to the whole fraction a valid frame holds nothing.
5. `bytes_halves`: shared bytes split into two halves and join back.
6. `share_roundtrip`: exclusive bytes become the whole share and back.
7. `half_reads`: half a typed share reads the value and keeps the half.
8. `zero_no_spts`: a zero fraction is no typed share.

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

/-! ## Shared bytes (`ZigLean/Sep/Full/Share.lean`) -/

variable {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {tg : Option (Nat × Nat)}

/-- **The whole of the bytes splits into two halves, and two halves join back.** -/
theorem bytes_halves {r : Res} :
    sbytesAt p A S K bs tg Frac.one r ↔
      (sbytesAt p A S K bs tg Frac.one.half ⋆ sbytesAt p A S K bs tg Frac.one.half) r := by
  rw [← sbytesAt_add, Frac.half_add_half]

/-- **Exclusive bytes become the whole share and back.** -/
theorem share_roundtrip : EUpd (abytesAt p A S K bs tg) (abytesAt p A S K bs tg) :=
  EUpd.share_whole.trans EUpd.unshare_whole

/-- **Half a share reads the value** and keeps the half. -/
theorem half_reads {T : Type} [Enc T] {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    FTotalTriple (spts p a Frac.one.half v) (Zig.load T a p)
      (fun x => ⟪x = v⟫ ⋆ spts p a Frac.one.half v) :=
  FTotalTriple.sload hn

/-- **No share, no read**: a typed share holds a positive fraction. -/
theorem zero_no_spts {T : Type} [Enc T] {a : Nat} {v : T} {r : Res} :
    ¬ spts p a Frac.zero v r := fun h => by
  have := h.1; simp only [Frac.zero] at this; exact Rat.lt_irrefl this

#print axioms halves_read
#print axioms disagree_invalid
#print axioms over_invalid
#print axioms whole_excludes
#print axioms bytes_halves
#print axioms share_roundtrip
#print axioms half_reads
#print axioms zero_no_spts

end Zig.Full.ShareCX
