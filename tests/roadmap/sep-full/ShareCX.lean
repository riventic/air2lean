import ZigLean.Sep.Full.Extent
import ZigLean.Sep.Full.Share
import ZigLean.Sep.Full.ThreadStep

/-!
# Read shares: regressions (`ZigLean/Sep/Full/Res.lean` §Read shares)

1. `halves_read`: two halves of one cell compose (validly) and both read that cell.
2. `disagree_invalid`: shares of two different cells of one byte do not compose, at any fractions.
3. `over_invalid`: fractions of one cell summing above `1` do not compose.
4. `whole_excludes`: next to the whole fraction a valid frame holds nothing.
5. `mixed_tags`: shared bytes keep a tag per cell (an atomic field next to a plain one).
6. `bytes_halves`, `halves_join`: the whole share splits into two halves and joins back.
7. `pts_roundtrip`: `p ↦ v` becomes its whole share and back.
8. `half_reads`: half a typed share reads the value and keeps the half.
9. `share_no_store`: a share owns no byte as a cell, so no store or free rule applies.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Zig.Full.ShareCX

open Zig Zig.Full FAssn

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

variable {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte}

/-- **Each cell keeps its own tag**: plain bytes with any tag per cell (an atomic field next to
a plain one) are shared bytes, whole. -/
theorem mixed_tags {h : Heap} (hb : bytesAt p A S K bs h) (tag : Loc → Option (Nat × Nat)) :
    sbytesAt p A S K bs Frac.one
      ⟨FHeap.empty, Know.none, Ghost.sharesOf (fun l => (h l).map (⟨·, tag l⟩)) Frac.one⟩ := by
  refine ⟨_, ⟨?_, rfl, rfl⟩, rfl, rfl, rfl⟩
  have e : FHeap.erase (fun l => (h l).map (⟨·, tag l⟩)) = h := funext fun l => by
    simp only [FHeap.erase, Option.map_map]; cases h l <;> rfl
  show bytesAt p A S K bs (FHeap.erase _); rw [e]; exact hb

/-- **The whole share splits into two halves, and two halves join back.** -/
theorem bytes_halves {r : Res} (h : sbytesAt p A S K bs Frac.one r) :
    (sbytesAt p A S K bs Frac.one.half ⋆ sbytesAt p A S K bs Frac.one.half) r :=
  sbytesAt_split (by rw [Frac.half_add_half]; exact h)

theorem halves_join : EUpd (sbytesAt p A S K bs Frac.one.half ⋆ sbytesAt p A S K bs Frac.one.half)
    (sbytesAt p A S K bs Frac.one) := by
  have h := EUpd.sbytesAt_join (p := p) (A := A) (S := S) (K := K) (bs := bs)
    (q₁ := Frac.one.half) (q₂ := Frac.one.half) (Frac.half_pos (by decide))
    (Frac.half_pos (by decide))
  rwa [Frac.half_add_half] at h

/-- **`p ↦ v` becomes its whole share and back** (with `K ≠ .constGlobal` kept). -/
theorem pts_roundtrip {T : Type} [Enc T] {a : Nat} {v : T} :
    EUpd (up (pts p a v)) (spts p a Frac.one v) ∧ EUpd (spts p a Frac.one v) (up (pts p a v)) :=
  ⟨EUpd.spts_whole, EUpd.spts_unwhole⟩

/-- **Half a share reads the value** and keeps the half. -/
theorem half_reads {T : Type} [Enc T] {a : Nat} {v : T} (hn : 0 < Enc.size T) :
    FTotalTriple (spts p a Frac.one.half v) (Zig.load T a p)
      (fun x => ⟪x = v⟫ ⋆ spts p a Frac.one.half v) :=
  FTotalTriple.sload hn

/-- **A share licenses no store or free**: a typed share owns no byte as a cell (`OwnsPtr`, the
premise of the thread store and free rules), whatever its fraction. -/
theorem share_no_store {T : Type} [Enc T] {a : Nat} {v : T} {q : Frac} {r : Res} {b : BlockId}
    {n : Nat} (hr : spts p a q v r) (hb : p.block = some b) (hn : 0 < n) :
    ¬ OwnsPtr (spts p a q v) p n := fun h => by
  have ⟨_, _, _, hH, _, _⟩ := hr
  exact h b hb r hr p.off.toNat (Nat.le_refl _) (by omega) (by rw [hH]; rfl)

#print axioms halves_read
#print axioms disagree_invalid
#print axioms over_invalid
#print axioms whole_excludes
#print axioms mixed_tags
#print axioms bytes_halves
#print axioms halves_join
#print axioms pts_roundtrip
#print axioms half_reads
#print axioms share_no_store

end Zig.Full.ShareCX
