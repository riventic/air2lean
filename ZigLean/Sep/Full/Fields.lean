import ZigLean.Sep.Full.Typed
import ZigLean.Sep.Full.AutoRules

/-!
# Typed fields of a region

A struct in an allocated region is used through its fields (`pts`: a typed value, the form that
loads and stores of generated code take), and handed back to its allocator as the region (a
grant's bytes, `FAllocInv.granted`). Two library lemmas convert between the forms, for any field
type:

* `region_pts_split`: the first `Enc.size T` bytes of a region whose bytes there decode to `v`
  are the typed value `v`; the rest stays a region with the same labels. A plain entailment.
* `EUpd.pts_region_join`: a typed value directly in front of a region of its block joins it
  into one region. A typed value hides its cells' labels (block address, size, kind), so the
  join reads them off the memory: two owned regions of one block carry the block's address and
  kind (`facts_regions_labels`), and the field's size label and kind are relabelled to the
  region's (`EUpd.relabel`). An update in the memory, not an entailment.

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig.Full

open FAssn

variable {T : Type} [Enc T] {p : Ptr} {A S a a' : Nat} {K : BlockKind} {bs : Array Byte} {v : T}

/-- **A typed field off the front of a region.** -/
theorem region_pts_split (hn : Enc.size T ≤ bs.size)
    (hv : Enc.decode (bs.extract 0 (Enc.size T)) = pure v)
    (ha' : (A + p.off.toNat + Enc.size T) % a' = 0) {r : Res} (h : up (regionIn p A S K a bs) r) :
    (up (pts p a v) ⋆ up (regionIn (p.add (Enc.size T)) A S K a' (bs.extract (Enc.size T) bs.size))) r := by
  obtain ⟨hr, hk, hg⟩ := h
  have hs := Region.regionIn_split hr hn ha'
  refine sep_mono (fun r' h' => up_pts_of_region (by simp; omega) hv ?_) (fun _ h' => h') (up_sep ⟨hs, hk, hg⟩)
  obtain ⟨hr', hk', hg'⟩ := h'
  exact ⟨Region.region_of_regionIn hr', hk', hg'⟩

/-- **A typed field joins the region behind it** (an update in the memory: the labels of the
field's cells are the block's, `facts_regions_labels`, and are relabelled, `EUpd.relabel`). -/
theorem EUpd.pts_region_join (hn : 0 < Enc.size T) (hbs : 0 < bs.size) :
    EUpd (up (pts p a v) ⋆ up (regionIn (p.add (Enc.size T)) A S K a' bs))
      (FAssn.ex fun cs : Array Byte =>
        ⟪cs.size = Enc.size T + bs.size ∧ Enc.decode (cs.extract 0 (Enc.size T)) = pure v ∧
          cs.extract (Enc.size T) cs.size = bs⟫ ⋆ up (regionIn p A S K a cs)) := by
  -- the field as a region with its own labels
  refine EUpd.trans (P' := (FAssn.ex fun fs : Array Byte => FAssn.ex fun A₁ : Nat =>
      FAssn.ex fun S₁ : Nat => FAssn.ex fun K₁ : BlockKind =>
        ⟪fs.size = Enc.size T ∧ Enc.decode fs = pure v⟫ ⋆ up (regionIn p A₁ S₁ K₁ a fs)) ⋆
      up (regionIn (p.add (Enc.size T)) A S K a' bs))
    (EUpd.of_imp fun r h => sep_mono_left (fun r' h' => ?_) h) ?_
  · obtain ⟨fs, hx⟩ := up_pts_iff.mp h'
    obtain ⟨hfs, ⟨A₁, S₁, K₁, hr⟩, hk⟩ := sep_lift.mp hx
    exact ⟨fs, A₁, S₁, K₁, sep_lift.mpr ⟨hfs, hr, hk⟩⟩
  refine EUpd.ex fun fs => ?_
  refine EUpd.trans (EUpd.of_imp fun _ h => sep_ex.mpr (sep_ex.mp h)) (EUpd.ex fun A₁ => ?_)
  refine EUpd.trans (EUpd.of_imp fun _ h => sep_ex.mpr (sep_ex.mp h)) (EUpd.ex fun S₁ => ?_)
  refine EUpd.trans (EUpd.of_imp fun _ h => sep_ex.mpr (sep_ex.mp h)) (EUpd.ex fun K₁ => ?_)
  refine EUpd.trans (EUpd.of_imp fun _ h => sep_assoc h) (EUpd.lift fun ⟨hfs, hv⟩ => ?_)
  -- the block of the field, and the labels of the two regions
  refine EUpd.withFact (φ := ∃ b, p.block = some b) (fun _ r _ _ h _ => ?_) fun ⟨b, hb⟩ => ?_
  · obtain ⟨r₁, r₂, _, _, h1, _⟩ := h
    obtain ⟨b, hb, _⟩ := h1.1.2.2
    exact ⟨b, hb⟩
  refine EUpd.trans (MemFacts.eupd (Auto.facts_regions_labels (p := p) (q := p.add (Enc.size T)) hb
    (by simpa [Ptr.add] using hb) (by omega) hbs)) (EUpd.lift fun ⟨hA, hK⟩ => ?_)
  subst hA
  refine EUpd.trans (EUpd.frame (EUpd.relabel (S' := S) (K' := K) hK.symm)) (EUpd.of_imp fun r h => ?_)
  refine ⟨fs ++ bs, sep_lift.mpr ⟨⟨by simp [hfs], by simp [← hfs, hv], by simp [← hfs]⟩, ?_⟩⟩
  obtain ⟨hr, hk, hg⟩ := sep_up h
  exact ⟨Region.regionIn_join (by rwa [hfs]), hk, hg⟩

end Zig.Full
