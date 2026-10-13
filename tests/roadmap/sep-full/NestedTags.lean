import ZigLean.Sep.Full.Extent

/-!
# Nested tags: an outer reset revokes the inner shares transitively (regression,
`docs/sep-full-state.md` §Nested tags)

An arena whose child is an arena gets node shares that are already tagged by the outer arena's
ledger. It lends sub-shares off them under its own ledger, whose parent tag is the outer tag
(`Upd.alloc (some (γo, 0))`, `EUpd.lendT` from a share tagged with the parent). The scenario, at
the ghost level, on one block `b` of `S` bytes:

1. the outer ledger `γo` (no parent) lends half of the block's extent as a share tagged
   `(γo, 0)` (the outer arena's grant: the inner arena's node);
2. the inner ledger `γi` (parent `(γo, 0)`) lends that share on as a share tagged `(γi, 0)` (the
   inner arena's grant to its client);
3. the outer arena resets: `Upd.bump` of `γo` and `EUpd.revoke` of its receipt. The outer share
   returns untagged and joins the authority: the **full extent** is back, while the inner
   ledger, the inner client's share and the inner receipt are all still held.

`nested_reset` is that update. `inner_dead` shows that the inner client's tag is inactive in every
memory that holds the result, so its share gives no bound (`Holds.bshare` needs an active tag),
and `full_excl` applies to the block although the inner share was never given back.
-/

namespace Zig.Full.NestedCX
open FAssn

variable {b : BlockId} {S k : Nat} {K : BlockKind}

/-- Half of the whole fraction. -/
def hf : Frac := Frac.one.half

theorem hf_pos : 0 < hf.val := Frac.half_pos (by decide)

theorem EUpd.exE {α : Type} {P : α → FAssn} {Q : FAssn} (h : ∀ x, EUpd (P x) Q) : EUpd (FAssn.ex P) Q :=
  fun m r rF hh ⟨x, hp⟩ hs => h x m r rF hh hp hs

/-- A ghost update from nothing, next to anything. -/
theorem upd_emp {P Q : FAssn} (h : Upd emp Q) : EUpd P (Q ⋆ P) :=
  EUpd.trans (EUpd.of_imp fun _ h => sep_comm (sep_emp.mpr h)) (EUpd.of_upd (Upd.frame h))

theorem ex_sep {α : Type} {P : α → FAssn} {Q : FAssn} : EUpd (FAssn.ex P ⋆ Q) (FAssn.ex fun x => P x ⋆ Q) :=
  EUpd.of_imp fun _ h => sep_ex.mp h

/-- **The outer reset revokes the inner shares**: from the full extent, through an outer grant, an
inner ledger under it and an inner grant, to the full extent again after the outer reset, with
the inner ledger, the inner client's share and the inner receipt still held. -/
theorem nested_reset (hk : k ≤ S) :
    EUpd (bext b S K)
      (FAssn.ex fun γo => FAssn.ex fun γi =>
        bext b S K ⋆ (gauth γo 1 GMap.empty ⋆ (gauthP γi 0 GMap.empty (some (γo, 0)) ⋆
          (bshare b hf k (some (γi, 0)) ⋆ brcpt b hf k γi 0)))) := by
  have hq : hf.add hf = Frac.one := Frac.half_add_half Frac.one
  refine EUpd.trans (upd_emp (Upd.alloc none)) (EUpd.trans ex_sep (EUpd.exE fun γo => ?_))
  refine EUpd.trans (EUpd.frame EUpd.dropEp) ?_
  -- the outer arena's node: half of the extent, tagged `(γo, 0)`
  refine EUpd.trans (P' := gauthP γo 0 GMap.empty none ⋆ bauth b S K (hf.add hf))
    (EUpd.of_imp fun _ h => by rw [hq]; exact h) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.lend (b := b) (K := K) hk hf_pos)) ?_
  refine EUpd.trans (P' := bauth b S K hf ⋆ (gauthP γo 0 GMap.empty none ⋆ bshare b hf k none))
    (EUpd.of_imp fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.lendT (Nat.le_refl k))) ?_
  -- the inner arena's ledger, with the outer tag as its parent, and its grant
  refine EUpd.trans (upd_emp (Upd.alloc (some (γo, 0)))) (EUpd.trans ex_sep (EUpd.exE fun γi => ?_))
  refine EUpd.trans (EUpd.frame EUpd.dropEp) ?_
  refine EUpd.trans (P' := (bauth b S K hf ⋆ (gauthP γo 0 GMap.empty none ⋆ brcpt b hf k γo 0)) ⋆
      (gauthP γi 0 GMap.empty (some (γo, 0)) ⋆ bshare b hf k (some (γo, 0))))
    (EUpd.of_imp fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frameL (EUpd.lendT (Nat.le_refl k))) ?_
  -- the outer reset: next epoch, then revoke the outer receipt and take the extent back
  refine EUpd.trans (P' := (gauthP γo 0 GMap.empty none ⋆ (bauth b S K hf ⋆ brcpt b hf k γo 0)) ⋆
      (gauthP γi 0 GMap.empty (some (γo, 0)) ⋆ (bshare b hf k (some (γi, 0)) ⋆ brcpt b hf k γi 0)))
    (EUpd.of_imp fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (EUpd.of_upd (Upd.frame Upd.bump))) ?_
  refine EUpd.trans (EUpd.frame (EUpd.frame EUpd.dropEp)) ?_
  refine EUpd.trans (P' := (bauth b S K hf ⋆ (gauthP γo (0 + 1) GMap.empty none ⋆ brcpt b hf k γo 0)) ⋆
      (gauthP γi 0 GMap.empty (some (γo, 0)) ⋆ (bshare b hf k (some (γi, 0)) ⋆ brcpt b hf k γi 0)))
    (EUpd.of_imp fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame (EUpd.frameL (EUpd.revoke (Nat.zero_lt_one)))) ?_
  refine EUpd.trans (P' := (bauth b S K hf ⋆ bshare b hf k none) ⋆ (gauthP γo (0 + 1) GMap.empty none ⋆
      (gauthP γi 0 GMap.empty (some (γo, 0)) ⋆ (bshare b hf k (some (γi, 0)) ⋆ brcpt b hf k γi 0))))
    (EUpd.of_imp fun _ h => of_eq (by ac_rfl) h) ?_
  refine EUpd.trans (EUpd.frame EUpd.unlend) (EUpd.of_imp fun _ h => ⟨γo, γi, ?_⟩)
  rw [hq] at h; exact h

/-- **The inner client's tag is dead** after the outer reset: its ledger is at its epoch, but its
parent tag `(γo, 0)` is past. So the inner share gives no bound (`Holds.bshare`), and nothing the
inner arena's clients kept stops the outer arena from shrinking or freeing the block. -/
theorem inner_dead {γo γi : Nat} {R : FAssn} {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (h : (gauth γo 1 GMap.empty ⋆ (gauthP γi 0 GMap.empty (some (γo, 0)) ⋆ R)) r) :
    ¬ Act (r.gh.add rF.gh).ls (some (γi, 0)) := by
  have hu := hh.ghost.1.1.uniq
  obtain ⟨r₁, r₂₃, -, rfl, ⟨-, -, g1⟩, r₂, r₃, -, rfl, ⟨-, -, g2⟩, -⟩ := h
  have ho : (((r₁.gh.add (r₂.gh.add r₃.gh))).add rF.gh).ls γo 1 none :=
    Ghost.ls_add _ _ _ _ _ (Ghost.ls_add _ _ _ _ _ (by rw [g1]; exact Ghost.at_auth1_ls))
  have hi : (((r₁.gh.add (r₂.gh.add r₃.gh))).add rF.gh).ls γi 0 (some (γo, 0)) :=
    Ghost.ls_add _ _ _ _ _ (Ghost.ls_add' _ _ _ _ _ (Ghost.ls_add _ _ _ _ _
      (by rw [g2]; exact Ghost.at_auth1_ls)))
  intro ha
  obtain ⟨p, h1, h2⟩ := ha.inv
  rw [(hu _ _ _ _ _ h1 hi).2] at h2
  obtain ⟨p', h3, -⟩ := h2.inv
  have := (hu _ _ _ _ _ h3 ho).1
  omega

end Zig.Full.NestedCX

-- The regression and the rules it uses (axioms: propext, Classical.choice, Quot.sound only).
#print axioms Zig.Full.NestedCX.nested_reset
#print axioms Zig.Full.NestedCX.inner_dead
#print axioms Zig.Full.Ghost.valid_led_change
