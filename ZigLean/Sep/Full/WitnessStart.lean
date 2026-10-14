import ZigLean.Sep.Full.Witness
import ZigLean.Sep.Full.Init
import ZigLean.Sep.Full.Claims

/-!
# Admissible inputs built from the start memory (`docs/claim-strength.md` §Witnesses)

A non-vacuity witness of a full-state claim shows its precondition `P` in some `Mem.FSeq` memory
(`FAdmit P`). A precondition over an allocator's invariant holds ghost state that only updates
create: shares of a block's extent lent out of its authority (`EUpd.lend`), byte-range claims
(`bclaim`), the persistent vtable (`vtR_intro`). Such a precondition is shown admissible in the
memory at program start (`FAdmit.init_claims`) and carried there by the updates that create its
ghost state, which change the resources and not the memory:

* `FAdmit.eupd`: an update keeps admissibility;
* `FAdmit.frame`: a part of an admissible input is one (the rest joins the frame);
* `FAdmit.ex`: an admissible existential has an admissible instance (`sep_ex_eq_right` with
  `sep_ex_eq` moves a start resource's existentials outside);
* `FAdmit.init_claims`: the globals at program start (`globals`, `FAdmit.init`) **with the claim
  on every global's bytes** (`gclaims`). Claims are created with their block
  (`FTriple.mintClaim`); no one holds a claim at program start, so the start resource can hold
  all of them (`Holds.addClaim`).

The bound of owned bytes below `2 ^ 63` (the memory's live layout) is a facts lemma of `fsym`
(`MemFacts.bytesAt_bound`, `MemFacts.regionIn_bound` in `Full/Region`): `fsym_entail` adds it to
the state's facts, e.g. for the region view of a global's bytes.
-/

namespace Zig
namespace Witness

open Full FAssn

/-- **An update keeps admissibility**: it replaces the resources and keeps the memory. -/
theorem FAdmit.eupd {P P' : FAssn} (h : FAdmit P) (hu : EUpd P P') : FAdmit P' := by
  obtain ⟨m, r, rF, hh, hp, hs, -⟩ := h
  obtain ⟨r', hh', hp'⟩ := hu m r rF hh hp hs
  exact ⟨m, r', rF, hh', hp', hs, trivial⟩

/-- **A part of an admissible input is admissible**: the other part joins the frame. -/
theorem FAdmit.frame {P R : FAssn} (h : FAdmit (P ⋆ R)) : FAdmit P := by
  obtain ⟨m, r, rF, hh, ⟨r₁, r₂, hd, rfl, h1, -⟩, hs, -⟩ := h
  exact ⟨m, r₁, _, Holds.split hd hh, h1, hs, trivial⟩

/-- An existential on the right of `⋆` scopes over both parts (`sep_ex_eq`, mirrored): with it
`simp` moves the existentials of a start resource (the globals' addresses) outside. -/
theorem _root_.Zig.Full.sep_ex_eq_right {γ : Type} (P : FAssn) (Q : γ → FAssn) :
    (P ⋆ FAssn.ex Q) = FAssn.ex fun x => P ⋆ Q x := by
  rw [Full.sep_comm_eq, sep_ex_eq]; congr; funext x; exact Full.sep_comm_eq _ _

/-- An admissible existential has an admissible instance. -/
theorem FAdmit.ex {γ : Type} {P : γ → FAssn} (h : FAdmit (FAssn.ex P)) : ∃ x, FAdmit (P x) := by
  obtain ⟨m, r, rF, hh, ⟨x, hp⟩, hs, -⟩ := h
  exact ⟨x, m, r, rF, hh, hp, hs, trivial⟩

/-! ## Claims at program start -/

/-- **A claim on a block that no one claims can be added** (`GOk.addCl`, the step of
`FTriple.mintClaimOpt` without the program). -/
theorem _root_.Zig.Full.Holds.addClaim {m : Mem} {r rF : Res} {b : BlockId} {lo hi : Nat}
    (hh : Holds m r rF) (hr : ∀ x, r.gh.cl b x = ECell.unit) (hF : ∀ x, rF.gh.cl b x = ECell.unit)
    (hb : b < m.blocks.size) :
    Holds m ⟨r.heap ∪ FHeap.empty, r.know.union Know.none,
      r.gh.add (Ghost.atCl b (ECell.onRange lo hi (ECell.shareT none Frac.one 0)))⟩ rF :=
  ⟨by rw [FHeap.union_empty]; exact hh.disj, by rw [FHeap.union_empty]; exact hh.heap,
    by rw [Know.union_none]; exact hh.know, hh.knowF,
    GOk.addCl hh.ghost (fun y => by rw [hr y, hF y, ECell.add_unit]) hb
      (fun y ls hu => onRange_share_ok lo hi y ls hu) (fun y γ e k => onRange_share_tags lo hi y γ e k)⟩

/-- The claim on every byte of every global. -/
def gclaims (gs : List (Array Byte × Nat × BlockKind)) : FAssn :=
  sepN gs.length fun j => match gs[j]? with
    | some (bs, _, _) => bclaim j 0 bs.size
    | none => emp

theorem noCl_known (b : BlockId) (A : Nat) : NoCl (known b A) := by
  rintro _ ⟨-, -, hg⟩ b' x; rw [hg]; rfl

theorem noCl_sepN {n : Nat} {f : Nat → FAssn} (h : ∀ j, j < n → NoCl (f j)) : NoCl (sepN n f) := by
  induction n with
  | zero => exact noCl_emp
  | succ n ih => exact noCl_sep (h n (by omega)) (ih fun j hj => h j (by omega))

/-- The globals at program start hold no claim. -/
theorem noCl_globals (gs : List (Array Byte × Nat × BlockKind)) : NoCl (globals gs) := by
  refine noCl_sepN fun j _ => ?_
  split
  · refine noCl_ex fun _ => noCl_sep (noCl_lift _) (noCl_sep (noCl_up _) (noCl_sep (noCl_known _ _) ?_))
    unfold gext; split
    · exact noCl_bauth _ _ _ _
    · exact noCl_emp
  · exact noCl_emp

/-- **The globals at program start, with the claim on every global's bytes, are admissible**
(`FAdmit.init` with `gclaims`), under every placement. -/
theorem FAdmit.init_claims (σ : Placement) (gs : List (Array Byte × Nat × BlockKind))
    (h : Mem.GlobalsFit gs) (hK : ∀ g ∈ gs, g.2.2.mappedLo = 0) :
    FAdmit (globals gs ⋆ gclaims gs) := by
  let f : Nat → FAssn := fun j => match gs[j]? with
    | some (bs, _, _) => bclaim j 0 bs.size
    | none => emp
  -- the claims of the globals below `n`, none above
  have key : ∀ n, n ≤ gs.length → ∃ r, Holds (Mem.ofGlobals σ gs) r ⟨FHeap.empty, Know.none, Ghost.unit⟩ ∧
      (globals gs ⋆ sepN n f) r ∧ ∀ b x, n ≤ b → r.gh.cl b x = ECell.unit := by
    intro n hn
    induction n with
    | zero =>
      obtain ⟨hh, hg⟩ := initRes_holds σ gs hK
      refine ⟨_, ?_, ⟨_, ⟨FHeap.empty, Know.none, Ghost.unit⟩, FHeap.disjoint_empty _, rfl, hg,
        rfl, rfl, rfl⟩, fun b x _ => ?_⟩
      · simpa [FHeap.union_empty, Know.union_none, Ghost.add_unit] using hh
      · simp only [Ghost.add_cl, noCl_globals gs _ hg b x]; exact ECell.unit_add _
    | succ n ih =>
      obtain ⟨r, hh, hp, hz⟩ := ih (by omega)
      have hb : n < (Mem.ofGlobals σ gs).blocks.size := by rw [Mem.ofGlobals_size]; omega
      have hgn : gs[n]? = some gs[n] := List.getElem?_eq_getElem (by omega)
      refine ⟨_, Holds.addClaim (lo := 0) (hi := (gs[n]'(by omega)).1.size) hh (hz n · (Nat.le_refl n))
        (fun _ => rfl) hb, ?_, fun b x hbn => ?_⟩
      · have hc : f n ⟨FHeap.empty, Know.none,
            Ghost.atCl n (ECell.onRange 0 (gs[n]'(by omega)).1.size (ECell.shareT none Frac.one 0))⟩ := by
          simp only [f, hgn]; exact ⟨rfl, rfl, rfl⟩
        have hj : ((globals gs ⋆ sepN n f) ⋆ f n) _ :=
          ⟨r, _, FHeap.disjoint_empty _, rfl, hp, hc⟩
        show (globals gs ⋆ (f n ⋆ sepN n f)) _
        exact ac_cast hj (by ac_rfl)
      · simp only [Ghost.add_cl, hz b x (by omega), Ghost.atCl, show b ≠ n by omega, ↓reduceIte,
          ECell.add_unit]
  obtain ⟨r, hh, hp, -⟩ := key gs.length (Nat.le_refl _)
  exact ⟨_, r, _, hh, hp, Mem.init_fseq σ gs h, trivial⟩

end Witness
end Zig
