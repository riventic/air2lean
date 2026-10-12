import ZigLean.Sep.Full.AllocSpec

/-!
# Byte-range claims (`docs/sep-full-state.md` §Byte-range claims)

An extent share (`bshare`) says that a block is live and long enough; it says nothing about who
else may use which bytes. A **claim** `bclaim b lo hi t` is exclusive: no other resource holds a
live claim on a byte of `[lo, hi)` of block `b` in the same world `t` of the tag tree. Allocators
that hand out parts of one block (a fixed buffer, an arena's nodes) give each grant the claim on
its bytes, so two outstanding grants are disjoint even when neither side owns the bytes any more
(decision O1, `docs/alloc-arena.md`).

**Model.** Each byte `x` of each block `b` has a claim cell `Ghost.cl b x : ECell`, the same kind
of cell as a block's extent claims, used at bound `0`: a claim on `x` tagged `t` is the whole
fraction `1` of the cell in world `t` (`ECell.shareT t 1 0`), a receipt is `ECell.rcpt γ e 1 0`.
Validity (`Ghost.CValid`) is the extent cells' (`ECell.Valid`, `ECell.TagOk`), so

* two claims on one byte in one active world exceed the world's budget (`bclaim_disjoint`);
* tagged claims are lent, returned and revoked exactly like tagged shares (`EUpd.lendC`,
  `EUpd.returnC`, `EUpd.revokeC`: the per-byte steps `ECell.stepE_lendT`, … of
  `EUpd.lendT`, `EUpd.returnT`, `EUpd.revoke`);
* a range claim is the union of its bytes' claims: split and join are equalities
  (`bclaim_split`), not updates.

**Where claims come from.** A claim is born with its block: `GOk` requires that no resource
claims a byte of a block the memory has not created (`ClFresh`), so the creator of a new block
may claim any range of it (`FTriple.mintClaim`). There is no other source: a claim cannot be
minted from `bext` later, because the extent rules (`EUpd.unlend`) re-complete `bext` without
looking at claims (`docs/sep-full-state.md` §Byte-range claims, "why claims are born with the
block"). Claims on bytes beyond a block's size or of a freed block are harmless: block ids are
never reused and in-place growth mints nothing.
-/

namespace Zig
namespace Full

open FAssn

/-! ## Claim cells -/

namespace ECell

/-- The cell `c` on the bytes `[lo, hi)` and nothing elsewhere. -/
def onRange (lo hi : Nat) (c : ECell) : Nat → ECell := fun x => if lo ≤ x ∧ x < hi then c else ECell.unit

theorem onRange_split {lo m hi : Nat} (h1 : lo ≤ m) (h2 : m ≤ hi) (c : ECell) (x : Nat) :
    (onRange lo m c x).add (onRange m hi c x) = onRange lo hi c x := by
  simp only [onRange]
  by_cases h3 : lo ≤ x ∧ x < m
  · rw [if_pos h3, if_neg (by omega), if_pos (by omega), ECell.add_unit]
  · by_cases h4 : m ≤ x ∧ x < hi
    · rw [if_neg h3, if_pos h4, if_pos (by omega), ECell.unit_add]
    · rw [if_neg h3, if_neg h4, if_neg (by omega), ECell.add_unit]

/-- A step that changes nothing. -/
theorem StepE.refl (ls : LStat) (c : ECell) : StepE ls c c :=
  ⟨rfl, fun _ n N E => ⟨n, N, E, id⟩, fun j h => .inl ⟨j, Nat.le_refl _, h⟩, id, fun _ _ _ h => h⟩

/-- A step keeps every frame that `c` composed with validly (`StepE.ok` without the memory). -/
theorem StepE.okV {ls : LStat} {c c' d : ECell} (hst : StepE ls c c') (hv : (c.add d).Valid)
    (hto : (c.add d).TagOk ls) : (c'.add d).Valid ∧ (c'.add d).TagOk ls := by
  obtain ⟨hauth, hw, -, hfut, -⟩ := hst
  obtain ⟨h1, h2, -⟩ := hv
  have ea : (c'.add d).auth = (c.add d).auth := by simp only [add, hauth]
  have hb : ∀ n N E, (c'.add d).Bal ls n N E := fun n N E => by
    obtain ⟨n', N', E', h⟩ := hw d n N E
    exact h (hto.1 n' N' E')
  refine ⟨⟨fun x => by rw [ea]; exact h1 x, fun x y hx hy => h2 x y (by rw [← ea]; exact hx)
    (by rw [← ea]; exact hy), fun n => ?_⟩, ⟨hb, (hfut hto.2.of_add).add ?_⟩⟩
  · obtain ⟨β, h, -⟩ := hb n 0 0
    simp only [mass, gsum, tg_none] at h
    rw [total_eq]; grind
  · exact (by rw [add_comm] at hto; exact hto.2.of_add)

/-- **An active world holds at most the whole** below every bound: by induction on the tag's
activity, a child's budget lies inside its parent's fraction. -/
theorem mass_act_le {ls : LStat} {c : ECell} (n : Nat) :
    ∀ t, Act ls t → ∃ N₀ E₀, ∀ N E β, N₀ ≤ N → E₀ ≤ E → c.BalAt ls β n N E →
      c.mass ls β t n N E ≤ 1 := by
  intro t ht
  induction ht with
  | root => exact ⟨0, 0, fun N E β _ _ hb => hb.1⟩
  | @tag γ e p hls hp ih =>
    obtain ⟨N₀, E₀, ih⟩ := ih
    refine ⟨Max.max N₀ (γ + 1), Max.max E₀ (e + 1), fun N E β hN hE hb => ?_⟩
    have h1 := hb.2 γ e (by omega) (by omega) (.tag hls hp)
    have h2 := cwt_ge_β (β := β) (R := c.rc γ e) (n := n) hls
    have h3 := cwt_le_mass ls c β p (γ := γ) (e := e) n (N := N) (E := E) (by omega) (by omega)
    have h4 := ih N E β (by omega) (by omega) hb
    grind

/-- The fraction of an active world below any bound is at most the whole. -/
theorem ftot_act_le {ls : LStat} {c : ECell} (hc : c.TagOk ls) {t : STag} (ht : Act ls t) (n : Nat) :
    ftot (c.tg t) n ≤ 1 := by
  obtain ⟨N₀, E₀, h⟩ := mass_act_le (c := c) n t ht
  obtain ⟨β, hb⟩ := hc.1 n N₀ E₀
  have h1 := h N₀ E₀ β (Nat.le_refl _) (Nat.le_refl _) hb
  have := gsum_nonneg (fun γ e => cwt_nonneg ls t β γ e (c.rc γ e) n) N₀ E₀
  simp only [mass] at h1; grind

/-- The whole fraction of the root world at bound `0` composes with nothing live. -/
theorem share_one_ok (ls : LStat) (hu : ls.Uniq) : (share Frac.one 0).Valid ∧ (share Frac.one 0).TagOk ls := by
  have h := (dormant_unit ls).auth1_ok (S := 0) (K := .heap)
  rw [add_unit] at h
  have hle : (share Frac.one 0).Le (auth1 0 .heap Frac.one) := by
    refine ⟨fun x => by simp [share], fun k => ?_, fun _ _ _ => by simp [share, auth1],
      fun _ _ _ => by simp [share, auth1]⟩
    simp only [share, auth1]; split <;> simp [Frac.zero]
  refine ⟨⟨fun _ => by simp [share], fun _ _ h => by simp [share] at h, fun n => ?_⟩,
    TagOk.of_le (LStat.Sub.refl _) hu hle h.2⟩
  rw [total_share]; split
  · exact Rat.le_refl
  · decide

end ECell

/-! ## Assertions -/

/-- The ghost state with the claim cells `C` on block `b` and nothing else. -/
def Ghost.atCl (b : BlockId) (C : Nat → ECell) : Ghost :=
  ⟨fun _ => GCell.unit, fun _ => ECell.unit, fun b' x => if b' = b then C x else ECell.unit⟩

theorem Ghost.atCl_add (b : BlockId) (C C' : Nat → ECell) :
    (Ghost.atCl b C).add (Ghost.atCl b C') = Ghost.atCl b fun x => (C x).add (C' x) := by
  ext1
  · funext γ; simp [Ghost.add, Ghost.atCl]
  · funext x; simp [Ghost.add, Ghost.atCl]
  · funext x y; simp only [Ghost.add, Ghost.atCl]; split <;> simp

/-- **An exclusive claim** on the bytes `[lo, hi)` of block `b` in world `t` (the root for
`t = none`, a tag's world for `t = some (γ, e)`). Owns no bytes, no knowledge. -/
def bclaim (b : BlockId) (lo hi : Nat) (t : STag := none) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧
    r.gh = Ghost.atCl b (ECell.onRange lo hi (ECell.shareT t Frac.one 0))

/-- **A receipt** for the claim on `[lo, hi)` of block `b` lent as a claim tagged `(γ, e)`
(`EUpd.lendC`): it lies in the world of the ledger's parent and holds the bytes there. -/
def bcrcpt (b : BlockId) (lo hi γ e : Nat) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧
    r.gh = Ghost.atCl b (ECell.onRange lo hi (ECell.rcpt γ e Frac.one 0))

/-- A claim on the part of `p`'s block from `lo` to `hi`. -/
def pclaim (p : Ptr) (lo hi : Nat) (t : STag := none) : FAssn :=
  FAssn.ex fun b => ⟪p.block = some b⟫ ⋆ bclaim b lo hi t

theorem ghostOnly_sep {C C' : Nat → ECell} {b : BlockId} {r : Res}
    (h : ((fun r => r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.atCl b C) ⋆
      (fun r => r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.atCl b C')) r) :
    r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.atCl b fun x => (C x).add (C' x) := by
  obtain ⟨r₁, r₂, -, rfl, ⟨h1, k1, g1⟩, ⟨h2, k2, g2⟩⟩ := h
  exact ⟨by simp [h1, h2], by simp [k1, k2, Know.union_none], by simp only [g1, g2, Ghost.atCl_add]⟩

theorem ghostOnly_sep_intro {C C' : Nat → ECell} {b : BlockId} :
    ((fun r => r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.atCl b C) ⋆
      (fun r => r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.atCl b C'))
      ⟨FHeap.empty, Know.none, Ghost.atCl b fun x => (C x).add (C' x)⟩ :=
  ⟨⟨FHeap.empty, Know.none, Ghost.atCl b C⟩, ⟨FHeap.empty, Know.none, Ghost.atCl b C'⟩,
    FHeap.disjoint_empty _, by simp [Know.union_none, Ghost.atCl_add], ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- **Split and join** are one law: a claim is the union of its bytes' claims. -/
theorem bclaim_split {b : BlockId} {lo m hi : Nat} {t : STag} (h1 : lo ≤ m) (h2 : m ≤ hi) :
    (bclaim b lo m t ⋆ bclaim b m hi t) = bclaim b lo hi t := by
  funext r
  apply propext
  have e : (fun x => (ECell.onRange lo m (ECell.shareT t Frac.one 0) x).add
      (ECell.onRange m hi (ECell.shareT t Frac.one 0) x)) = ECell.onRange lo hi (ECell.shareT t Frac.one 0) :=
    funext (ECell.onRange_split h1 h2 _)
  constructor
  · intro h; have := ghostOnly_sep h; rw [e] at this; exact this
  · rintro ⟨h0, k0, g0⟩
    rw [res_eta r, h0, k0, g0, ← e]
    exact ghostOnly_sep_intro

/-- Receipts split and join like claims. -/
theorem bcrcpt_split {b : BlockId} {lo m hi γ e : Nat} (h1 : lo ≤ m) (h2 : m ≤ hi) :
    (bcrcpt b lo m γ e ⋆ bcrcpt b m hi γ e) = bcrcpt b lo hi γ e := by
  funext r
  apply propext
  have e : (fun x => (ECell.onRange lo m (ECell.rcpt γ e Frac.one 0) x).add
      (ECell.onRange m hi (ECell.rcpt γ e Frac.one 0) x)) = ECell.onRange lo hi (ECell.rcpt γ e Frac.one 0) :=
    funext (ECell.onRange_split h1 h2 _)
  constructor
  · intro h; have := ghostOnly_sep h; rw [e] at this; exact this
  · rintro ⟨h0, k0, g0⟩
    rw [res_eta r, h0, k0, g0, ← e]
    exact ghostOnly_sep_intro

/-! ## Exclusivity -/

/-- **Two claims of one active world are disjoint**: a byte claimed twice would hold twice the
whole fraction in that world (`ECell.ftot_act_le`). -/
theorem Holds.bclaim_disjoint {m : Mem} {r rF : Res} {R : FAssn} {b : BlockId} {lo₁ hi₁ lo₂ hi₂ : Nat}
    {t : STag} (hh : Holds m r rF) (h : (bclaim b lo₁ hi₁ t ⋆ (bclaim b lo₂ hi₂ t ⋆ R)) r)
    (ha : Act r.gh.ls t := by exact Act.root) : hi₁ ≤ lo₂ ∨ hi₂ ≤ lo₁ ∨ hi₁ ≤ lo₁ ∨ hi₂ ≤ lo₂ := by
  refine Classical.byContradiction fun hn => ?_
  obtain ⟨r₁, r₂₃, -, rfl, ⟨-, -, g1⟩, r₂, r₃, -, rfl, ⟨-, -, g2⟩, -⟩ := h
  let x := Max.max lo₁ lo₂
  have hv := (hh.ghost.1.1.2.2.1 b x).2
  have hact : Act ((r₁.gh.add (r₂.gh.add r₃.gh)).add rF.gh).ls t := ha.mono (Ghost.ls_add _ _)
  have h1 := ECell.ftot_act_le hv hact 1
  simp only [ftot, Ghost.add_cl, g1, g2, Ghost.atCl, if_true, ECell.onRange] at h1
  rw [if_pos ⟨Nat.le_max_left _ _, by omega⟩, if_pos ⟨Nat.le_max_right _ _, by omega⟩] at h1
  simp only [ECell.tg_add_val, ECell.tg_shareT, true_and, if_true] at h1
  have := ((r₃.gh.cl b x).tg t 0).nonneg; have := ((rF.gh.cl b x).tg t 0).nonneg
  simp only [Frac.one] at h1; grind

/-- Two claims of one active world on `p`'s block are disjoint. -/
theorem Holds.pclaim_disjoint {m : Mem} {r rF : Res} {R : FAssn} {p : Ptr} {lo₁ hi₁ lo₂ hi₂ : Nat}
    {t : STag} (hh : Holds m r rF) (h : (pclaim p lo₁ hi₁ t ⋆ (pclaim p lo₂ hi₂ t ⋆ R)) r)
    (ha : Act r.gh.ls t := by exact Act.root) : hi₁ ≤ lo₂ ∨ hi₂ ≤ lo₁ ∨ hi₁ ≤ lo₁ ∨ hi₂ ≤ lo₂ := by
  obtain ⟨r₁, r₂₃, hd, rfl, ⟨b, hb⟩, hr⟩ := h
  obtain ⟨hpb, hb⟩ := sep_lift.mp hb
  obtain ⟨r₂, r₃, hd', rfl, ⟨b', hb'⟩, hr3⟩ := hr
  obtain ⟨hpb', hb'⟩ := sep_lift.mp hb'
  rw [hpb] at hpb'; cases hpb'
  exact hh.bclaim_disjoint (R := R) ⟨r₁, _, hd, rfl, hb, r₂, r₃, hd', rfl, hb', hr3⟩ ha

end Full
end Zig
