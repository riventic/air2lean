import ZigLean.Sep.Full.Logic
import ZigLean.Sep.Full.Extent

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
  ⟨fun _ => GCell.unit, fun _ => ECell.unit, fun b' x => if b' = b then C x else ECell.unit, ACell.unit⟩

@[simp] theorem Ghost.atCl_ac (b : BlockId) (C : Nat → ECell) : (Ghost.atCl b C).ac = ACell.unit := rfl

theorem Ghost.atCl_add (b : BlockId) (C C' : Nat → ECell) :
    (Ghost.atCl b C).add (Ghost.atCl b C') = Ghost.atCl b fun x => (C x).add (C' x) := by
  ext1
  · funext γ; simp [Ghost.add, Ghost.atCl]
  · funext x; simp [Ghost.add, Ghost.atCl]
  · funext x y; simp only [Ghost.add, Ghost.atCl]; split <;> simp
  · simp

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

/-! ## Lending, returning and revoking claims -/

namespace ECell

theorem onRange_add (lo hi : Nat) (c c' : ECell) (x : Nat) :
    (onRange lo hi c x).add (onRange lo hi c' x) = onRange lo hi (c.add c') x := by
  simp only [onRange]; split <;> simp

/-- A cell step on every byte of a range. -/
theorem StepE.onRange {ls : LStat} {c c' : ECell} (h : StepE ls c c') (lo hi x : Nat) :
    StepE ls (onRange lo hi c x) (onRange lo hi c' x) := by
  simp only [ECell.onRange]; split
  · exact h
  · exact StepE.refl ls _

/-- An empty range stays empty: if `c` is not the unit, `onRange lo hi c` is all unit only for
`hi ≤ lo`. -/
theorem onRange_unit {c c' : ECell} (hc : c ≠ unit) {lo hi : Nat} (h : ∀ x, onRange lo hi c x = unit) :
    ∀ x, onRange lo hi c' x = unit := fun x => by
  by_cases hx : lo ≤ x ∧ x < hi
  · have := h x; simp only [onRange, if_pos hx] at this; exact absurd this hc
  · simp only [onRange, if_neg hx]

theorem shareT_ne_unit (t : STag) {q : Frac} (hq : 0 < q.val) (k : Nat) : shareT t q k ≠ unit := fun h => by
  have h1 := tg_shareT t q k t k
  rw [h] at h1
  rcases t with _ | ⟨γ, e⟩ <;> simp [unit, tg, Frac.zero] at h1 <;> grind

theorem rcpt_ne_unit (γ e : Nat) {q : Frac} (hq : 0 < q.val) (k : Nat) (d : ECell) :
    d.add (rcpt γ e q k) ≠ unit := fun h => by
  have h1 := congrArg (fun c : ECell => (c.rc γ e k).val) h
  simp only [rc_add_val, rcpt_rc_val, and_self, if_true] at h1
  have := (d.rc γ e k).nonneg
  simp [unit, Frac.zero] at h1; grind

end ECell

theorem Ghost.atCl_ls (b : BlockId) (C : Nat → ECell) (g : Ghost) : (g.add (Ghost.atCl b C)).ls = g.ls := by
  funext γ e p; simp [Ghost.ls, Ghost.add, Ghost.atCl]

/-- Replacing the claim cells `C` of one block by `C'`, next to a ledger part `L` without claims,
keeps a composition when every byte's change is a cell step (`ECell.StepE`) under every ledger
status that contains `L`'s, and a block without claims stays without claims. -/
theorem GOk.cl1 {m : Mem} {L : Ghost} (hL : ∀ x y, L.cl x y = ECell.unit) {b : BlockId}
    {C C' : Nat → ECell} {gF : Ghost} (hok : GOk m (L.add (Ghost.atCl b C)) gF)
    (h : ∀ ls : LStat, L.ls.Sub ls → ls.Uniq → ∀ x, ECell.StepE ls (C x) (C' x))
    (hz : (∀ x, C x = ECell.unit) → ∀ x, C' x = ECell.unit) :
    GOk m (L.add (Ghost.atCl b C')) gF := by
  obtain ⟨⟨⟨hv, hx, ⟨hcv, NC, hNC⟩, hcr⟩, N, hN⟩, ht, hcf, hma⟩ := hok
  have hV : Ghost.Valid ((L.add (Ghost.atCl b C)).add gF) := ⟨hv, hx, ⟨hcv, NC, hNC⟩, hcr⟩
  have eled : ((L.add (Ghost.atCl b C')).add gF).led = ((L.add (Ghost.atCl b C)).add gF).led := rfl
  have ex : ((L.add (Ghost.atCl b C')).add gF).extent = ((L.add (Ghost.atCl b C)).add gF).extent := rfl
  have els : ((L.add (Ghost.atCl b C')).add gF).ls = ((L.add (Ghost.atCl b C)).add gF).ls := rfl
  have ecl : ∀ D x y, ((L.add (Ghost.atCl b D)).add gF).cl x y =
      if x = b then (D y).add (gF.cl b y) else gF.cl x y := fun D x y => by
    by_cases hb : x = b
    · subst hb; simp [Ghost.atCl, hL]
    · simp [Ghost.atCl, hL, hb]
  have hst := h ((L.add (Ghost.atCl b C)).add gF).ls
    (fun γ e p h => Ghost.ls_add _ _ _ _ _ (Ghost.ls_add _ _ _ _ _ h)) hV.uniq
  refine ⟨⟨⟨hv, by rw [ex, els]; exact hx, ⟨fun x y => ?_, Max.max NC N, fun γ hγ x y e k => ?_⟩,
    by simpa using hcr⟩, N, fun γ hγ => hN γ hγ⟩, ExtTrue.congr ex els ht, fun x hx y => ?_,
    by simpa using hma⟩
  · rw [ecl, els]
    have h0 := hcv x y
    rw [ecl] at h0
    split
    · rename_i hb; subst hb; rw [if_pos rfl] at h0; exact (hst y).okV h0.1 h0.2
    · rename_i hb; rw [if_neg hb] at h0; exact h0
  · have h0 := hNC γ (by omega) x y
    rw [ecl] at h0 ⊢
    split
    · rename_i hb; subst hb; rw [if_pos rfl] at h0
      have hz' := fun e k => ECell.add_tags_zero (a := C y) (b := gF.cl x y)
        (by have := hNC γ (by omega) x y e k; rw [ecl, if_pos rfl] at this; exact this)
      have hnep : ∀ e p, ¬ ((L.add (Ghost.atCl x C)).add gF).ls γ e p := fun e p ⟨M, hM⟩ => by
        rw [(hN γ (by omega)).1] at hM; simp [GCell.unit] at hM
      have hnpar : ∀ γ' e' e, ¬ ((L.add (Ghost.atCl x C)).add gF).ls γ' e' (some (γ, e)) :=
        fun γ' e' e ⟨M, hM⟩ => by have := (hN γ (by omega)).2.2 γ' e' M e; omega
      have := (hst y).2.2.2.2 γ hnep hnpar (fun e k => ⟨(hz' e k).1, (hz' e k).2.1⟩) e k
      simp only [ECell.add, Frac.add_val, this.1, this.2, (hz' e k).2.2.1, (hz' e k).2.2.2]; grind
    · rename_i hb; rw [if_neg hb] at h0; exact h0 e k
  · have h0 := hcf x hx
    rw [ecl]; split
    · rename_i hb; subst hb
      have hC : ∀ y, C y = ECell.unit := fun y => by
        have := h0 y; rw [ecl, if_pos rfl] at this; exact ECell.eq_unit_of_add this
      have hF : gF.cl x y = ECell.unit := by
        have := h0 y; rw [ecl, if_pos rfl, ECell.add_comm] at this; exact ECell.eq_unit_of_add this
      rw [hz hC y, hF, ECell.add_unit]
    · rename_i hb; have := h0 y; rw [ecl, if_neg hb] at this; exact this

namespace EUpd

variable {P P' : FAssn}

/-- **A local update of one block's claim cells** next to a ledger part `L` (`GOk.cl1`). -/
theorem cl1L {L : Ghost} (hL : ∀ x y, L.cl x y = ECell.unit) {b : BlockId} {C C' : Nat → ECell}
    (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, L.add (Ghost.atCl b C)⟩ ∧
      P' ⟨FHeap.empty, Know.none, L.add (Ghost.atCl b C')⟩ ∧
      (∀ ls : LStat, L.ls.Sub ls → ls.Uniq → ∀ x, ECell.StepE ls (C x) (C' x)) ∧
      ((∀ x, C x = ECell.unit) → ∀ x, C' x = ECell.unit)) : EUpd P P' := by
  intro m r rF hh hr _
  obtain ⟨e, hp', hst, hz⟩ := hp r hr
  subst e
  exact ⟨⟨FHeap.empty, Know.none, L.add (Ghost.atCl b C')⟩,
    ⟨hh.disj, hh.heap, hh.know, hh.knowF, GOk.cl1 hL hh.ghost hst hz⟩, hp'⟩

end EUpd

section ClaimRules

variable {b : BlockId} {lo hi γ e : Nat} {M : GMap} {p : STag}

theorem bclaim_eq {t : STag} {r : Res} (h : bclaim b lo hi t r) :
    r = ⟨FHeap.empty, Know.none, Ghost.atCl b (ECell.onRange lo hi (ECell.shareT t Frac.one 0))⟩ := by
  obtain ⟨h1, h2, h3⟩ := h; rw [res_eta r, h1, h2, h3]

theorem bcrcpt_eq {r : Res} (h : bcrcpt b lo hi γ e r) :
    r = ⟨FHeap.empty, Know.none, Ghost.atCl b (ECell.onRange lo hi (ECell.rcpt γ e Frac.one 0))⟩ := by
  obtain ⟨h1, h2, h3⟩ := h; rw [res_eta r, h1, h2, h3]

/-- A tagged claim next to its receipt, as one claim cell per byte. -/
theorem bclaim_bcrcpt_eq {r : Res} (h : (bclaim b lo hi (some (γ, e)) ⋆ bcrcpt b lo hi γ e) r) :
    r = ⟨FHeap.empty, Know.none, Ghost.atCl b (ECell.onRange lo hi
      ((ECell.tshare γ e Frac.one 0).add (ECell.rcpt γ e Frac.one 0)))⟩ := by
  obtain ⟨h1, h2, h3⟩ := ghostOnly_sep h
  rw [res_eta r, h1, h2, h3]
  congr 2; funext x; exact ECell.onRange_add lo hi _ _ x

theorem bclaim_bcrcpt_intro :
    (bclaim b lo hi (some (γ, e)) ⋆ bcrcpt b lo hi γ e) ⟨FHeap.empty, Know.none, Ghost.atCl b
      (ECell.onRange lo hi ((ECell.tshare γ e Frac.one 0).add (ECell.rcpt γ e Frac.one 0)))⟩ := by
  have := ghostOnly_sep_intro (b := b) (C := ECell.onRange lo hi (ECell.shareT (some (γ, e)) Frac.one 0))
    (C' := ECell.onRange lo hi (ECell.rcpt γ e Frac.one 0))
  have e : (fun x => (ECell.onRange lo hi (ECell.shareT (some (γ, e)) Frac.one 0) x).add
      (ECell.onRange lo hi (ECell.rcpt γ e Frac.one 0) x)) =
      ECell.onRange lo hi ((ECell.tshare γ e Frac.one 0).add (ECell.rcpt γ e Frac.one 0)) :=
    funext (ECell.onRange_add lo hi _ _)
  rw [e] at this; exact this

/-- `gauthP γ e M p ⋆ P`, where `P` holds the claim cells `C` of block `b` only, as one resource. -/
theorem gauth_cl_eq {P : FAssn} {C : Nat → ECell}
    (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, Ghost.atCl b C⟩) {r : Res} (h : (gauthP γ e M p ⋆ P) r) :
    r = ⟨FHeap.empty, Know.none, (Ghost.at γ (GCell.auth1 e M p)).add (Ghost.atCl b C)⟩ := by
  obtain ⟨r₁, r₂, -, rfl, ⟨h1, k1, g1⟩, h2⟩ := h
  rw [hp _ h2, h1, k1, g1]; simp [FHeap.union_empty, Know.union_none]

theorem gauth_cl_intro {P : FAssn} {C : Nat → ECell} (hp : P ⟨FHeap.empty, Know.none, Ghost.atCl b C⟩) :
    (gauthP γ e M p ⋆ P) ⟨FHeap.empty, Know.none, (Ghost.at γ (GCell.auth1 e M p)).add (Ghost.atCl b C)⟩ :=
  ⟨⟨FHeap.empty, Know.none, Ghost.at γ (GCell.auth1 e M p)⟩, ⟨FHeap.empty, Know.none, Ghost.atCl b C⟩,
    FHeap.disjoint_empty _, by simp [FHeap.union_empty, Know.union_none], ⟨rfl, rfl, rfl⟩, hp⟩

theorem frac_one_pos : 0 < Frac.one.val := by decide

/-- **Lend a claim** of the world `p` as a claim tagged `(γ, e)` (ledger `γ` at epoch `e` with
parent `p`): the lender keeps a receipt (`EUpd.lendT` on each byte). -/
theorem EUpd.lendC :
    EUpd (gauthP γ e M p ⋆ bclaim b lo hi p)
      (gauthP γ e M p ⋆ (bclaim b lo hi (some (γ, e)) ⋆ bcrcpt b lo hi γ e)) :=
  EUpd.cl1L (L := Ghost.at γ (GCell.auth1 e M p)) (fun _ _ => rfl) fun r h =>
    ⟨gauth_cl_eq (fun _ h => bclaim_eq h) h, gauth_cl_intro bclaim_bcrcpt_intro,
      fun ls hL hu x => (ECell.stepE_lendT (Nat.le_refl 0) frac_one_pos (hL _ _ _ Ghost.at_auth1_ls) hu).onRange lo hi x,
      ECell.onRange_unit (ECell.shareT_ne_unit p frac_one_pos 0)⟩

/-- **Give a tagged claim back** during its epoch: it cancels its receipt, and the world `p`
gets the claim back (`EUpd.returnT` on each byte). -/
theorem EUpd.returnC :
    EUpd (gauthP γ e M p ⋆ (bclaim b lo hi (some (γ, e)) ⋆ bcrcpt b lo hi γ e))
      (gauthP γ e M p ⋆ bclaim b lo hi p) :=
  EUpd.cl1L (L := Ghost.at γ (GCell.auth1 e M p)) (fun _ _ => rfl) fun r h =>
    ⟨gauth_cl_eq (fun _ h => bclaim_bcrcpt_eq h) h, gauth_cl_intro ⟨rfl, rfl, rfl⟩,
      fun ls hL hu x => (ECell.stepE_returnT (Nat.le_refl 0) frac_one_pos (hL _ _ _ Ghost.at_auth1_ls) hu).onRange lo hi x,
      ECell.onRange_unit (ECell.rcpt_ne_unit γ e frac_one_pos 0 _)⟩

/-- **Revoke a past epoch's claim**: once ledger `γ` is past epoch `e`, a claim receipt turns back
into the claim of the world `p`, whatever the tagged claim's holder kept (`EUpd.revoke` on each
byte). -/
theorem EUpd.revokeC {e' : Nat} (he : e < e') :
    EUpd (gauthP γ e' M p ⋆ bcrcpt b lo hi γ e) (gauthP γ e' M p ⋆ bclaim b lo hi p) :=
  EUpd.cl1L (L := Ghost.at γ (GCell.auth1 e' M p)) (fun _ _ => rfl) fun r h =>
    ⟨gauth_cl_eq (fun _ h => bcrcpt_eq h) h, gauth_cl_intro ⟨rfl, rfl, rfl⟩,
      fun ls hL hu x => (ECell.stepE_revoke he frac_one_pos (hL _ _ _ Ghost.at_auth1_ls) hu).onRange lo hi x,
      ECell.onRange_unit (by simpa using ECell.rcpt_ne_unit γ e frac_one_pos 0 ECell.unit)⟩

end ClaimRules

/-! ## Exclusivity -/

/-- **Two claims of one active world are disjoint**: a byte claimed twice would hold twice the
whole fraction in that world (`ECell.ftot_act_le`). -/
theorem Holds.bclaim_disjoint {m : Mem} {r rF : Res} {R : FAssn} {b : BlockId} {lo₁ hi₁ lo₂ hi₂ : Nat}
    {t : STag} (hh : Holds m r rF) (h : (bclaim b lo₁ hi₁ t ⋆ (bclaim b lo₂ hi₂ t ⋆ R)) r)
    (ha : Act r.gh.ls t := by exact Act.root) : hi₁ ≤ lo₂ ∨ hi₂ ≤ lo₁ ∨ hi₁ ≤ lo₁ ∨ hi₂ ≤ lo₂ := by
  refine Classical.byContradiction fun hn => ?_
  obtain ⟨r₁, r₂₃, -, rfl, ⟨-, -, g1⟩, r₂, r₃, -, rfl, ⟨-, -, g2⟩, -⟩ := h
  let x := Max.max lo₁ lo₂
  have hv := (hh.ghost.1.1.2.2.1.1 b x).2
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

/-! ## Claims are born with their block -/

/-- Untagged claim cells: valid under every ledger status, no tag. -/
theorem onRange_share_ok (lo hi : Nat) (x : Nat) (ls : LStat) (hu : ls.Uniq) :
    (ECell.onRange lo hi (ECell.shareT none Frac.one 0) x).Valid ∧
      (ECell.onRange lo hi (ECell.shareT none Frac.one 0) x).TagOk ls := by
  simp only [ECell.onRange, ECell.shareT_none]
  split
  · exact ECell.share_one_ok ls hu
  · exact ⟨ECell.valid_unit, ECell.tagOk_unit ls⟩

theorem onRange_share_tags (lo hi x γ e k : Nat) :
    ((ECell.onRange lo hi (ECell.shareT none Frac.one 0) x).tsh γ e k).val = 0 ∧
      ((ECell.onRange lo hi (ECell.shareT none Frac.one 0) x).rc γ e k).val = 0 := by
  simp only [ECell.onRange, ECell.shareT_none]
  split <;> exact ⟨rfl, rfl⟩

/-- **Claims on a block no part claims** can be added: the root world of each byte gets the
whole. -/
theorem GOk.addCl {m : Mem} {g gF : Ghost} {b : BlockId} {C : Nat → ECell} (hok : GOk m g gF)
    (hz : ∀ x, (g.cl b x).add (gF.cl b x) = ECell.unit) (hb : b < m.blocks.size)
    (hC : ∀ x (ls : LStat), ls.Uniq → (C x).Valid ∧ (C x).TagOk ls)
    (hCt : ∀ x γ e k, ((C x).tsh γ e k).val = 0 ∧ ((C x).rc γ e k).val = 0) :
    GOk m (g.add (Ghost.atCl b C)) gF := by
  obtain ⟨⟨⟨hv, hx, ⟨hcv, NC, hNC⟩, hcr⟩, N, hN⟩, ht, hcf, hma⟩ := hok
  have hu : (g.add gF).ls.Uniq := Ghost.Valid.uniq (g := g.add gF) ⟨hv, hx, ⟨hcv, NC, hNC⟩, hcr⟩
  have e : (g.add (Ghost.atCl b C)).add gF = (g.add gF).add (Ghost.atCl b C) := by
    rw [Ghost.add_assoc, Ghost.add_comm (Ghost.atCl b C), ← Ghost.add_assoc]
  unfold GOk Ghost.Ok
  rw [e]
  have eled : ((g.add gF).add (Ghost.atCl b C)).led = (g.add gF).led := by
    funext γ; simp [Ghost.add, Ghost.atCl]
  have ex : ((g.add gF).add (Ghost.atCl b C)).extent = (g.add gF).extent := by
    funext x; simp [Ghost.add, Ghost.atCl]
  have els : ((g.add gF).add (Ghost.atCl b C)).ls = (g.add gF).ls := by
    funext γ e p; simp only [Ghost.ls, eled]
  have ecl : ∀ x y, ((g.add gF).add (Ghost.atCl b C)).cl x y =
      if x = b then C y else (g.add gF).cl x y := by
    intro x y
    by_cases h : x = b
    · subst h; simp only [Ghost.add_cl, Ghost.atCl, if_true, hz, ECell.unit_add]
    · simp only [Ghost.add_cl, Ghost.atCl, h, if_false, ECell.add_unit]
  refine ⟨⟨⟨by rw [eled]; exact hv, by rw [ex, els]; exact hx, ⟨fun x y => ?_, NC, fun γ hγ x y e k => ?_⟩,
    by simpa using hcr⟩, N, fun γ hγ => ?_⟩, ExtTrue.congr ex els ht, fun x hx y => ?_,
    by simpa using hma⟩
  · rw [ecl, els]; split
    · exact hC y _ hu
    · exact hcv x y
  · rw [ecl]; split
    · exact hCt y γ e k
    · exact hNC γ hγ x y e k
  · rw [eled, ex]; exact hN γ hγ
  · by_cases h : x = b
    · exact absurd hb (Nat.not_lt.mpr (h ▸ hx))
    · rw [ecl, if_neg h]; exact hcf x hx y

/-- A claim on `[lo, hi)` of block `b` if there is one (`nb = some b`), nothing otherwise. -/
def optClaim : Option BlockId → Nat → Nat → FAssn
  | some b, lo, hi => bclaim b lo hi
  | none, _, _ => emp

/-- **The creator of a block claims its bytes** (any range `[lo v, hi v)`): a program whose run
creates block `b` whenever `nb v = some b` (absent before, present after) yields that block's
untagged claim next to its post, when the post holds no claim on the new block. -/
theorem FTriple.mintClaimOpt {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} (nb : α → Option BlockId)
    (lo hi : α → Nat) (ht : FTriple P c Q)
    (hfresh : ∀ m v m' b, (c.run m).run = some (.ok (v, m')) → nb v = some b →
      m.blocks.size ≤ b ∧ b < m'.blocks.size)
    (hQ : ∀ v b r, nb v = some b → Q v r → ∀ x, r.gh.cl b x = ECell.unit) :
    FTriple P c (fun v => Q v ⋆ optClaim (nb v) (lo v) (hi v)) := by
  intro m r rF hh hp hs
  have h := ht m r rF hh hp hs
  revert h
  cases hrun : (c.run m).run with
  | none => intro; trivial
  | some x =>
    cases x with
    | error e => exact id
    | ok p =>
      obtain ⟨v, m'⟩ := p
      rintro ⟨r', hh', hq, hs'⟩
      cases hnb : nb v with
      | none =>
        refine ⟨r', hh', ?_, hs'⟩
        show (Q v ⋆ optClaim (nb v) (lo v) (hi v)) r'
        rw [hnb]; exact sep_emp.mpr hq
      | some b =>
        obtain ⟨h1, h2⟩ := hfresh m v m' b hrun hnb
        have hz : ∀ y, (r'.gh.cl b y).add (rF.gh.cl b y) = ECell.unit := fun y => by
          rw [hQ v b r' hnb hq y, hh.ghost.2.2.1.frame b h1 y, ECell.add_unit]
        refine ⟨⟨r'.heap ∪ FHeap.empty, r'.know.union Know.none,
            r'.gh.add (Ghost.atCl b (ECell.onRange (lo v) (hi v) (ECell.shareT none Frac.one 0)))⟩,
          ⟨by rw [FHeap.union_empty]; exact hh'.disj, by rw [FHeap.union_empty]; exact hh'.heap,
            by rw [Know.union_none]; exact hh'.know, hh'.knowF,
            GOk.addCl hh'.ghost hz h2 (fun y ls hu => onRange_share_ok (lo v) (hi v) y ls hu)
              (fun y γ e k => onRange_share_tags (lo v) (hi v) y γ e k)⟩, ?_, hs'⟩
        show (Q v ⋆ optClaim (nb v) (lo v) (hi v)) _
        rw [hnb]
        exact ⟨r', ⟨FHeap.empty, Know.none, _⟩, FHeap.disjoint_empty _, rfl, hq, rfl, rfl, rfl⟩

/-- **The creator of a block claims its bytes** (any range `[lo, hi)`): a program whose run
creates block `nb v` (absent before, present after) yields the untagged claim next to its post,
when the post holds no claim on the new block. -/
theorem FTriple.mintClaim {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} (nb : α → BlockId)
    (lo hi : Nat) (ht : FTriple P c Q)
    (hfresh : ∀ m v m', (c.run m).run = some (.ok (v, m')) → m.blocks.size ≤ nb v ∧ nb v < m'.blocks.size)
    (hQ : ∀ v r, Q v r → ∀ x, r.gh.cl (nb v) x = ECell.unit) :
    FTriple P c (fun v => Q v ⋆ bclaim (nb v) lo hi) :=
  FTriple.mintClaimOpt (fun v => some (nb v)) (fun _ => lo) (fun _ => hi) ht
    (fun m v m' b h e => by cases e; exact hfresh m v m' h) (fun v b r e hq => by cases e; exact hQ v r hq)

/-- `FTriple.mintClaimOpt` for a total triple (the precondition is unchanged). -/
theorem FTotalTriple.mintClaimOpt {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}
    (nb : α → Option BlockId) (lo hi : α → Nat) (ht : FTotalTriple P c Q)
    (hfresh : ∀ m v m' b, (c.run m).run = some (.ok (v, m')) → nb v = some b →
      m.blocks.size ≤ b ∧ b < m'.blocks.size)
    (hQ : ∀ v b r, nb v = some b → Q v r → ∀ x, r.gh.cl b x = ECell.unit) :
    FTotalTriple P c (fun v => Q v ⋆ optClaim (nb v) (lo v) (hi v)) :=
  ⟨FTriple.mintClaimOpt nb lo hi ht.1 hfresh hQ, ht.2⟩

/-- An assertion whose resources hold no byte claim (bytes, knowledge, extents, ledgers). -/
def NoCl (Q : FAssn) : Prop := ∀ r, Q r → ∀ b x, r.gh.cl b x = ECell.unit

theorem noCl_sep {P Q : FAssn} (hp : NoCl P) (hq : NoCl Q) : NoCl (P ⋆ Q) := by
  rintro _ ⟨r₁, r₂, -, rfl, h1, h2⟩ b x
  simp only [Ghost.add_cl, hp _ h1 b x, hq _ h2 b x, ECell.add_unit]

theorem noCl_ex {γ : Type} {P : γ → FAssn} (h : ∀ x, NoCl (P x)) : NoCl (FAssn.ex P) := by
  rintro _ ⟨y, hy⟩ b x; exact h y _ hy b x

theorem noCl_lift (φ : Prop) : NoCl ⟪φ⟫ := by
  rintro _ ⟨-, -, -, hg⟩ b x; rw [hg]; rfl

theorem noCl_emp : NoCl emp := by
  rintro _ ⟨-, -, hg⟩ b x; rw [hg]; rfl

theorem noCl_up (P : Assn) : NoCl (up P) := by
  rintro _ ⟨-, -, hg⟩ b x; rw [hg]; rfl

theorem noCl_bauth (b : BlockId) (S : Nat) (K : BlockKind) (q : Frac) : NoCl (bauth b S K q) := by
  rintro _ ⟨-, -, hg⟩ b' x; rw [hg]; rfl

theorem noCl_bshare (b : BlockId) (q : Frac) (k : Nat) (t : STag) : NoCl (bshare b q k t) := by
  rintro _ ⟨-, -, -, hg⟩ b' x; rw [hg]; rfl

/-! ## Claims and receipts of a pointer's block -/

/-- A receipt for the claim on the part of `p`'s block from `lo` to `hi`, lent as tagged
`(γ, e)`. -/
def pcrcpt (p : Ptr) (lo hi γ e : Nat) : FAssn :=
  FAssn.ex fun b => ⟪p.block = some b⟫ ⋆ bcrcpt b lo hi γ e

section PtrClaims

variable {p p' : Ptr} {b : BlockId} {lo m hi γ e : Nat} {t : STag}

theorem pclaim_eq (hb : p.block = some b) : pclaim p lo hi t = bclaim b lo hi t := by
  funext r; apply propext; constructor
  · rintro ⟨b', h⟩; obtain ⟨hb', h⟩ := sep_lift.mp h; rw [hb] at hb'; cases hb'; exact h
  · exact fun h => ⟨b, sep_lift.mpr ⟨hb, h⟩⟩

theorem pcrcpt_eq (hb : p.block = some b) : pcrcpt p lo hi γ e = bcrcpt b lo hi γ e := by
  funext r; apply propext; constructor
  · rintro ⟨b', h⟩; obtain ⟨hb', h⟩ := sep_lift.mp h; rw [hb] at hb'; cases hb'; exact h
  · exact fun h => ⟨b, sep_lift.mpr ⟨hb, h⟩⟩

/-- A claim names its block, not its pointer. -/
theorem pclaim_rebase (h : p.block = p'.block) : pclaim p lo hi t = pclaim p' lo hi t := by
  simp only [pclaim, h]

theorem pcrcpt_rebase (h : p.block = p'.block) : pcrcpt p lo hi γ e = pcrcpt p' lo hi γ e := by
  simp only [pcrcpt, h]

/-- A claim without a block holds nowhere. -/
theorem pclaim_none (hb : p.block = none) {r : Res} : ¬ pclaim p lo hi t r := by
  rintro ⟨b, h⟩; rw [hb] at h; cases (sep_lift.mp h).1

theorem pcrcpt_none (hb : p.block = none) {r : Res} : ¬ pcrcpt p lo hi γ e r := by
  rintro ⟨b, h⟩; rw [hb] at h; cases (sep_lift.mp h).1

/-- **Split and join** of a pointer's claim (`bclaim_split`). -/
theorem pclaim_split (h1 : lo ≤ m) (h2 : m ≤ hi) :
    (pclaim p lo m t ⋆ pclaim p m hi t) = pclaim p lo hi t := by
  cases hb : p.block with
  | some b => rw [pclaim_eq hb, pclaim_eq hb, pclaim_eq hb, bclaim_split h1 h2]
  | none =>
    funext r; apply propext
    exact ⟨fun ⟨_, _, _, _, h, _⟩ => (pclaim_none hb h).elim, fun h => (pclaim_none hb h).elim⟩

theorem pcrcpt_split (h1 : lo ≤ m) (h2 : m ≤ hi) :
    (pcrcpt p lo m γ e ⋆ pcrcpt p m hi γ e) = pcrcpt p lo hi γ e := by
  cases hb : p.block with
  | some b => rw [pcrcpt_eq hb, pcrcpt_eq hb, pcrcpt_eq hb, bcrcpt_split h1 h2]
  | none =>
    funext r; apply propext
    exact ⟨fun ⟨_, _, _, _, h, _⟩ => (pcrcpt_none hb h).elim, fun h => (pcrcpt_none hb h).elim⟩

/-- A claim owns no bytes and no knowledge (`EUpd.drop` forgets it). -/
theorem pclaim_ghost {r : Res} (h : pclaim p lo hi t r) : r.heap = FHeap.empty ∧ r.know = Know.none := by
  obtain ⟨b, h⟩ := h; obtain ⟨-, h, k, -⟩ := sep_lift.mp h; exact ⟨h, k⟩

theorem pcrcpt_ghost {r : Res} (h : pcrcpt p lo hi γ e r) : r.heap = FHeap.empty ∧ r.know = Know.none := by
  obtain ⟨b, h⟩ := h; obtain ⟨-, h, k, -⟩ := sep_lift.mp h; exact ⟨h, k⟩

end PtrClaims

/-- **Lend a pointer's claim** (`EUpd.lendC`). -/
theorem EUpd.plendC {γ e lo hi : Nat} {M : GMap} {t : STag} {p : Ptr} :
    EUpd (gauthP γ e M t ⋆ pclaim p lo hi t)
      (gauthP γ e M t ⋆ (pclaim p lo hi (some (γ, e)) ⋆ pcrcpt p lo hi γ e)) := by
  refine EUpd.trans (EUpd.of_imp (P' := FAssn.ex fun b => ⟪p.block = some b⟫ ⋆
    (gauthP γ e M t ⋆ bclaim b lo hi t)) fun r h => ?_) (EUpd.exAll fun b => EUpd.lift fun hb => ?_)
  · obtain ⟨b, h⟩ := sep_ex.mp (sep_comm h)
    obtain ⟨hb, h⟩ := sep_lift.mp (sep_assoc h)
    exact ⟨b, sep_lift.mpr ⟨hb, sep_comm h⟩⟩
  · refine EUpd.trans EUpd.lendC (EUpd.of_imp fun _ h => ?_)
    rw [pclaim_eq hb, pcrcpt_eq hb]; exact h

/-- **Revoke a pointer's claim receipt** of a past epoch (`EUpd.revokeC`). -/
theorem EUpd.prevokeC {γ e e' lo hi : Nat} {M : GMap} {t : STag} {p : Ptr} (he : e < e') :
    EUpd (gauthP γ e' M t ⋆ pcrcpt p lo hi γ e) (gauthP γ e' M t ⋆ pclaim p lo hi t) := by
  refine EUpd.trans (EUpd.of_imp (P' := FAssn.ex fun b => ⟪p.block = some b⟫ ⋆
    (gauthP γ e' M t ⋆ bcrcpt b lo hi γ e)) fun r h => ?_) (EUpd.exAll fun b => EUpd.lift fun hb => ?_)
  · obtain ⟨b, h⟩ := sep_ex.mp (sep_comm h)
    obtain ⟨hb, h⟩ := sep_lift.mp (sep_assoc h)
    exact ⟨b, sep_lift.mpr ⟨hb, sep_comm h⟩⟩
  · refine EUpd.trans (EUpd.revokeC he) (EUpd.of_imp fun _ h => ?_)
    rw [pclaim_eq hb]; exact h

end Full
end Zig
