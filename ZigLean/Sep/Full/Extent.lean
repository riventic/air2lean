import ZigLean.Sep.Full.Conc

/-!
# Extent updates (`docs/sep-full-state.md` §Block extents)

A block's extent claims (`bauth`, `bext`, `bshare`, `Res.lean`) change only by **frame-preserving
updates in a memory** (`EUpd P P'`): every resource of `P` that a memory holds with a frame can
be replaced by one of `P'` that the same memory holds with the same frame. Unlike `Upd`
(`Ghost.lean`), an `EUpd` may change extent claims, because it sees the memory that makes them
true. `FTriple.eupd` / `eupd_post` (and the `FTotalTriple`, `CTriple` versions) apply one to a
triple; `EUpd.frame` frames one.

The rules on one block's claims (all general; none is specific to an allocator):

| rule | from | to | side condition |
|---|---|---|---|
| `EUpd.lend` | `bauth b S K (q₁ + q₂)` | `bauth b S K q₁ ⋆ bshare b q₂ k` | `k ≤ S`, `0 < q₂` |
| `EUpd.unlend` | `bauth b S K q₁ ⋆ bshare b q₂ k` | `bauth b S K (q₁ + q₂)` | |
| `bshare_split` | `bshare b (q₁ + q₂) k` | `bshare b q₁ k ⋆ bshare b q₂ k` | `0 < q₁`, `0 < q₂` (an equivalence) |
| `EUpd.join` | `bshare b q₁ k₁ ⋆ bshare b q₂ k₂` | `bshare b (q₁ + q₂) (max k₁ k₂)` | |
| `EUpd.weaken` | `bshare b q k` | `bshare b q k'` | `k' ≤ k` |
| `EUpd.lendT` | `gauth γ e M ⋆ bshare b q k` | `gauth γ e M ⋆ (bshare b q k' (some (γ, e)) ⋆ brcpt b q k γ e)` | `k' ≤ k` |
| `EUpd.returnT` | `gauth γ e M ⋆ (bshare b q k' (some (γ, e)) ⋆ brcpt b q k γ e)` | `gauth γ e M ⋆ bshare b q k` | `k' ≤ k` |
| `EUpd.revoke` | `gauth γ e' M ⋆ brcpt b q k γ e` | `gauth γ e' M ⋆ bshare b q k` | `e < e'` |

The tagged rules (`docs/sep-full-state.md` §Epoch-tagged shares) are instances of `EUpd.ext1L`
(`ECell.StepE`: a step under every ledger status that contains the resource's ledger). The
untagged ones are instances of `EUpd.ext1` (`ECell.Step`): a change of the claims `c` on block `b` to `c'` that keeps
the authority claims, does not raise the fraction held below any bound beyond what `c` holds below
some bound (`ECell.total`), and whose every share is covered by a share of `c` at a bound at
least as high or by an authority claim of `c` of a size at least as high. `join` takes the higher
bound because the share at that bound already certifies it: this is what lets an allocator take a
grant's share back into its own share at the buffer's or node's bound.

Facts: `Holds.bshare` (a held share gives a live block of at least `k` bytes), `Holds.bauth` (the
authority gives the exact extent), and `EUpd.fact` (any fact of the memory, as an update).
-/

namespace Zig
namespace Full

open FAssn

/-! ## Fractions -/

namespace Frac

/-- Half of a fraction. -/
def half (q : Frac) : Frac := ⟨q.val / 2, by have := q.nonneg; grind⟩

@[simp] theorem add_val (a b : Frac) : (a.add b).val = a.val + b.val := rfl

theorem half_add_half (q : Frac) : q.half.add q.half = q := eq (by simp only [add, half]; grind)

theorem half_pos {q : Frac} (h : 0 < q.val) : 0 < q.half.val := by simp only [half]; grind

end Frac

/-! ## The claims on one block -/

namespace ECell

theorem total_auth1 (S : Nat) (K : BlockKind) (q : Frac) :
    ∀ n, (auth1 S K q).total n = if n = 0 then 0 else q.val
  | 0 => rfl
  | n + 1 => by
    rw [total, total_auth1 S K q n]
    simp only [auth1, Frac.zero]
    by_cases hn : n = 0 <;> simp [hn] <;> grind

theorem total_share (q : Frac) (k : Nat) : ∀ n, (share q k).total n = if k < n then q.val else 0
  | 0 => by simp [total]
  | n + 1 => by
    rw [total, total_share q k n]
    simp only [share]
    by_cases h1 : k < n
    · rw [if_pos h1, if_neg (by omega), if_pos (by omega)]; simp only [Frac.zero]; grind
    · by_cases h2 : n = k
      · subst h2; rw [if_neg h1, if_pos rfl, if_pos (by omega)]; grind
      · rw [if_neg h1, if_neg h2, if_neg (by omega)]; simp only [Frac.zero]; grind

/-- **A local step of one block's claims under the ledger status `ep`**: the authority claims
stay; against every frame `d`, the counted fraction (`ECell.wsum`) with `c'` is at most the one
with `c` somewhere; every live claim of `c'` is covered by a live claim of `c` at a bound at least
as high or by an authority claim of `c`; and `c'` puts no tag after a ledger's epoch or on a ledger
that neither exists nor was tagged by `c`. -/
def StepE (ep : Nat → Nat → Prop) (c c' : ECell) : Prop :=
  c'.auth = c.auth ∧
    (∀ d n N E, ∃ n' N' E', (c'.add d).wsum ep n N E ≤ (c.add d).wsum ep n' N' E') ∧
    (∀ j, c'.Req ep j → (∃ j', j ≤ j' ∧ c.Req ep j') ∨ ∃ S K, 0 < c.auth (S, K) ∧ j ≤ S) ∧
    (∀ γ e e', ep γ e → e < e' → (∀ k, (c.tsh γ e' k).val = 0 ∧ (c.rc γ e' k).val = 0) →
      ∀ k, (c'.tsh γ e' k).val = 0 ∧ (c'.rc γ e' k).val = 0) ∧
    (∀ γ, (∀ e, ¬ ep γ e) → (∀ e k, (c.tsh γ e k).val = 0 ∧ (c.rc γ e k).val = 0) →
      ∀ e k, (c'.tsh γ e k).val = 0 ∧ (c'.rc γ e k).val = 0)

theorem add_tags_zero {a b : ECell} {γ e k : Nat}
    (h : ((a.add b).tsh γ e k).val = 0 ∧ ((a.add b).rc γ e k).val = 0) :
    (a.tsh γ e k).val = 0 ∧ (a.rc γ e k).val = 0 ∧ (b.tsh γ e k).val = 0 ∧ (b.rc γ e k).val = 0 := by
  simp only [add, Frac.add_val] at h
  have := (a.tsh γ e k).nonneg; have := (b.tsh γ e k).nonneg
  have := (a.rc γ e k).nonneg; have := (b.rc γ e k).nonneg
  grind

/-- A step keeps every frame `d` that `c` composed with, validly and truly in `m`. -/
theorem StepE.ok {ep : Nat → Nat → Prop} {m : Mem} {b : BlockId} {c c' d : ECell}
    (hst : StepE ep c c') (hv : (c.add d).Valid) (hto : (c.add d).TagOk ep)
    (ht : (c.add d).TrueIn ep m b) :
    (c'.add d).Valid ∧ (c'.add d).TagOk ep ∧ (c'.add d).TrueIn ep m b := by
  obtain ⟨hauth, hw, hsh, hfut, -⟩ := hst
  obtain ⟨h1, h2, -⟩ := hv
  obtain ⟨ta, ts⟩ := ht
  have ea : (c'.add d).auth = (c.add d).auth := by simp only [add, hauth]
  have hw' : ∀ n N E, (c'.add d).wsum ep n N E ≤ 1 := fun n N E => by
    obtain ⟨n', N', E', h⟩ := hw d n N E
    exact Rat.le_trans h (hto.1 n' N' E')
  refine ⟨⟨fun x => by rw [ea]; exact h1 x, fun x y hx hy => h2 x y (by rw [← ea]; exact hx)
    (by rw [← ea]; exact hy), fun n => ?_⟩, ⟨hw', fun γ e e' k he hlt => ?_⟩,
    fun S K hp => ta S K (by rw [← ea]; exact hp), fun j hp => ?_⟩
  · have := hw' n 0 0; simp only [wsum, gsum] at this; grind
  · have hz := fun k => add_tags_zero (hto.2 γ e e' k he hlt)
    have := hfut γ e e' he hlt (fun k => ⟨(hz k).1, (hz k).2.1⟩) k
    simp only [add, Frac.add_val, this.1, this.2, (hz k).2.2.1, (hz k).2.2.2]; grind
  · rcases Req_add.mp hp with hc | hd
    · rcases hsh j hc with ⟨j', hjj, hj'⟩ | ⟨S, K, hSK, hjS⟩
      · obtain ⟨blk, hb, hl, hs, hlo⟩ := ts j' (Req_add.mpr (.inl hj'))
        exact ⟨blk, hb, hl, by omega, hlo⟩
      · obtain ⟨blk, hb, hl, hs, hk, hlo⟩ := ta S K (by simp only [add]; omega)
        exact ⟨blk, hb, hl, by omega, by rw [hk, hs]; exact hlo⟩
    · exact ts j (Req_add.mpr (.inr hd))

/-- No tagged claim and no receipt. -/
def NoTag (c : ECell) : Prop := ∀ γ e k, (c.tsh γ e k).val = 0 ∧ (c.rc γ e k).val = 0

theorem NoTag.auth1 (S : Nat) (K : BlockKind) (q : Frac) : (auth1 S K q).NoTag := fun _ _ _ => ⟨rfl, rfl⟩

theorem NoTag.share (q : Frac) (k : Nat) : (share q k).NoTag := fun _ _ _ => ⟨rfl, rfl⟩

theorem NoTag.add {a b : ECell} (ha : a.NoTag) (hb : b.NoTag) : (a.add b).NoTag := fun γ e k => by
  simp only [ECell.add, Frac.add_val, (ha γ e k).1, (ha γ e k).2, (hb γ e k).1, (hb γ e k).2]
  grind

theorem NoTag.tags_eq {c c' : ECell} (h : c.NoTag) (h' : c'.NoTag) :
    ∀ γ e k, (c'.tsh γ e k).val = (c.tsh γ e k).val ∧ (c'.rc γ e k).val = (c.rc γ e k).val :=
  fun γ e k => ⟨by rw [(h γ e k).1, (h' γ e k).1], by rw [(h γ e k).2, (h' γ e k).2]⟩

/-- **A local step of one block's untagged claims** (module doc): the authority claims and the
tagged claims stay, the fraction below every bound is at most what `c` held below some bound, and
every share of `c'` is covered by a share of `c` at a bound at least as high or by an authority
claim of `c`. -/
def Step (c c' : ECell) : Prop :=
  c'.auth = c.auth ∧ (∀ n, ∃ N, n ≤ N ∧ c'.total n ≤ c.total N) ∧
    (∀ j, 0 < (c'.sh j).val → (∃ j', j ≤ j' ∧ 0 < (c.sh j').val) ∨ ∃ S K, 0 < c.auth (S, K) ∧ j ≤ S) ∧
    ∀ γ e k, (c'.tsh γ e k).val = (c.tsh γ e k).val ∧ (c'.rc γ e k).val = (c.rc γ e k).val

theorem tagWt_congr_vals {ep : Nat → Nat → Prop} {γ e : Nat} {T R T' R' : Nat → Frac}
    (hT : ∀ k, (T' k).val = (T k).val) (hR : ∀ k, (R' k).val = (R k).val) (n : Nat) :
    tagWt ep γ e T' R' n = tagWt ep γ e T R n := by
  unfold tagWt; rw [ftot_congr hT, ftot_congr hR]

/-- An untagged step is a step under every ledger status. -/
theorem Step.toE {c c' : ECell} (h : Step c c') (ep : Nat → Nat → Prop) : StepE ep c c' := by
  obtain ⟨hauth, htot, hsh, htag⟩ := h
  have hv : ∀ d γ e k, ((c'.add d).tsh γ e k).val = ((c.add d).tsh γ e k).val ∧
      ((c'.add d).rc γ e k).val = ((c.add d).rc γ e k).val := fun d γ e k => by
    simp only [add, Frac.add_val, (htag γ e k).1, (htag γ e k).2, and_self]
  refine ⟨hauth, fun d n N E => ?_, fun j hj => ?_, fun γ e e' _ _ hz k => ?_, fun γ _ hz e k => ?_⟩
  · obtain ⟨n', hnn, hle⟩ := htot n
    refine ⟨n', N, E, ?_⟩
    have := gsum_le (f := fun γ e => tagWt ep γ e ((c'.add d).tsh γ e) ((c'.add d).rc γ e) n)
      (g := fun γ e => tagWt ep γ e ((c.add d).tsh γ e) ((c.add d).rc γ e) n') (fun γ e => by
        rw [tagWt_congr_vals (fun k => (hv d γ e k).1) (fun k => (hv d γ e k).2) n]
        exact tagWt_mono ep γ e _ _ hnn) N E
    have := (d.total_mono hnn)
    simp only [wsum, total_add] at this ⊢
    grind
  · rcases hj with hj | ⟨γ, e, ⟨he, hp⟩ | ⟨he, hp⟩⟩
    · rcases hsh j hj with ⟨j', h1, h2⟩ | h
      · exact .inl ⟨j', h1, .inl h2⟩
      · exact .inr h
    · exact .inl ⟨j, Nat.le_refl _, .inr ⟨γ, e, .inl ⟨he, by rw [← (htag γ e j).1]; exact hp⟩⟩⟩
    · exact .inl ⟨j, Nat.le_refl _, .inr ⟨γ, e, .inr ⟨he, by rw [← (htag γ e j).2]; exact hp⟩⟩⟩
  · rw [(htag γ e' k).1, (htag γ e' k).2]; exact hz k
  · rw [(htag γ e k).1, (htag γ e k).2]; exact hz e k

end ECell

/-! ### Steps on tagged claims -/

theorem ftot_single {f : Nat → Frac} {k : Nat} (h : ∀ j, j ≠ k → (f j).val = 0) :
    ∀ n, ftot f n = if k < n then (f k).val else 0
  | 0 => by simp [ftot]
  | n + 1 => by
    rw [ftot, ftot_single h n]
    by_cases h1 : k < n
    · rw [if_pos h1, if_pos (by omega), h n (by omega)]; grind
    · by_cases h2 : n = k
      · subst h2; rw [if_neg h1, if_pos (by omega)]; grind
      · rw [if_neg h1, if_neg (by omega), h n h2]; grind

theorem tagWt_shift {ep : Nat → Nat → Prop} {γ e : Nat} {T R T' R' : Nat → Frac} {n : Nat} {δ : Rat}
    (hδ : 0 ≤ δ) (hT : ftot T' n ≤ ftot T n + δ) (hR : ftot R' n ≤ ftot R n + δ) :
    tagWt ep γ e T' R' n ≤ tagWt ep γ e T R n + δ := by
  unfold tagWt; split
  · grind
  · split <;> grind

theorem tagWt_shift_ge {ep : Nat → Nat → Prop} {γ e : Nat} {T R T' R' : Nat → Frac} {n : Nat}
    {δ : Rat} (hlive : ep γ e ∨ ∃ e', e < e' ∧ ep γ e') (hT : ep γ e → ftot T' n + δ ≤ ftot T n)
    (hR : ftot R' n + δ ≤ ftot R n) : tagWt ep γ e T' R' n + δ ≤ tagWt ep γ e T R n := by
  unfold tagWt
  by_cases h : ep γ e
  · rw [if_pos h, if_pos h]; have := hT h; grind
  · rw [if_neg h, if_neg h, if_pos (hlive.resolve_left h), if_pos (hlive.resolve_left h)]; exact hR

theorem esum_single_ge {f g : Nat → Rat} {e₀ : Nat} {δ : Rat}
    (h : ∀ e, e ≠ e₀ → f e ≤ g e) (h₀ : f e₀ + δ ≤ g e₀) : ∀ E, e₀ < E → esum f E + δ ≤ esum g E
  | 0, h' => absurd h' (Nat.not_lt_zero _)
  | E + 1, _ => by
    simp only [esum]
    by_cases he : E = e₀
    · subst he
      have := esum_le' (f := f) (g := g) (E := E) fun e he' => h e (by omega)
      grind
    · have := esum_single_ge h h₀ E (by omega); have := h E he; grind

theorem gsum_single_ge {f g : Nat → Nat → Rat} {γ₀ e₀ : Nat} {δ : Rat}
    (h : ∀ γ e, (γ, e) ≠ (γ₀, e₀) → f γ e ≤ g γ e) (h₀ : f γ₀ e₀ + δ ≤ g γ₀ e₀) :
    ∀ N E, γ₀ < N → e₀ < E → gsum f N E + δ ≤ gsum g N E
  | 0, _, h', _ => absurd h' (Nat.not_lt_zero _)
  | N + 1, E, _, hE => by
    simp only [gsum]
    by_cases hN : N = γ₀
    · subst hN
      have := gsum_le' (f := f) (g := g) (N := N) E fun γ e hγ => h γ e (by intro x; cases x; omega)
      have := esum_single_ge (f := f N) (g := g N) (e₀ := e₀) (fun e he => h N e (by
        intro x; cases x; exact he rfl)) h₀ E hE
      grind
    · have := gsum_single_ge h h₀ N E (by omega) hE
      have := esum_le (fun e => h N e (by intro x; cases x; exact hN rfl)) E
      grind

namespace ECell

theorem tshare_tsh (γ e : Nat) (q : Frac) (k γ' e' j : Nat) :
    ((tshare γ e q k).tsh γ' e' j).val = if γ' = γ ∧ e' = e ∧ j = k then q.val else 0 := by
  simp only [tshare]; split <;> rfl

theorem rcpt_rc (γ e : Nat) (q : Frac) (k γ' e' j : Nat) :
    ((rcpt γ e q k).rc γ' e' j).val = if γ' = γ ∧ e' = e ∧ j = k then q.val else 0 := by
  simp only [rcpt]; split <;> rfl

/-- The weight of tag `(γ, e)` of `c.add d`, as a function of the frame's tags. -/
theorem tagWt_add_eq (ep : Nat → Nat → Prop) (c d : ECell) (γ e n : Nat) :
    tagWt ep γ e ((c.add d).tsh γ e) ((c.add d).rc γ e) n =
      tagWt ep γ e (fun k => (c.tsh γ e k).add (d.tsh γ e k)) (fun k => (c.rc γ e k).add (d.rc γ e k)) n :=
  rfl

/-- Changing the claims at one tag `(γ, e)` only, by at most `δ` in the weight below `n`. -/
theorem gsum_tag_le {ep : Nat → Nat → Prop} {c c' d : ECell} {γ e n : Nat} {δ : Rat} (hδ : 0 ≤ δ)
    (hoth : ∀ γ' e' j, (γ', e') ≠ (γ, e) → (c'.tsh γ' e' j).val = (c.tsh γ' e' j).val ∧
      (c'.rc γ' e' j).val = (c.rc γ' e' j).val)
    (hT : ftot (c'.tsh γ e) n ≤ ftot (c.tsh γ e) n + δ) (hR : ftot (c'.rc γ e) n ≤ ftot (c.rc γ e) n + δ)
    (N E : Nat) :
    gsum (fun γ e => tagWt ep γ e ((c'.add d).tsh γ e) ((c'.add d).rc γ e) n) N E ≤
      gsum (fun γ e => tagWt ep γ e ((c.add d).tsh γ e) ((c.add d).rc γ e) n) N E + δ := by
  refine gsum_single (γ₀ := γ) (e₀ := e) hδ (fun γ' e' hne => ?_) ?_ N E
  · rw [tagWt_congr_vals (T := (c.add d).tsh γ' e') (R := (c.add d).rc γ' e')
      (fun j => by simp only [add, Frac.add_val, (hoth γ' e' j hne).1])
      (fun j => by simp only [add, Frac.add_val, (hoth γ' e' j hne).2])]
    exact Rat.le_refl
  · refine tagWt_shift hδ ?_ ?_
    · show ftot (fun k => (c'.tsh γ e k).add (d.tsh γ e k)) n ≤
        ftot (fun k => (c.tsh γ e k).add (d.tsh γ e k)) n + δ
      rw [ftot_add, ftot_add]; grind
    · show ftot (fun k => (c'.rc γ e k).add (d.rc γ e k)) n ≤
        ftot (fun k => (c.rc γ e k).add (d.rc γ e k)) n + δ
      rw [ftot_add, ftot_add]; grind

/-- Changing the claims at one live tag `(γ, e)` only, lowering its weight below `n` by `δ`. -/
theorem gsum_tag_ge {ep : Nat → Nat → Prop} {c c' d : ECell} {γ e n : Nat} {δ : Rat}
    (hoth : ∀ γ' e' j, (γ', e') ≠ (γ, e) → (c'.tsh γ' e' j).val = (c.tsh γ' e' j).val ∧
      (c'.rc γ' e' j).val = (c.rc γ' e' j).val)
    (hlive : ep γ e ∨ ∃ e', e < e' ∧ ep γ e')
    (hT : ep γ e → ftot (c'.tsh γ e) n + δ ≤ ftot (c.tsh γ e) n)
    (hR : ftot (c'.rc γ e) n + δ ≤ ftot (c.rc γ e) n) (N E : Nat) (hN : γ < N) (hE : e < E) :
    gsum (fun γ e => tagWt ep γ e ((c'.add d).tsh γ e) ((c'.add d).rc γ e) n) N E + δ ≤
      gsum (fun γ e => tagWt ep γ e ((c.add d).tsh γ e) ((c.add d).rc γ e) n) N E := by
  refine gsum_single_ge (γ₀ := γ) (e₀ := e) (fun γ' e' hne => ?_) ?_ N E hN hE
  · rw [tagWt_congr_vals (T := (c.add d).tsh γ' e') (R := (c.add d).rc γ' e')
      (fun j => by simp only [add, Frac.add_val, (hoth γ' e' j hne).1])
      (fun j => by simp only [add, Frac.add_val, (hoth γ' e' j hne).2])]
    exact Rat.le_refl
  · refine tagWt_shift_ge hlive (fun h => ?_) ?_
    · show ftot (fun k => (c'.tsh γ e k).add (d.tsh γ e k)) n + δ ≤
        ftot (fun k => (c.tsh γ e k).add (d.tsh γ e k)) n
      rw [ftot_add, ftot_add]; have := hT h; grind
    · show ftot (fun k => (c'.rc γ e k).add (d.rc γ e k)) n + δ ≤
        ftot (fun k => (c.rc γ e k).add (d.rc γ e k)) n
      rw [ftot_add, ftot_add]; grind

end ECell

/-- Replacing the claims on one block, next to a ledger part `L`, keeps a composition that the
change keeps at that block under every ledger status that contains `L`'s. -/
theorem GOk.ext1 {m : Mem} {L : Ghost} (hL : ∀ x, L.extent x = ECell.unit) {b : BlockId}
    {c c' : ECell} {gF : Ghost} (hok : GOk m (L.add (Ghost.atExt b c)) gF)
    (h : ∀ ep : Nat → Nat → Prop, (∀ γ e, L.ep γ e → ep γ e) → (∀ γ e e', ep γ e → ep γ e' → e = e') →
      ECell.StepE ep c c') :
    GOk m (L.add (Ghost.atExt b c')) gF := by
  obtain ⟨⟨⟨hv, hx⟩, N, hN⟩, ht⟩ := hok
  have hV : Ghost.Valid ((L.add (Ghost.atExt b c)).add gF) := ⟨hv, hx⟩
  have eled : ((L.add (Ghost.atExt b c')).add gF).led = ((L.add (Ghost.atExt b c)).add gF).led := by
    funext γ; simp [Ghost.add, Ghost.atExt]
  have eep : ((L.add (Ghost.atExt b c')).add gF).ep = ((L.add (Ghost.atExt b c)).add gF).ep := by
    funext γ e; simp only [Ghost.ep, eled]
  have ex : ∀ x, x ≠ b → ((L.add (Ghost.atExt b c')).add gF).extent x =
      ((L.add (Ghost.atExt b c)).add gF).extent x := fun x hx => by
    simp [Ghost.add, Ghost.atExt, hx]
  have eb : ∀ c₀, ((L.add (Ghost.atExt b c₀)).add gF).extent b = c₀.add (gF.extent b) := fun c₀ => by
    simp [Ghost.add, Ghost.atExt, hL]
  have hst := h ((L.add (Ghost.atExt b c)).add gF).ep (fun γ e h => Ghost.ep_add (Ghost.ep_add h))
    (fun _ _ _ => hV.ep_uniq)
  have hb := hst.ok (by rw [← eb]; exact (hx b).1) (by rw [← eb]; exact (hx b).2)
    (by rw [← eb]; exact ht b)
  refine ⟨⟨⟨by rw [eled]; exact hv, fun x => ?_⟩, N, fun γ hγ => ⟨by rw [eled]; exact (hN γ hγ).1,
    fun x e k => ?_⟩⟩, fun x => ?_⟩
  · rw [eep]
    by_cases e : x = b
    · subst e; rw [eb]; exact ⟨hb.1, hb.2.1⟩
    · rw [ex x e]; exact hx x
  · by_cases e' : x = b
    · subst e'
      rw [eb]
      have hz := fun e k => ECell.add_tags_zero (by rw [← eb]; exact (hN γ hγ).2 x e k)
      have hnep : ∀ e, ¬ ((L.add (Ghost.atExt x c)).add gF).ep γ e := fun e ⟨M, hM⟩ => by
        rw [(hN γ hγ).1] at hM; simp [GCell.unit] at hM
      have := hst.2.2.2.2 γ hnep (fun e k => ⟨(hz e k).1, (hz e k).2.1⟩) e k
      simp only [ECell.add, Frac.add_val, this.1, this.2, (hz e k).2.2.1, (hz e k).2.2.2]; grind
    · rw [ex x e']; exact (hN γ hγ).2 x e k
  · show ECell.TrueIn _ _ _ _
    rw [eep]
    by_cases e : x = b
    · subst e; rw [eb]; exact hb.2.2
    · rw [ex x e]; exact ht x

/-! ## Updates in a memory -/

/-- **A frame-preserving update in a memory**: every resource of `P` that `m` holds with a frame
can be replaced by one of `P'` that `m` holds with the same frame. -/
def EUpd (P P' : FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → m.FSeq → ∃ r', Holds m r' rF ∧ P' r'

/-- `m` holds `r₁ ⋆ r₂` with frame `rF` if it holds `r₁` with frame `r₂ ⋆ rF` (`Holds.split`
backwards). -/
theorem Holds.join {m : Mem} {r₁ r₂ rF : Res} (hd : FHeap.Disjoint r₁.heap r₂.heap)
    (h2F : FHeap.Disjoint r₂.heap rF.heap)
    (hh : Holds m r₁ ⟨r₂.heap ∪ rF.heap, r₂.know.union rF.know, r₂.gh.add rF.gh⟩) :
    Holds m ⟨r₁.heap ∪ r₂.heap, r₁.know.union r₂.know, r₁.gh.add r₂.gh⟩ rF := by
  obtain ⟨hd', hh', hk', hkF', hg'⟩ := hh
  exact ⟨FHeap.disjoint_union_left.mpr ⟨(FHeap.disjoint_union_right.mp hd').2, h2F⟩,
    by rw [FHeap.union_assoc]; exact hh', hk'.union hkF'.left, hkF'.right, GOk.assoc.mpr hg'⟩

namespace EUpd

variable {P P' P'' R : FAssn}

theorem of_imp (h : ∀ r, P r → P' r) : EUpd P P' := fun _ r _ hh hp _ => ⟨r, hh, h r hp⟩

theorem trans (h₁ : EUpd P P') (h₂ : EUpd P' P'') : EUpd P P'' := fun m r rF hh hp hs => by
  obtain ⟨r₁, hh₁, hp₁⟩ := h₁ m r rF hh hp hs
  exact h₂ m r₁ rF hh₁ hp₁ hs

/-- A ghost update (`Upd`) is an update in every memory: it keeps the extent claims. -/
theorem of_upd (hu : Upd P P') : EUpd P P' := fun m r rF hh hp _ => by
  obtain ⟨r', hp', e, k, x, hg, ht⟩ := hu r hp rF.gh hh.ghost.1
  exact ⟨r', ⟨by rw [e]; exact hh.disj, by rw [e]; exact hh.heap, by rw [k]; exact hh.know,
    hh.knowF, ⟨hg, ht m hh.ghost.2⟩⟩, hp'⟩

/-- Updates frame. -/
theorem frame (h : EUpd P P') : EUpd (P ⋆ R) (P' ⋆ R) := by
  rintro m _ rF hh ⟨r₁, r₂, hd, rfl, hp, hr⟩ hs
  have h2F := (FHeap.disjoint_union_left.mp hh.disj).2
  obtain ⟨r₁', hh', hp'⟩ := h m r₁ _ (Holds.split hd hh) hp hs
  have hd' := (FHeap.disjoint_union_right.mp hh'.disj).1
  exact ⟨_, Holds.join hd' h2F hh', ⟨r₁', r₂, hd', rfl, hp', hr⟩⟩

theorem frameL (h : EUpd P P') : EUpd (R ⋆ P) (R ⋆ P') :=
  trans (of_imp fun _ h => sep_comm h) (trans (frame h) (of_imp fun _ h => sep_comm h))

/-- A fact of every memory that holds `P`. -/
theorem fact {φ : Prop} (hφ : ∀ m r rF, Holds m r rF → P r → m.FSeq → φ) : EUpd P (⟪φ⟫ ⋆ P) :=
  fun m r rF hh hp hs => ⟨r, hh, sep_lift.mpr ⟨hφ m r rF hh hp hs, hp⟩⟩

/-- **A local update of one block's claims** (`ECell.Step`). -/
theorem ext1L {L : Ghost} (hL : ∀ x, L.extent x = ECell.unit) {b : BlockId} {c c' : ECell}
    (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, L.add (Ghost.atExt b c)⟩ ∧
      P' ⟨FHeap.empty, Know.none, L.add (Ghost.atExt b c')⟩ ∧
      ∀ ep : Nat → Nat → Prop, (∀ γ e, L.ep γ e → ep γ e) → (∀ γ e e', ep γ e → ep γ e' → e = e') →
        ECell.StepE ep c c') : EUpd P P' := by
  intro m r rF hh hr _
  obtain ⟨e, hp', hst⟩ := hp r hr
  subst e
  exact ⟨⟨FHeap.empty, Know.none, L.add (Ghost.atExt b c')⟩,
    ⟨hh.disj, hh.heap, hh.know, hh.knowF, GOk.ext1 hL hh.ghost hst⟩, hp'⟩

theorem ext1 {b : BlockId} {c c' : ECell}
    (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, Ghost.atExt b c⟩ ∧
      P' ⟨FHeap.empty, Know.none, Ghost.atExt b c'⟩ ∧ ECell.Step c c') : EUpd P P' :=
  ext1L (L := Ghost.unit) (fun _ => rfl) fun r h => by
    obtain ⟨e, hp', hst⟩ := hp r h
    exact ⟨by rw [Ghost.unit_add]; exact e, by rw [Ghost.unit_add]; exact hp', fun ep _ _ => hst.toE ep⟩

end EUpd

/-! ## Rules on extent assertions -/

section Rules

variable {b : BlockId} {S k k' : Nat} {K : BlockKind} {q q₁ q₂ : Frac}

theorem bauth_eq {r : Res} (h : bauth b S K q r) :
    r = ⟨FHeap.empty, Know.none, Ghost.atExt b (ECell.auth1 S K q)⟩ := by
  obtain ⟨h1, h2, h3⟩ := h; rw [res_eta r, h1, h2, h3]

theorem bshareT_eq {r : Res} {t : Option (Nat × Nat)} (h : bshare b q k t r) :
    r = ⟨FHeap.empty, Know.none, Ghost.atExt b (ECell.shareT t q k)⟩ := by
  obtain ⟨-, h1, h2, h3⟩ := h; rw [res_eta r, h1, h2, h3]

theorem bshare_eq {r : Res} (h : bshare b q k none r) :
    r = ⟨FHeap.empty, Know.none, Ghost.atExt b (ECell.share q k)⟩ := bshareT_eq h

theorem brcpt_eq {r : Res} {γ e : Nat} (h : brcpt b q k γ e r) :
    r = ⟨FHeap.empty, Know.none, Ghost.atExt b (ECell.rcpt γ e q k)⟩ := by
  obtain ⟨-, h1, h2, h3⟩ := h; rw [res_eta r, h1, h2, h3]

/-- Two extent assertions on `b`, as one claim cell. -/
theorem ext_sep_eq {P Q : FAssn} {c c' : ECell} {r : Res}
    (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, Ghost.atExt b c⟩)
    (hq : ∀ r, Q r → r = ⟨FHeap.empty, Know.none, Ghost.atExt b c'⟩) (h : (P ⋆ Q) r) :
    r = ⟨FHeap.empty, Know.none, Ghost.atExt b (c.add c')⟩ := by
  obtain ⟨r₁, r₂, -, rfl, h1, h2⟩ := h
  rw [hp _ h1, hq _ h2]
  simp [FHeap.union_empty, Know.union_none, Ghost.atExt_add]

theorem ext_sep_intro {P Q : FAssn} {c c' : ECell}
    (hp : P ⟨FHeap.empty, Know.none, Ghost.atExt b c⟩) (hq : Q ⟨FHeap.empty, Know.none, Ghost.atExt b c'⟩) :
    (P ⋆ Q) ⟨FHeap.empty, Know.none, Ghost.atExt b (c.add c')⟩ :=
  ⟨_, _, FHeap.disjoint_empty _, by simp [FHeap.union_empty, Know.union_none, Ghost.atExt_add], hp, hq⟩

/-- **Lend a share** off the authority, at a bound `k` up to the block's size. -/
theorem EUpd.lend (hk : k ≤ S) (hq : 0 < q₂.val) :
    EUpd (bauth b S K (q₁.add q₂)) (bauth b S K q₁ ⋆ bshare b q₂ k) := by
  refine EUpd.ext1 (c' := (ECell.auth1 S K q₁).add (ECell.share q₂ k)) fun _ h =>
    ⟨bauth_eq h, ext_sep_intro ⟨rfl, rfl, rfl⟩ ⟨hq, rfl, rfl, rfl⟩,
    by funext x; simp [ECell.add, ECell.auth1, ECell.share], fun n => ⟨n + 1, by omega, ?_⟩,
    fun j hj => .inr ⟨S, K, by simp [ECell.auth1], ?_⟩,
    ECell.NoTag.tags_eq (.auth1 _ _ _) (.add (.auth1 _ _ _) (.share _ _))⟩
  · rw [ECell.total_add, ECell.total_auth1, ECell.total_auth1, ECell.total_share]
    have := q₁.nonneg; have := q₂.nonneg
    simp only [Frac.add_val]; split <;> split <;> grind
  · simp only [ECell.add, ECell.auth1, ECell.share, Frac.add_val, Frac.zero] at hj
    by_cases e : j = 0
    · omega
    · by_cases e' : j = k
      · omega
      · simp only [e, e', if_false] at hj; grind

/-- **Give a share back** to the authority (from any bound). -/
theorem EUpd.unlend : EUpd (bauth b S K q₁ ⋆ bshare b q₂ k) (bauth b S K (q₁.add q₂)) := by
  refine EUpd.ext1 fun _ h => ⟨ext_sep_eq (fun _ h => bauth_eq h) (fun _ h => bshare_eq h) h,
    ⟨rfl, rfl, rfl⟩, by funext x; simp [ECell.add, ECell.auth1, ECell.share],
    fun n => ⟨Max.max n (k + 1), by omega, ?_⟩, fun j hj => .inr ⟨S, K, by simp [ECell.add, ECell.auth1, ECell.share], ?_⟩,
    ECell.NoTag.tags_eq (.add (.auth1 _ _ _) (.share _ _)) (.auth1 _ _ _)⟩
  · rw [ECell.total_add, ECell.total_auth1, ECell.total_auth1, ECell.total_share]
    have := q₁.nonneg; have := q₂.nonneg
    simp only [Frac.add_val]
    by_cases hn : n = 0
    · subst hn; simp only [if_pos]; rw [if_neg (by omega), if_pos (by omega)]; grind
    · rw [if_neg hn, if_neg (by omega), if_pos (by omega)]; exact Rat.le_refl
  · simp only [ECell.auth1, Frac.zero] at hj
    by_cases e : j = 0
    · omega
    · simp [e] at hj

/-- **Split and join a share** at one bound. -/
theorem bshare_split {r : Res} (h₁ : 0 < q₁.val) (h₂ : 0 < q₂.val) :
    bshare b (q₁.add q₂) k none r ↔ (bshare b q₁ k ⋆ bshare b q₂ k) r := by
  have e : ECell.share (q₁.add q₂) k = (ECell.share q₁ k).add (ECell.share q₂ k) := by
    ext <;> simp only [ECell.share, ECell.add] <;> (try split) <;> simp
  constructor
  · intro h
    rw [bshare_eq h, e]
    exact ext_sep_intro ⟨h₁, rfl, rfl, rfl⟩ ⟨h₂, rfl, rfl, rfl⟩
  · intro h
    rw [ext_sep_eq (fun _ h => bshare_eq h) (fun _ h => bshare_eq h) h, ← e]
    exact ⟨by simp only [Frac.add_val]; grind, rfl, rfl, rfl⟩

/-- **Join two shares** at the higher bound: the share there already certifies it. -/
theorem EUpd.join : EUpd (bshare b q₁ k ⋆ bshare b q₂ k') (bshare b (q₁.add q₂) (Max.max k k')) := by
  refine EUpd.ext1 (b := b) (c := (ECell.share q₁ k).add (ECell.share q₂ k'))
    (c' := ECell.share (q₁.add q₂) (Max.max k k')) fun r h => ?_
  have e := ext_sep_eq (fun _ h => bshare_eq h) (fun _ h => bshare_eq h) h
  obtain ⟨r₁, r₂, -, -, ⟨hp1, -⟩, ⟨hp2, -⟩⟩ := h
  have := q₁.nonneg; have := q₂.nonneg
  refine ⟨e, ⟨by simp only [Frac.add_val]; grind, rfl, rfl, rfl⟩,
    by funext x; simp [ECell.add, ECell.share], fun n => ⟨n, Nat.le_refl _, ?_⟩, fun j hj => ?_,
    ECell.NoTag.tags_eq (.add (.share _ _) (.share _ _)) (.share _ _)⟩
  · rw [ECell.total_add, ECell.total_share, ECell.total_share, ECell.total_share]
    simp only [Frac.add_val]
    by_cases h1 : Max.max k k' < n
    · rw [if_pos h1, if_pos (by omega), if_pos (by omega)]; exact Rat.le_refl
    · rw [if_neg h1]; split <;> split <;> grind
  · simp only [ECell.share, Frac.zero] at hj
    split at hj
    · rename_i e; subst e
      left
      rcases Nat.le_total k k' with hkk | hkk
      · refine ⟨k', by omega, ?_⟩
        simp only [ECell.add, ECell.share, Frac.add_val, Frac.zero]
        split <;> grind
      · refine ⟨k, by omega, ?_⟩
        simp only [ECell.add, ECell.share, Frac.add_val, Frac.zero]
        split <;> grind
    · simp [Frac.zero] at hj

/-- **Weaken a share's bound.** -/
theorem EUpd.weaken (h : k' ≤ k) : EUpd (bshare b q k) (bshare b q k') := by
  refine EUpd.ext1 (c' := ECell.share q k') fun r hr => ⟨bshare_eq hr, ⟨hr.1, rfl, rfl, rfl⟩, rfl,
    fun n => ⟨Max.max n (k + 1), by omega, ?_⟩, fun j hj => .inl ⟨k, ?_, ?_⟩,
    ECell.NoTag.tags_eq (.share _ _) (.share _ _)⟩
  · rw [ECell.total_share, ECell.total_share]
    have := q.nonneg
    split
    · rw [if_pos (by omega)]; exact Rat.le_refl
    · split <;> grind
  · simp only [ECell.share, Frac.zero] at hj; split at hj <;> simp_all [Frac.zero] <;> omega
  · simp only [ECell.share, if_pos]; exact hr.1

/-! ## Facts -/

/-- The claims of a held resource are true. -/
theorem Holds.extTrue {m : Mem} {r rF : Res} (hh : Holds m r rF) : ExtTrue m r.gh :=
  ExtTrue.of_add hh.ghost.2

theorem Holds.claims {m : Mem} {r rF : Res} {P R : FAssn} (hh : Holds m r rF) (h : (P ⋆ R) r) :
    ∃ r₁, P r₁ ∧ ExtTrue m r₁.gh := by
  obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := h
  exact ⟨r₁, h1, ExtTrue.of_add hh.extTrue⟩

/-- **A held share gives a live block** of at least `k` bytes. -/
theorem Holds.bshare {m : Mem} {r rF : Res} {R : FAssn} (hh : Holds m r rF) (h : (bshare b q k ⋆ R) r) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ k ≤ blk.bytes.size ∧
      blk.kind.mappedLo < blk.bytes.size := by
  obtain ⟨r₁, h1, ht⟩ := hh.claims h
  have hq := h1.1
  rw [bshare_eq h1] at ht
  exact (ht b).2 k (.inl (by simpa [Ghost.atExt, ECell.share] using hq))

/-- **The authority gives the block's extent.** -/
theorem Holds.bauth {m : Mem} {r rF : Res} {R : FAssn} (hh : Holds m r rF) (h : (bauth b S K q ⋆ R) r) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ blk.bytes.size = S ∧ blk.kind = K ∧
      K.mappedLo < S := by
  obtain ⟨r₁, h1, ht⟩ := hh.claims h
  rw [bauth_eq h1] at ht
  exact (ht b).1 S K (by simp [Ghost.atExt, ECell.auth1])

end Rules

/-! ## Epoch-tagged shares (`docs/sep-full-state.md` §Epoch-tagged shares)

A share tagged `(γ, e)` (`bshare b q k (some (γ, e))`) counts and is true only while ledger `γ` is
at epoch `e`. It is lent off an untagged share together with a receipt (`EUpd.lendT`); given back
during its epoch it cancels its receipt (`EUpd.returnT`); once the ledger is past `e`, the
receipt alone turns back into an untagged share (`EUpd.revoke`), whatever the holder of the tagged
share kept. Every rule needs the ledger's authority. -/

@[simp] theorem Frac.zero_val : Frac.zero.val = 0 := rfl

namespace ECell

@[simp] theorem tshare_sh (γ e : Nat) (q : Frac) (k j : Nat) : (tshare γ e q k).sh j = Frac.zero := rfl
@[simp] theorem tshare_rc (γ e : Nat) (q : Frac) (k γ' e' j : Nat) : (tshare γ e q k).rc γ' e' j = Frac.zero := rfl
@[simp] theorem tshare_auth (γ e : Nat) (q : Frac) (k : Nat) (x) : (tshare γ e q k).auth x = 0 := rfl
@[simp] theorem rcpt_sh (γ e : Nat) (q : Frac) (k j : Nat) : (rcpt γ e q k).sh j = Frac.zero := rfl
@[simp] theorem rcpt_tsh (γ e : Nat) (q : Frac) (k γ' e' j : Nat) : (rcpt γ e q k).tsh γ' e' j = Frac.zero := rfl
@[simp] theorem rcpt_auth (γ e : Nat) (q : Frac) (k : Nat) (x) : (rcpt γ e q k).auth x = 0 := rfl
@[simp] theorem share_tsh (q : Frac) (k γ e j : Nat) : (share q k).tsh γ e j = Frac.zero := rfl
@[simp] theorem share_rc (q : Frac) (k γ e j : Nat) : (share q k).rc γ e j = Frac.zero := rfl
@[simp] theorem share_auth (q : Frac) (k : Nat) (x) : (share q k).auth x = 0 := rfl

theorem ftot_zero' (n : Nat) : ftot (fun _ => Frac.zero) n = 0 := ftot_zero (fun _ => rfl) n

@[simp] theorem ftot_share_tsh (q : Frac) (k γ e n : Nat) : ftot ((share q k).tsh γ e) n = 0 :=
  ftot_zero (fun _ => rfl) n
@[simp] theorem ftot_share_rc (q : Frac) (k γ e n : Nat) : ftot ((share q k).rc γ e) n = 0 :=
  ftot_zero (fun _ => rfl) n
@[simp] theorem ftot_tshare_rc (γ e : Nat) (q : Frac) (k γ' e' n : Nat) :
    ftot ((tshare γ e q k).rc γ' e') n = 0 := ftot_zero (fun _ => rfl) n
@[simp] theorem ftot_rcpt_tsh (γ e : Nat) (q : Frac) (k γ' e' n : Nat) :
    ftot ((rcpt γ e q k).tsh γ' e') n = 0 := ftot_zero (fun _ => rfl) n

theorem ftot_tshare (γ e : Nat) (q : Frac) (k γ' e' n : Nat) :
    ftot ((tshare γ e q k).tsh γ' e') n = if γ' = γ ∧ e' = e ∧ k < n then q.val else 0 := by
  rw [ftot_single (k := k) (fun j hj => by rw [tshare_tsh]; simp [hj]), tshare_tsh]
  by_cases h : γ' = γ ∧ e' = e
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg (fun (x : γ' = γ ∧ e' = e ∧ k = k) => h ⟨x.1, x.2.1⟩),
      if_neg (fun (x : γ' = γ ∧ e' = e ∧ k < n) => h ⟨x.1, x.2.1⟩)]
    split <;> rfl

theorem ftot_rcpt (γ e : Nat) (q : Frac) (k γ' e' n : Nat) :
    ftot ((rcpt γ e q k).rc γ' e') n = if γ' = γ ∧ e' = e ∧ k < n then q.val else 0 := by
  rw [ftot_single (k := k) (fun j hj => by rw [rcpt_rc]; simp [hj]), rcpt_rc]
  by_cases h : γ' = γ ∧ e' = e
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg (fun (x : γ' = γ ∧ e' = e ∧ k = k) => h ⟨x.1, x.2.1⟩),
      if_neg (fun (x : γ' = γ ∧ e' = e ∧ k < n) => h ⟨x.1, x.2.1⟩)]
    split <;> rfl

theorem total_tags (γ e : Nat) (q q' : Frac) (k k' n : Nat) :
    ((tshare γ e q k').add (rcpt γ e q' k)).total n = 0 := by
  rw [total_eq, ftot_zero (fun j => by simp [add])]

theorem total_rcpt (γ e : Nat) (q : Frac) (k n : Nat) : (rcpt γ e q k).total n = 0 := by
  rw [total_eq, ftot_zero (fun j => rfl)]

end ECell

section Tags

variable {b : BlockId} {k k' : Nat} {q : Frac} {γ e : Nat} {M : GMap}

/-- `gauth γ e M ⋆ P`, where `P` holds the claims `c` on block `b` only, as one resource. -/
theorem gauth_ext_eq {P : FAssn} {c : ECell} (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, Ghost.atExt b c⟩)
    {r : Res} (h : (gauth γ e M ⋆ P) r) :
    r = ⟨FHeap.empty, Know.none, (Ghost.at γ (GCell.auth1 e M)).add (Ghost.atExt b c)⟩ := by
  obtain ⟨r₁, r₂, -, rfl, ⟨h1, k1, g1⟩, h2⟩ := h
  rw [hp _ h2, h1, k1, g1]; simp [FHeap.union_empty, Know.union_none]

theorem gauth_ext_intro {P : FAssn} {c : ECell} (hp : P ⟨FHeap.empty, Know.none, Ghost.atExt b c⟩) :
    (gauth γ e M ⋆ P) ⟨FHeap.empty, Know.none, (Ghost.at γ (GCell.auth1 e M)).add (Ghost.atExt b c)⟩ :=
  ⟨⟨FHeap.empty, Know.none, Ghost.at γ (GCell.auth1 e M)⟩, ⟨FHeap.empty, Know.none, Ghost.atExt b c⟩,
    FHeap.disjoint_empty _, by simp [FHeap.union_empty, Know.union_none], ⟨rfl, rfl, rfl⟩, hp⟩

theorem Ghost.at_extent (γ : Nat) (c : GCell) (x : BlockId) : (Ghost.at γ c).extent x = ECell.unit := rfl

theorem Ghost.at_auth1_ep : (Ghost.at γ (GCell.auth1 e M)).ep γ e :=
  ⟨M, by simp [Ghost.at, GCell.auth1]⟩

/-- **Lend a tagged share** off an untagged one: the holder gets a share tagged `(γ, e)` (at a
bound up to the old one), the lender a receipt for it. Needs ledger `γ` at epoch `e`. -/
theorem EUpd.lendT (hk : k' ≤ k) :
    EUpd (gauth γ e M ⋆ bshare b q k)
      (gauth γ e M ⋆ (bshare b q k' (some (γ, e)) ⋆ brcpt b q k γ e)) := by
  refine EUpd.ext1L (L := Ghost.at γ (GCell.auth1 e M)) (Ghost.at_extent _ _) (b := b) (c := ECell.share q k)
    (c' := (ECell.tshare γ e q k').add (ECell.rcpt γ e q k)) fun r h => ?_
  have hq : 0 < q.val := by obtain ⟨_, _, _, _, _, h2⟩ := h; exact h2.1
  refine ⟨gauth_ext_eq (fun _ h => bshare_eq h) h,
    gauth_ext_intro (ext_sep_intro ⟨hq, rfl, rfl, rfl⟩ ⟨hq, rfl, rfl, rfl⟩), fun ep hL huniq => ?_⟩
  have hep : ep γ e := hL _ _ Ghost.at_auth1_ep
  refine ⟨by funext x; simp [ECell.add], fun d n N E => ⟨Max.max n (k + 1), N, E, ?_⟩,
    fun j hj => ?_, fun γ' e₀ e'' he hlt _ j => ?_, fun γ' hn _ e' j => ?_⟩
  · refine Rat.le_trans (ECell.wsum_mono ep _ (Nat.le_max_left n (k + 1)) (Nat.le_refl N) (Nat.le_refl E)) ?_
    have hg := ECell.gsum_tag_le (ep := ep) (d := d) (c := ECell.share q k)
      (c' := (ECell.tshare γ e q k').add (ECell.rcpt γ e q k)) (γ := γ) (e := e)
      (n := Max.max n (k + 1)) (δ := q.val) (Rat.le_of_lt hq)
      (fun γ' e' j hne => by
        have : ¬ (γ' = γ ∧ e' = e ∧ j = k') := fun x => hne (by rw [x.1, x.2.1])
        have : ¬ (γ' = γ ∧ e' = e ∧ j = k) := fun x => hne (by rw [x.1, x.2.1])
        simp [ECell.add, ECell.tshare_tsh, ECell.rcpt_rc, *])
      (by
        show ftot (fun j => ((ECell.tshare γ e q k').tsh γ e j).add ((ECell.rcpt γ e q k).tsh γ e j)) _ ≤ _
        rw [ftot_add, ECell.ftot_tshare]
        simp only [ECell.ftot_rcpt_tsh, ECell.ftot_share_tsh]; split <;> grind [Frac.nonneg])
      (by
        show ftot (fun j => ((ECell.tshare γ e q k').rc γ e j).add ((ECell.rcpt γ e q k).rc γ e j)) _ ≤ _
        rw [ftot_add, ECell.ftot_rcpt]
        simp only [ECell.ftot_tshare_rc, ECell.ftot_share_rc]; split <;> grind [Frac.nonneg]) N E
    have ht := ECell.total_share q k (Max.max n (k + 1))
    rw [if_pos (by omega)] at ht
    simp only [ECell.wsum]
    rw [ECell.total_add ((ECell.tshare γ e q k').add (ECell.rcpt γ e q k)) d, ECell.total_add (ECell.share q k) d,
      ECell.total_tags, ht]
    grind
  · left
    refine ⟨k, ?_, .inl (by simp [ECell.share, hq])⟩
    rcases hj with hj | ⟨γ', e', ⟨-, hp⟩ | ⟨-, hp⟩⟩
    · simp [ECell.add] at hj
    · simp only [ECell.add, Frac.add_val, ECell.tshare_tsh, ECell.rcpt_tsh, Frac.zero_val] at hp
      split at hp
      · omega
      · grind
    · simp only [ECell.add, Frac.add_val, ECell.rcpt_rc, ECell.tshare_rc, Frac.zero_val] at hp
      split at hp
      · omega
      · grind
  · have : ¬ (γ' = γ ∧ e'' = e ∧ j = k') := fun x => by
      rw [x.1] at he; have := huniq _ _ _ he hep; omega
    have : ¬ (γ' = γ ∧ e'' = e ∧ j = k) := fun x => by
      rw [x.1] at he; have := huniq _ _ _ he hep; omega
    simp [ECell.add, ECell.tshare_tsh, ECell.rcpt_rc, *]
  · have : γ' ≠ γ := fun x => hn e (x ▸ hep)
    simp [ECell.add, ECell.tshare_tsh, ECell.rcpt_rc, this]

/-- **Give a tagged share back** during its epoch: it cancels its receipt, and the receipt's
holder gets the untagged share back at the receipt's bound. -/
theorem EUpd.returnT (hk : k' ≤ k) :
    EUpd (gauth γ e M ⋆ (bshare b q k' (some (γ, e)) ⋆ brcpt b q k γ e))
      (gauth γ e M ⋆ bshare b q k) := by
  refine EUpd.ext1L (L := Ghost.at γ (GCell.auth1 e M)) (Ghost.at_extent _ _) (b := b)
    (c := (ECell.tshare γ e q k').add (ECell.rcpt γ e q k)) (c' := ECell.share q k) fun r h => ?_
  have hq : 0 < q.val := by obtain ⟨_, _, _, _, _, _, _, _, _, h2, _⟩ := h; exact h2.1
  refine ⟨gauth_ext_eq (fun _ h => ext_sep_eq (fun _ h => bshareT_eq h) (fun _ h => brcpt_eq h) h) h,
    gauth_ext_intro ⟨hq, rfl, rfl, rfl⟩, fun ep hL huniq => ?_⟩
  have hep : ep γ e := hL _ _ Ghost.at_auth1_ep
  refine ⟨by funext x; simp [ECell.add], fun d n N E => ⟨n, Max.max N (γ + 1), Max.max E (e + 1), ?_⟩,
    fun j hj => ?_, fun _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ => by simp⟩
  · refine Rat.le_trans (ECell.wsum_mono ep _ (Nat.le_refl n) (Nat.le_max_left N (γ + 1))
      (Nat.le_max_left E (e + 1))) ?_
    have hg := ECell.gsum_tag_ge (ep := ep) (d := d) (c := (ECell.tshare γ e q k').add (ECell.rcpt γ e q k))
      (c' := ECell.share q k) (γ := γ) (e := e) (n := n) (δ := if k < n then q.val else 0)
      (fun γ' e' j hne => by
        have : ¬ (γ' = γ ∧ e' = e ∧ j = k') := fun x => hne (by rw [x.1, x.2.1])
        have : ¬ (γ' = γ ∧ e' = e ∧ j = k) := fun x => hne (by rw [x.1, x.2.1])
        simp [ECell.add, ECell.tshare_tsh, ECell.rcpt_rc, *])
      (.inl hep)
      (fun _ => by
        show _ ≤ ftot (fun j => ((ECell.tshare γ e q k').tsh γ e j).add ((ECell.rcpt γ e q k).tsh γ e j)) _
        rw [ftot_add, ECell.ftot_tshare]
        simp only [ECell.ftot_rcpt_tsh, ECell.ftot_share_tsh]
        split <;> split <;> simp_all <;> grind [Frac.nonneg])
      (by
        show _ ≤ ftot (fun j => ((ECell.tshare γ e q k').rc γ e j).add ((ECell.rcpt γ e q k).rc γ e j)) _
        rw [ftot_add, ECell.ftot_rcpt]
        simp only [ECell.ftot_tshare_rc, ECell.ftot_share_rc]
        split <;> simp_all <;> grind)
      (Max.max N (γ + 1)) (Max.max E (e + 1)) (by omega) (by omega)
    simp only [ECell.wsum]
    rw [ECell.total_add ((ECell.tshare γ e q k').add (ECell.rcpt γ e q k)) d, ECell.total_add (ECell.share q k) d,
      ECell.total_tags, ECell.total_share]
    grind
  · rcases hj with hj | ⟨_, _, ⟨-, hp⟩ | ⟨-, hp⟩⟩
    · have : j = k := by simp only [ECell.share] at hj; split at hj <;> simp_all
      subst this
      exact .inl ⟨j, Nat.le_refl _, .inr ⟨γ, e, .inr ⟨.inl hep, by simp [ECell.add, ECell.rcpt_rc, hq]⟩⟩⟩
    · simp at hp
    · simp at hp

/-- **Revoke a past epoch's share**: once ledger `γ` is past epoch `e`, a receipt of epoch `e`
turns back into an untagged share, whatever the holder of the tagged share kept (it is dormant). -/
theorem EUpd.revoke {e' : Nat} (he : e < e') :
    EUpd (gauth γ e' M ⋆ brcpt b q k γ e) (gauth γ e' M ⋆ bshare b q k) := by
  refine EUpd.ext1L (L := Ghost.at γ (GCell.auth1 e' M)) (Ghost.at_extent _ _) (b := b)
    (c := ECell.rcpt γ e q k) (c' := ECell.share q k) fun r h => ?_
  have hq : 0 < q.val := by obtain ⟨_, _, _, _, _, h2⟩ := h; exact h2.1
  refine ⟨gauth_ext_eq (fun _ h => brcpt_eq h) h, gauth_ext_intro ⟨hq, rfl, rfl, rfl⟩,
    fun ep hL huniq => ?_⟩
  have hep : ep γ e' := hL _ _ Ghost.at_auth1_ep
  have hne : ¬ ep γ e := fun h => by have := huniq _ _ _ h hep; omega
  refine ⟨by funext x; simp, fun d n N E => ⟨n, Max.max N (γ + 1), Max.max E (e + 1), ?_⟩,
    fun j hj => ?_, fun _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ => by simp⟩
  · refine Rat.le_trans (ECell.wsum_mono ep _ (Nat.le_refl n) (Nat.le_max_left N (γ + 1))
      (Nat.le_max_left E (e + 1))) ?_
    have hg := ECell.gsum_tag_ge (ep := ep) (d := d) (c := ECell.rcpt γ e q k)
      (c' := ECell.share q k) (γ := γ) (e := e) (n := n) (δ := if k < n then q.val else 0)
      (fun γ' e₀ j hne => by
        have : ¬ (γ' = γ ∧ e₀ = e ∧ j = k) := fun x => hne (by rw [x.1, x.2.1])
        simp [ECell.rcpt_rc, *])
      (.inr ⟨e', he, hep⟩) (fun h => absurd h hne)
      (by
        rw [ECell.ftot_rcpt]; simp only [ECell.ftot_share_rc]
        split <;> simp_all <;> grind)
      (Max.max N (γ + 1)) (Max.max E (e + 1)) (by omega) (by omega)
    simp only [ECell.wsum]
    rw [ECell.total_add (ECell.rcpt γ e q k) d, ECell.total_add (ECell.share q k) d,
      ECell.total_rcpt, ECell.total_share]
    grind
  · rcases hj with hj | ⟨_, _, ⟨-, hp⟩ | ⟨-, hp⟩⟩
    · have : j = k := by simp only [ECell.share] at hj; split at hj <;> simp_all
      subst this
      exact .inl ⟨j, Nat.le_refl _, .inr ⟨γ, e, .inr ⟨.inr ⟨e', he, hep⟩, by simp [ECell.rcpt_rc, hq]⟩⟩⟩
    · simp at hp
    · simp at hp

/-- **A held tagged share of the current epoch gives a live block** of at least `k` bytes. -/
theorem Holds.bshareT {m : Mem} {r rF : Res} {R : FAssn} (hh : Holds m r rF)
    (h : ((gauth γ e M ⋆ Zig.Full.bshare b q k (some (γ, e))) ⋆ R) r) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ k ≤ blk.bytes.size ∧
      blk.kind.mappedLo < blk.bytes.size := by
  obtain ⟨r₁, h1, ht⟩ := hh.claims h
  have hq : 0 < q.val := by obtain ⟨_, _, _, _, _, h2⟩ := h1; exact h2.1
  rw [gauth_ext_eq (fun _ h => bshareT_eq h) h1] at ht
  refine (ht b).2 k (.inr ⟨γ, e, .inl ⟨Ghost.ep_add Ghost.at_auth1_ep, ?_⟩⟩)
  simp [Ghost.add, Ghost.at, Ghost.atExt, ECell.tshare_tsh, hq]

end Tags

/-! ## Triple rules -/

namespace FTriple

variable {α : Type} {P P' : FAssn} {c : MemM α} {Q Q' : α → FAssn}

/-- An update of the precondition. -/
theorem eupd (hu : EUpd P P') (ht : FTriple P' c Q) : FTriple P c Q := fun m r rF hh hp hs => by
  obtain ⟨r', hh', hp'⟩ := hu m r rF hh hp hs
  exact ht m r' rF hh' hp' hs

/-- An update of the postcondition. -/
theorem eupd_post (ht : FTriple P c Q) (hu : ∀ v, EUpd (Q v) (Q' v)) : FTriple P c Q' := by
  intro m r rF hh hp hs
  have := ht m r rF hh hp hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', hh', hq, hs'⟩ := this
    obtain ⟨r'', hh'', hq'⟩ := hu _ _ r' rF hh' hq hs'
    exact ⟨r'', hh'', hq', hs'⟩

end FTriple

namespace FTotalTriple

variable {α : Type} {P P' : FAssn} {c : MemM α} {Q Q' : α → FAssn}

theorem eupd (hu : EUpd P P') (ht : FTotalTriple P' c Q) : FTotalTriple P c Q :=
  ⟨FTriple.eupd hu ht.1, fun m r rF hh hp hs => by
    obtain ⟨r', hh', hp'⟩ := hu m r rF hh hp hs
    exact ht.2 m r' rF hh' hp' hs⟩

theorem eupd_post (ht : FTotalTriple P c Q) (hu : ∀ v, EUpd (Q v) (Q' v)) : FTotalTriple P c Q' :=
  ⟨FTriple.eupd_post ht.1 hu, ht.2⟩

end FTotalTriple

namespace CTriple

variable {Tgt α : Type} {P P' : FAssn} {x : ConcM Tgt α} {Q Q' : α → FAssn}

theorem eupd (hu : EUpd P P') (ht : CTriple P' x Q) : CTriple P x Q := fun n => FTriple.eupd hu (ht n)

theorem eupd_post (ht : CTriple P x Q) (hu : ∀ v, EUpd (Q v) (Q' v)) : CTriple P x Q' :=
  fun n => FTriple.eupd_post (ht n) hu

end CTriple

end Full
end Zig
