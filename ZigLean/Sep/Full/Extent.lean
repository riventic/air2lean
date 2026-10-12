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
| `EUpd.lendT` | `gauthP γ e M p ⋆ bshare b q k p` | `gauthP γ e M p ⋆ (bshare b q k' (some (γ, e)) ⋆ brcpt b q k γ e)` | `k' ≤ k` |
| `EUpd.returnT` | `gauthP γ e M p ⋆ (bshare b q k' (some (γ, e)) ⋆ brcpt b q k γ e)` | `gauthP γ e M p ⋆ bshare b q k p` | `k' ≤ k` |
| `EUpd.revoke` | `gauthP γ e' M p ⋆ brcpt b q k γ e` | `gauthP γ e' M p ⋆ bshare b q k p` | `e < e'` |

`bshare_split`, `EUpd.join` and `EUpd.weaken` hold for shares of any tag `t`.

The tagged rules (`docs/sep-full-state.md` §Epoch-tagged shares, §Nested tags) are instances of
`EUpd.ext1L` (`ECell.StepE`: a step under every ledger status that contains the resource's ledger;
`ECell.BalAt.change` moves fractions between the worlds of the tag tree). Split, join and weaken are
instances of `EUpd.ext1T` (`ECell.StepT`: a step of one tag's shares), the untagged ones of `EUpd.ext1`
(`ECell.Step`): a change of the claims `c` on block `b` to `c'` that keeps
the authority claims, does not raise the fraction held below any bound beyond what `c` holds below
some bound (`ECell.total`), and whose every share is covered by a share of `c` at a bound at
least as high or by an authority claim of `c` of a size at least as high. `join` takes the higher
bound because the share at that bound already certifies it: this is what lets an allocator take a
grant's share back into its own share at the buffer's or node's bound.

Facts: `Holds.bshare` (a held share of an active tag gives a live block of at least `k` bytes), `Holds.bauth` (the
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

/-- What is left of `q` after its part `q'`. -/
def diff (q q' : Frac) (h : q'.val ≤ q.val) : Frac := ⟨q.val - q'.val, by grind⟩

theorem add_diff {q q' : Frac} (h : q'.val ≤ q.val) : q'.add (q.diff q' h) = q :=
  eq (by simp only [add, diff]; grind)

theorem diff_pos {q q' : Frac} (h : q'.val < q.val) : 0 < (q.diff q' (Rat.le_of_lt h)).val := by
  simp only [diff]; grind

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

/-- **A local step of one block's claims under the ledger statuses `ls`**: the authority claims
stay; against every frame `d`, budgets that balance `c` with `d` below some bound give budgets that
balance `c'` with `d`; every live claim of `c'` is covered by a live claim of `c` at a bound at
least as high or by an authority claim of `c`; `c'` has no claim of a future tag if `c` has none;
and `c'` puts no tag on a ledger name that neither exists, nor is a parent, nor was tagged by
`c`. -/
def StepE (ls : LStat) (c c' : ECell) : Prop :=
  c'.auth = c.auth ∧
    (∀ d n N E, ∃ n' N' E', (c.add d).Bal ls n' N' E' → (c'.add d).Bal ls n N E) ∧
    (∀ j, c'.Req ls j → (∃ j', j ≤ j' ∧ c.Req ls j') ∨ ∃ S K, 0 < c.auth (S, K) ∧ j ≤ S) ∧
    (c.FutZ ls → c'.FutZ ls) ∧
    (∀ γ, (∀ e p, ¬ ls γ e p) → (∀ γ' e' e, ¬ ls γ' e' (some (γ, e))) →
      (∀ e k, (c.tsh γ e k).val = 0 ∧ (c.rc γ e k).val = 0) →
      ∀ e k, (c'.tsh γ e k).val = 0 ∧ (c'.rc γ e k).val = 0)

theorem add_tags_zero {a b : ECell} {γ e k : Nat}
    (h : ((a.add b).tsh γ e k).val = 0 ∧ ((a.add b).rc γ e k).val = 0) :
    (a.tsh γ e k).val = 0 ∧ (a.rc γ e k).val = 0 ∧ (b.tsh γ e k).val = 0 ∧ (b.rc γ e k).val = 0 := by
  simp only [add, Frac.add_val] at h
  have := (a.tsh γ e k).nonneg; have := (b.tsh γ e k).nonneg
  have := (a.rc γ e k).nonneg; have := (b.rc γ e k).nonneg
  grind

/-- A step keeps every frame `d` that `c` composed with, validly and truly in `m`. -/
theorem StepE.ok {ls : LStat} {m : Mem} {b : BlockId} {c c' d : ECell}
    (hst : StepE ls c c') (hv : (c.add d).Valid) (hto : (c.add d).TagOk ls)
    (ht : (c.add d).TrueIn ls m b) :
    (c'.add d).Valid ∧ (c'.add d).TagOk ls ∧ (c'.add d).TrueIn ls m b := by
  obtain ⟨hauth, hw, hsh, hfut, -⟩ := hst
  obtain ⟨h1, h2, -⟩ := hv
  obtain ⟨ta, ts⟩ := ht
  have ea : (c'.add d).auth = (c.add d).auth := by simp only [add, hauth]
  have hb : ∀ n N E, (c'.add d).Bal ls n N E := fun n N E => by
    obtain ⟨n', N', E', h⟩ := hw d n N E
    exact h (hto.1 n' N' E')
  refine ⟨⟨fun x => by rw [ea]; exact h1 x, fun x y hx hy => h2 x y (by rw [← ea]; exact hx)
    (by rw [← ea]; exact hy), fun n => ?_⟩, ⟨hb, (hfut hto.2.of_add).add ?_⟩,
    fun S K hp => ta S K (by rw [← ea]; exact hp), fun j hp => ?_⟩
  · obtain ⟨β, h, -⟩ := hb n 0 0
    simp only [mass, gsum, tg_none] at h
    rw [total_eq]; grind
  · exact (by rw [add_comm] at hto; exact hto.2.of_add)
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

/-- **A local step of the shares of one tag `t`** (the untagged ones for `t = none`): the
authority claims, the other tags' shares and the receipts stay; the fraction of `t` below every
bound is at most what `c` held below some bound; every share of `t` in `c'` is covered by one of
`c` at a bound at least as high or by an authority claim of `c`. -/
def StepT (t : STag) (c c' : ECell) : Prop :=
  c'.auth = c.auth ∧ (∀ n, ∃ N, n ≤ N ∧ ftot (c'.tg t) n ≤ ftot (c.tg t) N) ∧
    (∀ j, 0 < (c'.tg t j).val → (∃ j', j ≤ j' ∧ 0 < (c.tg t j').val) ∨
      ∃ S K, 0 < c.auth (S, K) ∧ j ≤ S) ∧
    (∀ u j, u ≠ t → (c'.tg u j).val = (c.tg u j).val) ∧ ∀ γ e j, (c'.rc γ e j).val = (c.rc γ e j).val

theorem Step.toT {c c' : ECell} (h : Step c c') : StepT none c c' := by
  obtain ⟨hauth, htot, hsh, htag⟩ := h
  refine ⟨hauth, fun n => ?_, hsh, fun u j hu => ?_, fun γ e j => (htag γ e j).2⟩
  · obtain ⟨N, h1, h2⟩ := htot n
    exact ⟨N, h1, by show ftot c'.sh n ≤ ftot c.sh N; rw [← total_eq, ← total_eq]; exact h2⟩
  · rcases u with _ | ⟨γ, e⟩
    · exact absurd rfl hu
    · exact (htag γ e j).1

theorem tg_add_val (a b : ECell) (t : STag) (k : Nat) :
    ((a.add b).tg t k).val = (a.tg t k).val + (b.tg t k).val := by rw [tg_add]; rfl

theorem rc_add_val (a b : ECell) (γ e k : Nat) :
    ((a.add b).rc γ e k).val = (a.rc γ e k).val + (b.rc γ e k).val := rfl

theorem ftot_tg_add (a b : ECell) (t : STag) (n : Nat) :
    ftot ((a.add b).tg t) n = ftot (a.tg t) n + ftot (b.tg t) n := by
  rw [← ftot_add]; exact ftot_congr (fun k => by rw [tg_add]) n

theorem ftot_rc_add (a b : ECell) (γ e n : Nat) :
    ftot ((a.add b).rc γ e) n = ftot (a.rc γ e) n + ftot (b.rc γ e) n := by
  rw [← ftot_add]; rfl

theorem tg_zero_of_ftot {f g : Nat → Frac} {j N : Nat} (h : ftot f (j + 1) ≤ ftot g N)
    (hg : ∀ k, (g k).val = 0) : (f j).val = 0 := by
  have := le_ftot f (k := j) (n := j + 1) (by omega)
  rw [ftot_zero hg] at h
  have := (f j).nonneg; grind

/-- A step of one tag's shares is a step under every ledger status. -/
theorem StepT.toE {t : STag} {c c' : ECell} (h : StepT t c c') (ls : LStat) : StepE ls c c' := by
  obtain ⟨hauth, htot, hsh, hoth, hrc⟩ := h
  refine ⟨hauth, fun d n N E => ?_, fun j hj => ?_, fun hf γ e k hfu => ?_, fun γ _ _ hz e k => ?_⟩
  · obtain ⟨n', hnn, hle⟩ := htot n
    refine ⟨n', N, E, fun ⟨β, hb⟩ => ⟨β, ?_⟩⟩
    have hm : ∀ w, (c'.add d).mass ls β w n N E ≤ (c.add d).mass ls β w n' N E := fun w => by
      have h1 : ftot ((c'.add d).tg w) n ≤ ftot ((c.add d).tg w) n' := by
        rw [ftot_tg_add, ftot_tg_add]
        have := ftot_mono (d.tg w) hnn
        by_cases hw : w = t
        · subst hw; grind
        · rw [ftot_congr (fun k => hoth w k hw) n]; have := ftot_mono (c.tg w) hnn; grind
      have h2 := gsum_le (f := fun γ e => cwt ls w β γ e ((c'.add d).rc γ e) n)
        (g := fun γ e => cwt ls w β γ e ((c.add d).rc γ e) n') (fun γ e => by
          rw [cwt_congr (β := β) (R := (c.add d).rc γ e) (R' := (c'.add d).rc γ e) rfl (fun k => by
            show (c'.rc γ e k).val + (d.rc γ e k).val = (c.rc γ e k).val + (d.rc γ e k).val
            rw [hrc]) n]
          exact cwt_mono _ _ _ _ _ _ hnn) N E
      simp only [mass]; grind
    exact ⟨Rat.le_trans (hm none) hb.1, fun γ e hγ he ha => Rat.le_trans (hm _) (hb.2 γ e hγ he ha)⟩
  · rcases hj with ⟨u, hu, hp⟩ | ⟨γ, e, hl, hp⟩
    · by_cases hut : u = t
      · subst hut
        rcases hsh j hp with ⟨j', h1, h2⟩ | h
        · exact .inl ⟨j', h1, .inl ⟨u, hu, h2⟩⟩
        · exact .inr h
      · exact .inl ⟨j, Nat.le_refl _, .inl ⟨u, hu, by rw [← hoth u j hut]; exact hp⟩⟩
    · exact .inl ⟨j, Nat.le_refl _, .inr ⟨γ, e, hl, by rw [← hrc]; exact hp⟩⟩
  · refine ⟨?_, by rw [hrc]; exact (hf γ e k hfu).2⟩
    by_cases hut : some (γ, e) = t
    · subst hut
      obtain ⟨N', h1, h2⟩ := htot (k + 1)
      exact tg_zero_of_ftot (f := c'.tg (some (γ, e))) h2 (fun j => (hf γ e j hfu).1)
    · have := hoth (some (γ, e)) k hut; simp only [tg_some] at this; rw [this]; exact (hf γ e k hfu).1
  · refine ⟨?_, by rw [hrc]; exact (hz e k).2⟩
    by_cases hut : some (γ, e) = t
    · subst hut
      obtain ⟨N', h1, h2⟩ := htot (k + 1)
      exact tg_zero_of_ftot (f := c'.tg (some (γ, e))) h2 (fun j => (hz e j).1)
    · have := hoth (some (γ, e)) k hut; simp only [tg_some] at this; rw [this]; exact (hz e k).1

theorem Step.toE {c c' : ECell} (h : Step c c') (ls : LStat) : StepE ls c c' := h.toT.toE ls

end ECell

/-! ### Changes at one tag -/

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

/-- A change at one place `(γ₀, e₀)` in range, by `δ` of any sign. -/
theorem gsum_single_in {f g : Nat → Nat → Rat} {γ₀ e₀ : Nat} {δ : Rat}
    (h : ∀ γ e, (γ, e) ≠ (γ₀, e₀) → f γ e ≤ g γ e) (h₀ : f γ₀ e₀ ≤ g γ₀ e₀ + δ) :
    ∀ N E, γ₀ < N → e₀ < E → gsum f N E ≤ gsum g N E + δ := by
  intro N E hN hE
  have := gsum_single_ge (δ := -δ) h (by grind) N E hN hE
  grind

open Classical in
/-- **The weight of a child tag** whose receipts change by `δ` (and whose budget changes by `δ`
while it is current) changes by `δ` where it is live. -/
theorem cwt_shift {ls : LStat} {w : STag} {β β' : Nat → Nat → Rat} {γ e : Nat} {R R' : Nat → Frac}
    {n : Nat} {δ : Rat} (hR : ftot R' n = ftot R n + δ) (hβ : ls γ e w → β' γ e = β γ e + δ) :
    cwt ls w β' γ e R' n ≤ cwt ls w β γ e R n + (if ∃ e', e ≤ e' ∧ ls γ e' w then δ else 0) := by
  unfold cwt
  by_cases h1 : ls γ e w
  · rw [if_pos h1, if_pos h1, if_pos ⟨e, Nat.le_refl _, h1⟩, hR, hβ h1]; grind
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : ∃ e', e < e' ∧ ls γ e' w
    · obtain ⟨e', he, h2'⟩ := h2
      rw [if_pos ⟨e', he, h2'⟩, if_pos ⟨e', he, h2'⟩, if_pos ⟨e', Nat.le_of_lt he, h2'⟩, hR]; grind
    · rw [if_neg h2, if_neg h2, if_neg (fun ⟨e', he, h3⟩ => by
        rcases Nat.lt_or_ge e e' with h | h
        · exact h2 ⟨e', h, h3⟩
        · exact h1 (by rw [show e = e' by omega]; exact h3))]
      grind

namespace ECell

/-- **The fraction of world `w`** after `c` becomes `c'` next to `d`, where only the receipts of
`(γ, e)` and the budget of `(γ, e)` may change (`(γ, e)` in range): it changes by what the shares of
`w` change, plus what the weight of `(γ, e)` changes. -/
theorem mass_change {ls : LStat} {c c' d : ECell} {β β' : Nat → Nat → Rat} {γ e : Nat} {w : STag}
    {n N E : Nat} {A B : Rat} (hN : γ < N) (hE : e < E)
    (hT : ftot (c'.tg w) n ≤ ftot (c.tg w) n + A)
    (hrc : ∀ γ' e' j, (γ', e') ≠ (γ, e) → (c'.rc γ' e' j).val = (c.rc γ' e' j).val)
    (hβ : ∀ γ' e', (γ', e') ≠ (γ, e) → β' γ' e' = β γ' e')
    (h0 : cwt ls w β' γ e ((c'.add d).rc γ e) n ≤ cwt ls w β γ e ((c.add d).rc γ e) n + B) :
    (c'.add d).mass ls β' w n N E ≤ (c.add d).mass ls β w n N E + (A + B) := by
  have hg := gsum_single_in (f := fun γ e => cwt ls w β' γ e ((c'.add d).rc γ e) n)
    (g := fun γ e => cwt ls w β γ e ((c.add d).rc γ e) n) (γ₀ := γ) (e₀ := e) (δ := B)
    (fun γ' e' hne => by
      rw [cwt_congr (β := β) (R := (c.add d).rc γ' e') (R' := (c'.add d).rc γ' e') (hβ γ' e' hne) (fun k => by
        show (c'.rc γ' e' k).val + (d.rc γ' e' k).val = (c.rc γ' e' k).val + (d.rc γ' e' k).val
        rw [hrc γ' e' k hne]) n]
      exact Rat.le_refl) h0 N E hN hE
  simp only [mass, ftot_tg_add]; grind

@[simp] theorem rcpt_tg (γ e : Nat) (q : Frac) (k : Nat) (w : STag) (j : Nat) :
    (rcpt γ e q k).tg w j = Frac.zero := by rcases w with _ | ⟨_, _⟩ <;> rfl

@[simp] theorem shareT_rc (u : STag) (q : Frac) (k γ e j : Nat) : (shareT u q k).rc γ e j = Frac.zero := by
  rcases u with _ | ⟨_, _⟩ <;> rfl

@[simp] theorem shareT_auth (u : STag) (q : Frac) (k : Nat) (x) : (shareT u q k).auth x = 0 := by
  rcases u with _ | ⟨_, _⟩ <;> rfl

theorem tg_shareT (u : STag) (q : Frac) (k : Nat) (w : STag) (j : Nat) :
    ((shareT u q k).tg w j).val = if w = u ∧ j = k then q.val else 0 := by
  rcases u with _ | ⟨γ, e⟩ <;> rcases w with _ | ⟨γ', e'⟩ <;>
    simp only [shareT, tg, share, tshare, reduceCtorEq, false_and, if_false, Option.some.injEq,
      Prod.mk.injEq, true_and] <;> (try split) <;> (try split) <;> simp_all [Frac.zero]

theorem ftot_tg_shareT (u : STag) (q : Frac) (k : Nat) (w : STag) (n : Nat) :
    ftot ((shareT u q k).tg w) n = if w = u ∧ k < n then q.val else 0 := by
  rw [ftot_single (k := k) (fun j hj => by rw [tg_shareT]; simp [hj]), tg_shareT]
  by_cases h : w = u <;> simp [h]

theorem tshare_tsh (γ e : Nat) (q : Frac) (k γ' e' j : Nat) :
    ((tshare γ e q k).tsh γ' e' j).val = if γ' = γ ∧ e' = e ∧ j = k then q.val else 0 := by
  simp only [tshare]; split <;> rfl

theorem rcpt_rc_val (γ e : Nat) (q : Frac) (k γ' e' j : Nat) :
    ((rcpt γ e q k).rc γ' e' j).val = if γ' = γ ∧ e' = e ∧ j = k then q.val else 0 := by
  simp only [rcpt]; split <;> rfl

theorem ftot_rcpt (γ e : Nat) (q : Frac) (k γ' e' n : Nat) :
    ftot ((rcpt γ e q k).rc γ' e') n = if γ' = γ ∧ e' = e ∧ k < n then q.val else 0 := by
  rw [ftot_single (k := k) (fun j hj => by rw [rcpt_rc_val]; simp [hj]), rcpt_rc_val]
  by_cases h : γ' = γ ∧ e' = e
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg (fun (x : γ' = γ ∧ e' = e ∧ k = k) => h ⟨x.1, x.2.1⟩),
      if_neg (fun (x : γ' = γ ∧ e' = e ∧ k < n) => h ⟨x.1, x.2.1⟩)]
    split <;> rfl

end ECell

/-- Replacing the claims on one block, next to a ledger part `L`, keeps a composition that the
change keeps at that block under every ledger status that contains `L`'s. -/
theorem GOk.ext1 {m : Mem} {L : Ghost} (hL : ∀ x, L.extent x = ECell.unit) {b : BlockId}
    {c c' : ECell} {gF : Ghost} (hok : GOk m (L.add (Ghost.atExt b c)) gF)
    (h : ∀ ls : LStat, L.ls.Sub ls → ls.Uniq → ECell.StepE ls c c') :
    GOk m (L.add (Ghost.atExt b c')) gF := by
  obtain ⟨⟨⟨hv, hx, hcv⟩, N, hN⟩, ht, hcf⟩ := hok
  have hV : Ghost.Valid ((L.add (Ghost.atExt b c)).add gF) := ⟨hv, hx, hcv⟩
  have eled : ((L.add (Ghost.atExt b c')).add gF).led = ((L.add (Ghost.atExt b c)).add gF).led := by
    funext γ; simp [Ghost.add, Ghost.atExt]
  have eep : ((L.add (Ghost.atExt b c')).add gF).ls = ((L.add (Ghost.atExt b c)).add gF).ls := by
    funext γ e p; simp only [Ghost.ls, eled]
  have ex : ∀ x, x ≠ b → ((L.add (Ghost.atExt b c')).add gF).extent x =
      ((L.add (Ghost.atExt b c)).add gF).extent x := fun x hx => by
    simp [Ghost.add, Ghost.atExt, hx]
  have eb : ∀ c₀, ((L.add (Ghost.atExt b c₀)).add gF).extent b = c₀.add (gF.extent b) := fun c₀ => by
    simp [Ghost.add, Ghost.atExt, hL]
  have hst := h ((L.add (Ghost.atExt b c)).add gF).ls
    (fun γ e p h => Ghost.ls_add _ _ _ _ _ (Ghost.ls_add _ _ _ _ _ h)) hV.uniq
  have hb := hst.ok (by rw [← eb]; exact (hx b).1) (by rw [← eb]; exact (hx b).2)
    (by rw [← eb]; exact ht b)
  have ecl : ((L.add (Ghost.atExt b c')).add gF).cl = ((L.add (Ghost.atExt b c)).add gF).cl := by
    funext x y; simp
  refine ⟨⟨⟨by rw [eled]; exact hv, fun x => ?_, hcv.congr ecl eep⟩, N, fun γ hγ =>
    ⟨by rw [eled]; exact (hN γ hγ).1, fun x e k => ?_, by rw [eled]; exact (hN γ hγ).2.2⟩⟩, fun x => ?_,
    hcf.congr ecl⟩
  · rw [eep]
    by_cases e : x = b
    · subst e; rw [eb]; exact ⟨hb.1, hb.2.1⟩
    · rw [ex x e]; exact hx x
  · by_cases e' : x = b
    · subst e'
      rw [eb]
      have hz := fun e k => ECell.add_tags_zero (by rw [← eb]; exact (hN γ hγ).2.1 x e k)
      have hnep : ∀ e p, ¬ ((L.add (Ghost.atExt x c)).add gF).ls γ e p := fun e p ⟨M, hM⟩ => by
        rw [(hN γ hγ).1] at hM; simp [GCell.unit] at hM
      have hnpar : ∀ γ' e' e, ¬ ((L.add (Ghost.atExt x c)).add gF).ls γ' e' (some (γ, e)) :=
        fun γ' e' e ⟨M, hM⟩ => by have := (hN γ hγ).2.2 γ' e' M e; omega
      have := hst.2.2.2.2 γ hnep hnpar (fun e k => ⟨(hz e k).1, (hz e k).2.1⟩) e k
      simp only [ECell.add, Frac.add_val, this.1, this.2, (hz e k).2.2.1, (hz e k).2.2.2]; grind
    · rw [ex x e']; exact (hN γ hγ).2.1 x e k
  · show ECell.TrueIn _ _ _ _
    rw [eep]
    by_cases e : x = b
    · subst e; rw [eb]; exact hb.2.2
    · rw [ex x e]; exact ht x

open Classical in
/-- **Moving fractions between worlds**: `c` becomes `c'` next to `d`; the shares of each world `w`
change by at most `G w`, and the receipts of one child tag `(γ, e)` (in range) by `δ`. If no
active world gains (counting the receipts' change where they are live) except `(γ, e)` itself by
at most `δ`, the budgets with `(γ, e)`'s raised by `δ` balance `c'`. -/
theorem ECell.BalAt.change {ls : LStat} {c c' d : ECell} {β : Nat → Nat → Rat} {γ e n N E : Nat}
    {δ : Rat} (G : STag → Rat) (hN : γ < N) (hE : e < E)
    (hT : ∀ w, ftot (c'.tg w) n ≤ ftot (c.tg w) n + G w)
    (hrc : ∀ γ' e' j, (γ', e') ≠ (γ, e) → (c'.rc γ' e' j).val = (c.rc γ' e' j).val)
    (hR : ftot ((c'.add d).rc γ e) n = ftot ((c.add d).rc γ e) n + δ)
    (hG : ∀ w, Act ls w → G w + (if ∃ e', e ≤ e' ∧ ls γ e' w then δ else 0) ≤
      if w = some (γ, e) then δ else 0)
    (h : (c.add d).BalAt ls β n N E) :
    (c'.add d).BalAt ls (fun γ₁ e₁ => if (γ₁, e₁) = (γ, e) then β γ e + δ else β γ₁ e₁) n N E := by
  have hm : ∀ w, Act ls w → (c'.add d).mass ls (fun γ₁ e₁ => if (γ₁, e₁) = (γ, e) then β γ e + δ else β γ₁ e₁)
      w n N E ≤ (c.add d).mass ls β w n N E + (if w = some (γ, e) then δ else 0) := fun w hw => by
    have := ECell.mass_change (ls := ls) (c := c) (c' := c') (d := d) (β := β)
      (β' := fun γ₁ e₁ => if (γ₁, e₁) = (γ, e) then β γ e + δ else β γ₁ e₁) (w := w) (n := n) (A := G w)
      (B := if ∃ e', e ≤ e' ∧ ls γ e' w then δ else 0) hN hE (hT w) hrc
      (fun γ' e' hne => by simp only [hne, if_false])
      (cwt_shift hR (fun _ => by simp only [if_true]))
    have := hG w hw
    grind
  refine ⟨?_, fun γ₁ e₁ hγ he ha => ?_⟩
  · have := hm none .root; simp only [reduceCtorEq, if_false] at this; have := h.1; grind
  · have h1 := hm _ ha
    have h2 := h.2 γ₁ e₁ hγ he ha
    by_cases hx : (γ₁, e₁) = (γ, e)
    · simp only [Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
      simp only [if_true] at h1 ⊢; grind
    · have hx' : some (γ₁, e₁) ≠ some (γ, e) := fun y => hx (Option.some.inj y)
      simp only [hx, hx', if_false] at h1 ⊢; grind

/-! ## Updates in a memory -/

namespace EUpd

variable {P P' P'' R : FAssn}

/-- A ghost update (`Upd`) is an update in every memory: it keeps the extent claims. -/
theorem of_upd (hu : Upd P P') : EUpd P P' := fun m r rF hh hp _ => by
  obtain ⟨r', hp', e, k, x, xc, hg, ht⟩ := hu r hp rF.gh hh.ghost.1
  exact ⟨r', ⟨by rw [e]; exact hh.disj, by rw [e]; exact hh.heap, by rw [k]; exact hh.know,
    hh.knowF, ⟨hg, ht m hh.ghost.2.1, hh.ghost.2.2.congr (by funext x y; simp [xc])⟩⟩, hp'⟩

/-- Updates frame. -/
theorem frame (h : EUpd P P') : EUpd (P ⋆ R) (P' ⋆ R) := by
  rintro m _ rF hh ⟨r₁, r₂, hd, rfl, hp, hr⟩ hs
  have h2F := (FHeap.disjoint_union_left.mp hh.disj).2
  obtain ⟨r₁', hh', hp'⟩ := h m r₁ _ (Holds.split hd hh) hp hs
  have hd' := (FHeap.disjoint_union_right.mp hh'.disj).1
  exact ⟨_, Holds.join hd' h2F hh', ⟨r₁', r₂, hd', rfl, hp', hr⟩⟩

theorem frameL (h : EUpd P P') : EUpd (R ⋆ P) (R ⋆ P') :=
  trans (of_imp fun _ h => sep_comm h) (trans (frame h) (of_imp fun _ h => sep_comm h))

/-- An update from each witness of an existential. -/
theorem ex {γ : Type} {P : γ → FAssn} (h : ∀ x, EUpd (P x ⋆ R) P') : EUpd (FAssn.ex P ⋆ R) P' :=
  fun m r rF hh hp hs => by obtain ⟨x, hx⟩ := sep_ex.mp hp; exact h x m r rF hh hx hs

/-- An update from every witness of an existential. -/
theorem exAll {γ : Type} {P : γ → FAssn} (h : ∀ x, EUpd (P x) P') : EUpd (FAssn.ex P) P' :=
  fun m r rF hh hp hs => by obtain ⟨x, hx⟩ := hp; exact h x m r rF hh hx hs

/-- An update under a pure fact. -/
theorem lift {φ : Prop} (h : φ → EUpd P P') : EUpd (⟪φ⟫ ⋆ P) P' :=
  fun m r rF hh hp hs => by obtain ⟨hφ, hp⟩ := sep_lift.mp hp; exact h hφ m r rF hh hp hs

/-- An update that may use a fact of every memory that holds `P`. -/
theorem withFact {φ : Prop} (hφ : ∀ m r rF, Holds m r rF → P r → m.FSeq → φ) (h : φ → EUpd P P') :
    EUpd P P' := fun m r rF hh hp hs => h (hφ m r rF hh hp hs) m r rF hh hp hs

/-- A fact of every memory that holds `P`. -/
theorem fact {φ : Prop} (hφ : ∀ m r rF, Holds m r rF → P r → m.FSeq → φ) : EUpd P (⟪φ⟫ ⋆ P) :=
  fun m r rF hh hp hs => ⟨r, hh, sep_lift.mpr ⟨hφ m r rF hh hp hs, hp⟩⟩

/-- **A local update of one block's claims** next to a ledger part `L` (`ECell.StepE` under every
ledger status that contains `L`'s). -/
theorem ext1L {L : Ghost} (hL : ∀ x, L.extent x = ECell.unit) {b : BlockId} {c c' : ECell}
    (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, L.add (Ghost.atExt b c)⟩ ∧
      P' ⟨FHeap.empty, Know.none, L.add (Ghost.atExt b c')⟩ ∧
      ∀ ls : LStat, L.ls.Sub ls → ls.Uniq → ECell.StepE ls c c') : EUpd P P' := by
  intro m r rF hh hr _
  obtain ⟨e, hp', hst⟩ := hp r hr
  subst e
  exact ⟨⟨FHeap.empty, Know.none, L.add (Ghost.atExt b c')⟩,
    ⟨hh.disj, hh.heap, hh.know, hh.knowF, GOk.ext1 hL hh.ghost hst⟩, hp'⟩

/-- **A local update of one tag's shares on one block** (`ECell.StepT`). -/
theorem ext1T {t : STag} {b : BlockId} {c c' : ECell}
    (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, Ghost.atExt b c⟩ ∧
      P' ⟨FHeap.empty, Know.none, Ghost.atExt b c'⟩ ∧ ECell.StepT t c c') : EUpd P P' :=
  ext1L (L := Ghost.unit) (fun _ => rfl) fun r h => by
    obtain ⟨e, hp', hst⟩ := hp r h
    exact ⟨by rw [Ghost.unit_add]; exact e, by rw [Ghost.unit_add]; exact hp', fun ls _ _ => hst.toE ls⟩

/-- **A local update of one block's untagged claims** (`ECell.Step`). -/
theorem ext1 {b : BlockId} {c c' : ECell}
    (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, Ghost.atExt b c⟩ ∧
      P' ⟨FHeap.empty, Know.none, Ghost.atExt b c'⟩ ∧ ECell.Step c c') : EUpd P P' :=
  ext1T (t := none) fun r h => by
    obtain ⟨e, hp', hst⟩ := hp r h
    exact ⟨e, hp', hst.toT⟩

end EUpd

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

/-- The claims of a share with tag `t`, as the sum of two. -/
theorem ECell.shareT_add (t : STag) (q₁ q₂ : Frac) (k : Nat) :
    ECell.shareT t (q₁.add q₂) k = (ECell.shareT t q₁ k).add (ECell.shareT t q₂ k) := by
  rcases t with _ | ⟨γ, e⟩ <;> ext <;>
    simp only [ECell.shareT, ECell.share, ECell.tshare, ECell.add] <;> (try split) <;> simp

/-- **Split and join a share** at one bound (any tag). -/
theorem bshare_split {t : STag} {r : Res} (h₁ : 0 < q₁.val) (h₂ : 0 < q₂.val) :
    bshare b (q₁.add q₂) k t r ↔ (bshare b q₁ k t ⋆ bshare b q₂ k t) r := by
  constructor
  · intro h
    rw [bshareT_eq h, ECell.shareT_add]
    exact ext_sep_intro ⟨h₁, rfl, rfl, rfl⟩ ⟨h₂, rfl, rfl, rfl⟩
  · intro h
    rw [ext_sep_eq (fun _ h => bshareT_eq h) (fun _ h => bshareT_eq h) h, ← ECell.shareT_add]
    exact ⟨by simp only [Frac.add_val]; grind, rfl, rfl, rfl⟩

theorem ECell.rcpt_add (γ e : Nat) (q₁ q₂ : Frac) (k : Nat) :
    ECell.rcpt γ e (q₁.add q₂) k = (ECell.rcpt γ e q₁ k).add (ECell.rcpt γ e q₂ k) := by
  ext <;> simp only [ECell.rcpt, ECell.add] <;> (try split) <;> simp

/-- **Split and join a receipt** at one bound: a receipt is a fraction like a share (an arena
whose grant's holder passes on part of its share splits the grant's receipt to match). -/
theorem brcpt_split {γ e : Nat} {r : Res} (h₁ : 0 < q₁.val) (h₂ : 0 < q₂.val) :
    brcpt b (q₁.add q₂) k γ e r ↔ (brcpt b q₁ k γ e ⋆ brcpt b q₂ k γ e) r := by
  constructor
  · intro h
    rw [brcpt_eq h, ECell.rcpt_add]
    exact ext_sep_intro ⟨h₁, rfl, rfl, rfl⟩ ⟨h₂, rfl, rfl, rfl⟩
  · intro h
    rw [ext_sep_eq (fun _ h => brcpt_eq h) (fun _ h => brcpt_eq h) h, ← ECell.rcpt_add]
    exact ⟨by simp only [Frac.add_val]; grind, rfl, rfl, rfl⟩

/-- **Join two shares** of one tag at the higher bound: the share there already certifies it. -/
theorem EUpd.join {t : STag} :
    EUpd (bshare b q₁ k t ⋆ bshare b q₂ k' t) (bshare b (q₁.add q₂) (Max.max k k') t) := by
  refine EUpd.ext1T (t := t) (b := b) (c := (ECell.shareT t q₁ k).add (ECell.shareT t q₂ k'))
    (c' := ECell.shareT t (q₁.add q₂) (Max.max k k')) fun r h => ?_
  have e := ext_sep_eq (fun _ h => bshareT_eq h) (fun _ h => bshareT_eq h) h
  obtain ⟨r₁, r₂, -, -, ⟨hp1, -⟩, ⟨hp2, -⟩⟩ := h
  have := q₁.nonneg; have := q₂.nonneg
  refine ⟨e, ⟨by simp only [Frac.add_val]; grind, rfl, rfl, rfl⟩,
    by funext x; simp [ECell.add], fun n => ⟨n, Nat.le_refl _, ?_⟩, fun j hj => ?_,
    fun u j hu => ?_, fun γ e j => by simp [ECell.add]⟩
  · rw [ECell.ftot_tg_add, ECell.ftot_tg_shareT, ECell.ftot_tg_shareT, ECell.ftot_tg_shareT]
    simp only [Frac.add_val, true_and]
    by_cases h1 : Max.max k k' < n
    · rw [if_pos h1, if_pos (by omega), if_pos (by omega)]; exact Rat.le_refl
    · rw [if_neg h1]; split <;> split <;> grind
  · rw [ECell.tg_shareT] at hj
    simp only [true_and] at hj
    split at hj
    · rename_i e; subst e
      left
      rcases Nat.le_total k k' with hkk | hkk
      · refine ⟨k', by omega, ?_⟩
        rw [ECell.tg_add_val, ECell.tg_shareT, ECell.tg_shareT]; simp only [true_and]; split <;> grind
      · refine ⟨k, by omega, ?_⟩
        rw [ECell.tg_add_val, ECell.tg_shareT, ECell.tg_shareT]; simp only [true_and]; split <;> grind
    · simp at hj
  · rw [ECell.tg_add_val, ECell.tg_shareT, ECell.tg_shareT, ECell.tg_shareT]; (simp [hu]) <;> grind

/-- **Weaken a share's bound** (any tag). -/
theorem EUpd.weaken {t : STag} (h : k' ≤ k) : EUpd (bshare b q k t) (bshare b q k' t) := by
  refine EUpd.ext1T (t := t) (c := ECell.shareT t q k) (c' := ECell.shareT t q k') fun r hr =>
    ⟨bshareT_eq hr, ⟨hr.1, rfl, rfl, rfl⟩, by funext x; simp, fun n => ⟨Max.max n (k + 1), by omega, ?_⟩,
      fun j hj => .inl ⟨k, ?_, ?_⟩, fun u j hu => by rw [ECell.tg_shareT, ECell.tg_shareT]; simp [hu],
      fun _ _ _ => by simp⟩
  · rw [ECell.ftot_tg_shareT, ECell.ftot_tg_shareT]; have := q.nonneg; simp only [true_and]
    split
    · rw [if_pos (by omega)]; exact Rat.le_refl
    · split <;> grind
  · rw [ECell.tg_shareT] at hj; simp only [true_and] at hj; split at hj <;> simp_all
  · rw [ECell.tg_shareT]; simp only [true_and, if_true]; exact hr.1

/-! ## Facts -/

/-- The claims of a held resource are true. -/
theorem Holds.extTrue {m : Mem} {r rF : Res} (hh : Holds m r rF) : ExtTrue m r.gh :=
  ExtTrue.of_add hh.ghost.2.1

theorem Holds.claims {m : Mem} {r rF : Res} {P R : FAssn} (hh : Holds m r rF) (h : (P ⋆ R) r) :
    ∃ r₁, P r₁ ∧ ExtTrue m r₁.gh := by
  obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := h
  exact ⟨r₁, h1, ExtTrue.of_add hh.extTrue⟩

/-- **A held share gives a live block** of at least `k` bytes, while its tag is active (always
for an untagged share; a tagged one needs the ledgers of its chain in the resource). -/
theorem Holds.bshare {t : STag} {m : Mem} {r rF : Res} {R : FAssn} (hh : Holds m r rF)
    (h : (bshare b q k t ⋆ R) r) (ha : Act r.gh.ls t := by exact Act.root) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ k ≤ blk.bytes.size ∧
      blk.kind.mappedLo < blk.bytes.size := by
  have ht := hh.ghost.2.1 b
  obtain ⟨r₁, r₂, -, rfl, h1, -⟩ := h
  have hle : (r₁.gh.extent b).Le (((r₁.gh.add r₂.gh).add rF.gh).extent b) :=
    (ECell.le_add _ _).trans (ECell.le_add _ _)
  refine ht.2 k (ECell.Req.mono (Ghost.ls_add _ _) hle (.inl ⟨t, ha, ?_⟩))
  rw [h1.2.2.2]; simp only [Ghost.atExt, if_true]; rw [ECell.tg_shareT]; simp only [true_and, if_true]
  exact h1.1

/-! ### Parts of a separating conjunction -/

/-- `X` is one of the separated parts of `P`: every resource of `P` splits into one of `X` and a
rest. The `within` tactic finds `X` in the separating conjunctions of `P`. -/
def Within (X P : FAssn) : Prop := ∀ r, P r → ∃ R : FAssn, (X ⋆ R) r

theorem Within.refl (X : FAssn) : Within X X := fun _ h => ⟨emp, sep_emp.mpr h⟩

theorem Within.sepL {X P R : FAssn} (h : Within X P) : Within X (P ⋆ R) := fun _ hr => by
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := hr
  obtain ⟨R', h'⟩ := h r₁ h1
  exact ⟨R' ⋆ R, sep_assoc ⟨r₁, r₂, hd, rfl, h', h2⟩⟩

theorem Within.sepR {X P R : FAssn} (h : Within X P) : Within X (R ⋆ P) := fun r hr =>
  h.sepL r (sep_comm hr)

theorem Within.trans {X Y P : FAssn} (h₁ : Within X Y) (h₂ : Within Y P) : Within X P := fun r hr => by
  obtain ⟨R, h⟩ := h₂ r hr
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := h
  obtain ⟨R', h'⟩ := h₁ r₁ h1
  exact ⟨R' ⋆ R, sep_assoc ⟨r₁, r₂, hd, rfl, h', h2⟩⟩

/-- `within`: prove `Within X P` by finding `X` among the separated parts of `P`. Definitions
are unfolded to find the separating conjunctions; a part matches `X` up to reducible unfolding
(state `X` with the same definitions as `P`'s parts). -/
syntax "within" : tactic
macro_rules
  | `(tactic| within) =>
    `(tactic| first
      | with_reducible exact Within.refl _
      | (apply Within.sepL; within)
      | (apply Within.sepR; within))

/-- **A held share gives a live block**, for a share among the parts of the resource
(`Holds.bshare`). -/
theorem Holds.bshareW {t : STag} {m : Mem} {r rF : Res} {P : FAssn} (hh : Holds m r rF)
    (hw : Within (Full.bshare b q k t) P) (hp : P r) (ha : Act r.gh.ls t := by exact Act.root) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ k ≤ blk.bytes.size ∧
      blk.kind.mappedLo < blk.bytes.size := by
  obtain ⟨R, h⟩ := hw r hp
  exact hh.bshare h ha

/-- **The authority gives the block's extent.** -/
theorem Holds.bauth {m : Mem} {r rF : Res} {R : FAssn} (hh : Holds m r rF) (h : (bauth b S K q ⋆ R) r) :
    ∃ blk, m.blocks[b]? = some blk ∧ blk.live = true ∧ blk.bytes.size = S ∧ blk.kind = K ∧
      K.mappedLo < S := by
  obtain ⟨r₁, h1, ht⟩ := hh.claims h
  rw [bauth_eq h1] at ht
  exact (ht b).1 S K (by simp [Ghost.atExt, ECell.auth1])

end Rules

/-! ## Tagged shares (`docs/sep-full-state.md` §Epoch-tagged shares, §Nested tags)

A share tagged `(γ, e)` (`bshare b q k (some (γ, e))`) counts and is true only while the tag is
active: ledger `γ` is at epoch `e` and `γ`'s parent tag `p` is active. It is lent off a share
tagged `p` (the root `none`: an untagged share) together with a receipt (`EUpd.lendT`); given back
during its epoch it cancels its receipt and the `p`-tagged share returns (`EUpd.returnT`); once the
ledger is past `e`, the receipt alone turns back into a `p`-tagged share (`EUpd.revoke`), whatever
the holder of the tagged share kept, and every share lent further from it is dormant with it.
Every rule needs the ledger's authority, which fixes `p`. -/

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

theorem total_tags (γ e : Nat) (q q' : Frac) (k k' n : Nat) :
    ((tshare γ e q k').add (rcpt γ e q' k)).total n = 0 := by
  rw [total_eq, ftot_zero (fun j => by simp [add])]

theorem total_rcpt (γ e : Nat) (q : Frac) (k n : Nat) : (rcpt γ e q k).total n = 0 := by
  rw [total_eq, ftot_zero (fun j => rfl)]

end ECell

section Tags

variable {b : BlockId} {k k' : Nat} {q : Frac} {γ e : Nat} {M : GMap} {p : STag}

/-- `gauthP γ e M p ⋆ P`, where `P` holds the claims `c` on block `b` only, as one resource. -/
theorem gauth_ext_eq {P : FAssn} {c : ECell} (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, Ghost.atExt b c⟩)
    {r : Res} (h : (gauthP γ e M p ⋆ P) r) :
    r = ⟨FHeap.empty, Know.none, (Ghost.at γ (GCell.auth1 e M p)).add (Ghost.atExt b c)⟩ := by
  obtain ⟨r₁, r₂, -, rfl, ⟨h1, k1, g1⟩, h2⟩ := h
  rw [hp _ h2, h1, k1, g1]; simp [FHeap.union_empty, Know.union_none]

theorem gauth_ext_intro {P : FAssn} {c : ECell} (hp : P ⟨FHeap.empty, Know.none, Ghost.atExt b c⟩) :
    (gauthP γ e M p ⋆ P) ⟨FHeap.empty, Know.none, (Ghost.at γ (GCell.auth1 e M p)).add (Ghost.atExt b c)⟩ :=
  ⟨⟨FHeap.empty, Know.none, Ghost.at γ (GCell.auth1 e M p)⟩, ⟨FHeap.empty, Know.none, Ghost.atExt b c⟩,
    FHeap.disjoint_empty _, by simp [FHeap.union_empty, Know.union_none], ⟨rfl, rfl, rfl⟩, hp⟩

theorem Ghost.at_extent (γ : Nat) (c : GCell) (x : BlockId) : (Ghost.at γ c).extent x = ECell.unit := rfl

theorem Ghost.at_auth1_ls : (Ghost.at γ (GCell.auth1 e M p)).ls γ e p :=
  ⟨M, by simp [Ghost.at, GCell.auth1]⟩

theorem ECell.ftot_rcpt_tg (γ e : Nat) (q : Frac) (k : Nat) (w : STag) (n : Nat) :
    ftot ((ECell.rcpt γ e q k).tg w) n = 0 := ftot_zero (fun _ => by simp) n

theorem ECell.ftot_shareT_rc (u : STag) (q : Frac) (k γ e n : Nat) :
    ftot ((ECell.shareT u q k).rc γ e) n = 0 := ftot_zero (fun _ => by simp) n

/-- **Lend a tagged share** off a share tagged with the ledger's parent `p`: the holder gets a
share tagged `(γ, e)` (at a bound up to the old one), the lender a receipt for it, which lies in
`p`'s world. Needs ledger `γ` at epoch `e`. With `p = none` it lends off an untagged share. -/
theorem EUpd.lendT (hk : k' ≤ k) :
    EUpd (gauthP γ e M p ⋆ bshare b q k p)
      (gauthP γ e M p ⋆ (bshare b q k' (some (γ, e)) ⋆ brcpt b q k γ e)) := by
  refine EUpd.ext1L (L := Ghost.at γ (GCell.auth1 e M p)) (Ghost.at_extent _ _) (b := b)
    (c := ECell.shareT p q k) (c' := (ECell.tshare γ e q k').add (ECell.rcpt γ e q k)) fun r h => ?_
  have hq : 0 < q.val := by obtain ⟨_, _, _, _, _, h2⟩ := h; exact h2.1
  refine ⟨gauth_ext_eq (fun _ h => bshareT_eq h) h,
    gauth_ext_intro (ext_sep_intro ⟨hq, rfl, rfl, rfl⟩ ⟨hq, rfl, rfl, rfl⟩), fun ls hL hu => ?_⟩
  have hls : ls γ e p := hL _ _ _ Ghost.at_auth1_ls
  have hlive : ∀ w, (∃ e', e ≤ e' ∧ ls γ e' w) → w = p := fun w ⟨e', _, h⟩ => (hu _ _ _ _ _ h hls).2
  have hrc0 : ∀ γ' e' j, (γ', e') ≠ (γ, e) →
      (((ECell.tshare γ e q k').add (ECell.rcpt γ e q k)).rc γ' e' j).val = ((ECell.shareT p q k).rc γ' e' j).val :=
    fun γ' e' j hne => by
      have : ¬ (γ' = γ ∧ e' = e ∧ j = k) := fun x => hne (by rw [x.1, x.2.1])
      simp only [ECell.rc_add_val, ECell.rcpt_rc_val, this, if_false, ECell.shareT_rc]
      simp [ECell.tshare]; grind
  refine ⟨by funext x; simp [ECell.add], fun d n N E => ⟨Max.max n (k + 1), Max.max N (γ + 1),
    Max.max E (e + 1), fun ⟨β, hb⟩ => ⟨_, (ECell.BalAt.change (γ := γ) (e := e) (n := Max.max n (k + 1)) (N := Max.max N (γ + 1))
      (E := Max.max E (e + 1)) (δ := q.val)
      (fun w => (if w = some (γ, e) then q.val else 0) - (if w = p then q.val else 0))
      (by omega) (by omega) (fun w => ?_) hrc0 ?_ (fun w _ => ?_) hb).anti (Nat.le_max_left _ _)
      (Nat.le_max_left _ _) (Nat.le_max_left _ _)⟩⟩, fun j hj => ?_, fun hf γ₁ e₁ j hfu => ?_,
    fun γ₁ hn hnp _ e₁ j => ?_⟩
  · rw [ECell.ftot_tg_add, ECell.ftot_rcpt_tg, ← ECell.shareT_some, ECell.ftot_tg_shareT, ECell.ftot_tg_shareT]
    simp only [show k' < Max.max n (k + 1) by omega, show k < Max.max n (k + 1) by omega, and_true]
    grind
  · rw [ECell.ftot_rc_add, ECell.ftot_rc_add, ECell.ftot_rc_add, ECell.ftot_rcpt, ECell.ftot_shareT_rc]
    simp only [ECell.ftot_tshare_rc, true_and, show k < Max.max n (k + 1) by omega, if_true]; grind
  · have := q.nonneg
    by_cases hl : ∃ e', e ≤ e' ∧ ls γ e' w
    · rw [if_pos hl, hlive w hl]; split <;> split <;> grind
    · rw [if_neg hl]; split <;> split <;> grind
  · left
    refine ⟨k, ?_, .inl ⟨p, ?_, by rw [ECell.tg_shareT]; simp [hq]⟩⟩
    · rcases hj with ⟨u, -, hp⟩ | ⟨γ', e', -, hp⟩
      · rw [ECell.tg_add_val, ← ECell.shareT_some, ECell.tg_shareT, ECell.rcpt_tg] at hp
        simp only [Frac.zero_val] at hp; split at hp <;> grind
      · rw [ECell.rc_add_val, ECell.rcpt_rc_val] at hp
        simp only [ECell.tshare_rc, Frac.zero_val] at hp; split at hp <;> grind
    · rcases hj with ⟨u, hu', hp⟩ | ⟨γ', e', ⟨w, e'', hee, hl, hw⟩, hp⟩
      · rw [ECell.tg_add_val, ← ECell.shareT_some, ECell.tg_shareT, ECell.rcpt_tg] at hp
        simp only [Frac.zero_val] at hp
        split at hp
        · rename_i hx; obtain ⟨rfl, -⟩ := hx
          obtain ⟨p', h1, h2⟩ := hu'.inv
          rw [(hu _ _ _ _ _ h1 hls).2] at h2; exact h2
        · grind
      · rw [ECell.rc_add_val, ECell.rcpt_rc_val] at hp
        simp only [ECell.tshare_rc, Frac.zero_val] at hp
        split at hp
        · rename_i hx; obtain ⟨rfl, rfl, -⟩ := hx
          rw [← hlive w ⟨e'', hee, hl⟩]; exact hw
        · grind
  · -- a future tag: not `(γ, e)` (its parent `p` would be future, and `p` holds `q`)
    have hne : (γ₁, e₁) ≠ (γ, e) := fun x => by
      simp only [Prod.mk.injEq] at x; obtain ⟨rfl, rfl⟩ := x
      cases hfu with
      | own h1 h2 => have := (hu _ _ _ _ _ h1 hls).1; omega
      | up h1 h2 =>
        rw [(hu _ _ _ _ _ h1 hls).2] at h2
        rcases p with _ | ⟨γp, ep⟩
        · exact h2.not_none
        · have := (hf γp ep k h2).1
          simp [ECell.shareT, ECell.tshare] at this; grind
    have : ¬ (γ₁ = γ ∧ e₁ = e ∧ j = k') := fun x => hne (by rw [x.1, x.2.1])
    have : ¬ (γ₁ = γ ∧ e₁ = e ∧ j = k) := fun x => hne (by rw [x.1, x.2.1])
    simp [ECell.add, ECell.tshare, ECell.rcpt_rc_val, *]
  · have : γ₁ ≠ γ := fun x => hn e p (x ▸ hls)
    simp [ECell.add, ECell.tshare, ECell.rcpt_rc_val, this]

/-- **Give a tagged share back** during its epoch: it cancels its receipt, and the receipt's
holder gets the share tagged with the ledger's parent `p` back, at the receipt's bound. -/
theorem EUpd.returnT (hk : k' ≤ k) :
    EUpd (gauthP γ e M p ⋆ (bshare b q k' (some (γ, e)) ⋆ brcpt b q k γ e))
      (gauthP γ e M p ⋆ bshare b q k p) := by
  refine EUpd.ext1L (L := Ghost.at γ (GCell.auth1 e M p)) (Ghost.at_extent _ _) (b := b)
    (c := (ECell.tshare γ e q k').add (ECell.rcpt γ e q k)) (c' := ECell.shareT p q k) fun r h => ?_
  have hq : 0 < q.val := by obtain ⟨_, _, _, _, _, _, _, _, _, h2, _⟩ := h; exact h2.1
  refine ⟨gauth_ext_eq (fun _ h => ext_sep_eq (fun _ h => bshareT_eq h) (fun _ h => brcpt_eq h) h) h,
    gauth_ext_intro ⟨hq, rfl, rfl, rfl⟩, fun ls hL hu => ?_⟩
  have hls : ls γ e p := hL _ _ _ Ghost.at_auth1_ls
  have hlive : ∀ w, (∃ e', e ≤ e' ∧ ls γ e' w) → w = p := fun w ⟨e', _, h⟩ => (hu _ _ _ _ _ h hls).2
  refine ⟨by funext x; simp [ECell.add], fun d n N E => ⟨Max.max n (k + 1), Max.max N (γ + 1),
    Max.max E (e + 1), fun ⟨β, hb⟩ => ⟨_, (ECell.BalAt.change (γ := γ) (e := e) (n := Max.max n (k + 1)) (N := Max.max N (γ + 1))
      (E := Max.max E (e + 1)) (δ := -q.val)
      (fun w => (if w = p then q.val else 0) - (if w = some (γ, e) then q.val else 0))
      (by omega) (by omega) (fun w => ?_) (fun γ' e' j hne => ?_) ?_ (fun w _ => ?_) hb).anti
      (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)⟩⟩, fun j hj => ?_,
    fun hf γ₁ e₁ j hfu => ?_, fun γ₁ hn hnp _ e₁ j => ?_⟩
  · rw [ECell.ftot_tg_add, ECell.ftot_rcpt_tg, ← ECell.shareT_some, ECell.ftot_tg_shareT, ECell.ftot_tg_shareT]
    simp only [show k' < Max.max n (k + 1) by omega, show k < Max.max n (k + 1) by omega, and_true]
    grind
  · have : ¬ (γ' = γ ∧ e' = e ∧ j = k) := fun x => hne (by rw [x.1, x.2.1])
    simp only [ECell.rc_add_val, ECell.rcpt_rc_val, this, if_false, ECell.shareT_rc]
    simp [ECell.tshare]; grind
  · rw [ECell.ftot_rc_add, ECell.ftot_rc_add, ECell.ftot_rc_add, ECell.ftot_rcpt, ECell.ftot_shareT_rc]
    simp only [ECell.ftot_tshare_rc, true_and, show k < Max.max n (k + 1) by omega, if_true]; grind
  · have := q.nonneg
    by_cases hl : ∃ e', e ≤ e' ∧ ls γ e' w
    · rw [if_pos hl, hlive w hl]; split <;> split <;> grind
    · have hwp : w ≠ p := fun h => hl ⟨e, Nat.le_refl _, h ▸ hls⟩
      rw [if_neg hl]; split <;> split <;> grind
  · rcases hj with ⟨u, hu', hp⟩ | ⟨γ', e', -, hp⟩
    · rw [ECell.tg_shareT] at hp
      split at hp
      · rename_i hx; obtain ⟨rfl, rfl⟩ := hx
        exact .inl ⟨j, Nat.le_refl _, .inr ⟨γ, e, ⟨u, e, Nat.le_refl _, hls, hu'⟩,
          by rw [ECell.rc_add_val, ECell.rcpt_rc_val]; simp; grind⟩⟩
      · simp at hp
    · simp at hp
  · -- `p`'s tag would make `(γ, e)` future, which holds `q`
    rw [ECell.shareT_rc]; refine ⟨?_, rfl⟩
    rcases p with _ | ⟨γp, ep⟩
    · rfl
    · have hfp : Fut ls (some (γp, ep)) → False := fun hfp => by
        have := (hf γ e k' (.up hls hfp)).1
        simp [ECell.add, ECell.tshare] at this; grind
      simp only [ECell.shareT, ECell.tshare]
      split
      · rename_i hx; obtain ⟨rfl, rfl, -⟩ := hx; exact absurd hfu hfp
      · rfl
  · rcases p with _ | ⟨γp, ep⟩
    · simp [ECell.shareT, ECell.share]
    · have : γ₁ ≠ γp := fun x => hnp γ e ep (x ▸ hls)
      simp [ECell.shareT, ECell.tshare, this]

/-- **Revoke a past epoch's share**: once ledger `γ` is past epoch `e`, a receipt of epoch `e`
turns back into a share tagged with the ledger's parent `p`, whatever the holder of the tagged
share kept (it is dormant, and so is every share lent further from it). -/
theorem EUpd.revoke {e' : Nat} (he : e < e') :
    EUpd (gauthP γ e' M p ⋆ brcpt b q k γ e) (gauthP γ e' M p ⋆ bshare b q k p) := by
  refine EUpd.ext1L (L := Ghost.at γ (GCell.auth1 e' M p)) (Ghost.at_extent _ _) (b := b)
    (c := ECell.rcpt γ e q k) (c' := ECell.shareT p q k) fun r h => ?_
  have hq : 0 < q.val := by obtain ⟨_, _, _, _, _, h2⟩ := h; exact h2.1
  refine ⟨gauth_ext_eq (fun _ h => brcpt_eq h) h, gauth_ext_intro ⟨hq, rfl, rfl, rfl⟩,
    fun ls hL hu => ?_⟩
  have hls : ls γ e' p := hL _ _ _ Ghost.at_auth1_ls
  have hlive : ∀ w, (∃ x, e ≤ x ∧ ls γ x w) → w = p := fun w ⟨x, _, h⟩ => (hu _ _ _ _ _ h hls).2
  have hnot : ¬ Act ls (some (γ, e)) := fun ha => by
    obtain ⟨p', h1, -⟩ := ha.inv; have := (hu _ _ _ _ _ h1 hls).1; omega
  refine ⟨by funext x; simp, fun d n N E => ⟨Max.max n (k + 1), Max.max N (γ + 1),
    Max.max E (e + 1), fun ⟨β, hb⟩ => ⟨_, (ECell.BalAt.change (γ := γ) (e := e) (n := Max.max n (k + 1)) (N := Max.max N (γ + 1))
      (E := Max.max E (e + 1)) (δ := -q.val)
      (fun w => if w = p then q.val else 0)
      (by omega) (by omega) (fun w => ?_) (fun γ' e₀ j hne => ?_) ?_ (fun w hw => ?_) hb).anti
      (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)⟩⟩, fun j hj => ?_,
    fun hf γ₁ e₁ j hfu => ?_, fun γ₁ hn hnp _ e₁ j => ?_⟩
  · rw [ECell.ftot_rcpt_tg, ECell.ftot_tg_shareT]
    simp only [show k < Max.max n (k + 1) by omega, and_true]; grind
  · have : ¬ (γ' = γ ∧ e₀ = e ∧ j = k) := fun x => hne (by rw [x.1, x.2.1])
    simp only [ECell.rcpt_rc_val, this, if_false, ECell.shareT_rc, Frac.zero_val]
  · rw [ECell.ftot_rc_add, ECell.ftot_rc_add, ECell.ftot_rcpt, ECell.ftot_shareT_rc]
    simp only [true_and, show k < Max.max n (k + 1) by omega, if_true]; grind
  · have hwt : w ≠ some (γ, e) := fun x => hnot (x ▸ hw)
    rw [if_neg hwt]
    have := q.nonneg
    by_cases hl : ∃ x, e ≤ x ∧ ls γ x w
    · rw [if_pos hl, hlive w hl]; simp only [if_true]; grind
    · have hwp : w ≠ p := fun h => hl ⟨e', Nat.le_of_lt he, h ▸ hls⟩
      rw [if_neg hl, if_neg hwp]; grind
  · rcases hj with ⟨u, hu', hp⟩ | ⟨γ', e₀, -, hp⟩
    · rw [ECell.tg_shareT] at hp
      split at hp
      · rename_i hx; obtain ⟨rfl, rfl⟩ := hx
        exact .inl ⟨j, Nat.le_refl _, .inr ⟨γ, e, ⟨u, e', Nat.le_of_lt he, hls, hu'⟩,
          by rw [ECell.rcpt_rc_val]; simp [hq]⟩⟩
      · simp at hp
    · simp at hp
  · rw [ECell.shareT_rc]; refine ⟨?_, rfl⟩
    rcases p with _ | ⟨γp, ep⟩
    · rfl
    · have hfp : Fut ls (some (γp, ep)) → False := fun hfp => by
        have := (hf γ e k (.up hls hfp)).2
        rw [ECell.rcpt_rc_val] at this; simp at this; grind
      simp only [ECell.shareT, ECell.tshare]
      split
      · rename_i hx; obtain ⟨rfl, rfl, -⟩ := hx; exact absurd hfu hfp
      · rfl
  · rcases p with _ | ⟨γp, ep⟩
    · simp [ECell.shareT, ECell.share]
    · have : γ₁ ≠ γp := fun x => hnp γ e' ep (x ▸ hls)
      simp [ECell.shareT, ECell.tshare, this]

open Classical in
/-- A child's weight grows with its receipts' fraction. -/
theorem cwt_le_of_ftot {ls : LStat} {w : STag} {β : Nat → Nat → Rat} {γ e : Nat} {R R' : Nat → Frac}
    {n n' : Nat} (h : ftot R n ≤ ftot R' n') : cwt ls w β γ e R n ≤ cwt ls w β γ e R' n' := by
  unfold cwt; split
  · grind
  · split <;> grind

/-- **Weaken a receipt's bound**: a receipt claims less at a lower bound (and gives back a share
at the lower bound). Any ledger status; the fraction is unchanged. -/
theorem EUpd.rweaken (h : k' ≤ k) : EUpd (brcpt b q k γ e) (brcpt b q k' γ e) := by
  refine EUpd.ext1L (L := Ghost.unit) (fun _ => rfl) (b := b) (c := ECell.rcpt γ e q k)
    (c' := ECell.rcpt γ e q k') fun r hr => ?_
  have hq := hr.1
  refine ⟨by rw [Ghost.unit_add]; exact brcpt_eq hr, by rw [Ghost.unit_add]; exact ⟨hq, rfl, rfl, rfl⟩,
    fun ls _ _ => ⟨by funext x; simp, fun d n N E => ⟨Max.max n (k + 1), N, E, fun ⟨β, hb⟩ => ⟨β, ?_⟩⟩,
      fun j hj => ?_, fun hf γ₁ e₁ j hfu => ?_, fun γ₁ _ _ hz e₁ j => ?_⟩⟩
  · -- every world weighs no more below `n` than before below `max n (k + 1)`
    have hm : ∀ w, ((ECell.rcpt γ e q k').add d).mass ls β w n N E ≤
        ((ECell.rcpt γ e q k).add d).mass ls β w (Max.max n (k + 1)) N E := fun w => by
      have h1 : ftot (((ECell.rcpt γ e q k').add d).tg w) n ≤
          ftot (((ECell.rcpt γ e q k).add d).tg w) (Max.max n (k + 1)) := by
        rw [ECell.ftot_tg_add, ECell.ftot_tg_add, ECell.ftot_rcpt_tg, ECell.ftot_rcpt_tg]
        have := ftot_mono (d.tg w) (Nat.le_max_left n (k + 1)); grind
      have h2 := gsum_le (f := fun γ₁ e₁ => cwt ls w β γ₁ e₁ (((ECell.rcpt γ e q k').add d).rc γ₁ e₁) n)
        (g := fun γ₁ e₁ => cwt ls w β γ₁ e₁ (((ECell.rcpt γ e q k).add d).rc γ₁ e₁) (Max.max n (k + 1)))
        (fun γ₁ e₁ => cwt_le_of_ftot (by
          rw [ECell.ftot_rc_add, ECell.ftot_rc_add, ECell.ftot_rcpt, ECell.ftot_rcpt]
          have := ftot_mono (d.rc γ₁ e₁) (Nat.le_max_left n (k + 1)); have := q.nonneg
          simp only [show k < Max.max n (k + 1) by omega, and_true]
          split <;> split <;> grind)) N E
      simp only [ECell.mass]; grind
    exact ⟨Rat.le_trans (hm none) hb.1, fun γ₁ e₁ h1 h2 ha => Rat.le_trans (hm _) (hb.2 γ₁ e₁ h1 h2 ha)⟩
  · -- the receipt at `k'` is covered by the one at `k`
    left
    rcases hj with ⟨u, -, hp⟩ | ⟨γ₁, e₁, hl, hp⟩
    · rw [ECell.rcpt_tg] at hp; simp at hp
    · rw [ECell.rcpt_rc_val] at hp
      split at hp
      · rename_i hx; obtain ⟨rfl, rfl, rfl⟩ := hx
        exact ⟨k, h, .inr ⟨γ₁, e₁, hl, by rw [ECell.rcpt_rc_val]; simp [hq]⟩⟩
      · simp at hp
  · refine ⟨by simp, ?_⟩
    rw [ECell.rcpt_rc_val]
    split
    · rename_i hx; obtain ⟨rfl, rfl, -⟩ := hx
      have := (hf γ₁ e₁ k hfu).2; rw [ECell.rcpt_rc_val] at this; simp at this; grind
    · rfl
  · refine ⟨by simp, ?_⟩
    rw [ECell.rcpt_rc_val]
    split
    · rename_i hx; obtain ⟨rfl, rfl, -⟩ := hx
      have := (hz e₁ k).2; rw [ECell.rcpt_rc_val] at this; simp at this; grind
    · rfl

/-- **Join two receipts** of one tag at the lower bound (`EUpd.rweaken`, `brcpt_split`): a
grant's receipt that was split, part returned and lent again at another bound, is one receipt
again. -/
theorem EUpd.rjoin {q₁ q₂ : Frac} {k₁ k₂ : Nat} :
    EUpd (brcpt b q₁ k₁ γ e ⋆ brcpt b q₂ k₂ γ e) (brcpt b (q₁.add q₂) (Min.min k₁ k₂) γ e) :=
  EUpd.trans (EUpd.frame (EUpd.rweaken (Nat.min_le_left k₁ k₂)))
    (EUpd.trans (EUpd.frameL (EUpd.rweaken (Nat.min_le_right k₁ k₂)))
      (EUpd.of_imp fun r h => by
        obtain ⟨r₁, r₂, -, -, h1, h2⟩ := id h
        exact (brcpt_split h1.1 h2.1).mpr h))

/-- **Give a tagged share back** against a receipt at any bound: the share is weakened to the
receipt's bound first (`EUpd.weaken`, `EUpd.returnT`). -/
theorem EUpd.returnTw :
    EUpd (gauthP γ e M p ⋆ (bshare b q k' (some (γ, e)) ⋆ brcpt b q k γ e))
      (gauthP γ e M p ⋆ bshare b q k p) :=
  EUpd.trans (EUpd.frameL (EUpd.frame (EUpd.weaken (Nat.min_le_left k' k))))
    (EUpd.returnT (Nat.min_le_right k' k))

end Tags

/-! ## Triple rules -/

namespace CTriple

variable {Tgt α : Type} {P P' : FAssn} {x : ConcM Tgt α} {Q Q' : α → FAssn}

theorem eupd (hu : EUpd P P') (ht : CTriple P' x Q) : CTriple P x Q := fun n => FTriple.eupd hu (ht n)

theorem eupd_post (ht : CTriple P x Q) (hu : ∀ v, EUpd (Q v) (Q' v)) : CTriple P x Q' :=
  fun n => FTriple.eupd_post (ht n) hu

end CTriple

end Full
end Zig
