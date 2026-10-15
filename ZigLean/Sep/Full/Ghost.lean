import ZigLean.Sep.Full.Triple

/-!
# Ghost epoch ledgers of named grants (`docs/sep-full-state.md` §Ghost state)

A ghost name `γ` holds a ledger: an authority `gauth γ e M` (the current epoch `e` and the grant
map `M`: grant id ↦ the region granted under it) and tokens `gfrag γ e i g` (grant `i` of epoch
`e`, naming region `g`). Ghost state lives only in resources (`Res.gh`); no primitive reads or
changes it, and `Holds` requires the ghost states of a resource and its frame to compose
(`Ghost.Ok`). It changes only by **frame-preserving updates** (`Upd`), applied to a triple's pre-
or postcondition (`FTriple.upd`, `FTriple.upd_post`):

* `Upd.alloc p`: a new ledger `gauthP γ 0 GMap.empty p` with parent tag `p`, at a name no frame
  uses;
* `Upd.issue`: a new grant under an unused id, and its token;
* `Upd.retire`: a token of the current epoch given back, its grant removed;
* `Upd.reassign`: a grant of the current epoch re-pointed at another region (resize in place);
* `Upd.bump`: the next epoch with no grant, every outstanding token stale (revocation without
  collection), and every share tagged with the old epoch or a tag below it dormant.

A ledger's parent tag (`gauthP γ e M p`; `gauth γ e M` is the ledger without parent) places it in
the tree of tags (`docs/sep-full-state.md` §Nested tags): its tags are lent from shares tagged `p`
and are active only while `p` is. `Ghost.valid_led_change` is the one lemma behind every change of
ledger statuses.

A token of the current epoch names a grant that the map records (`gfrag_mem`, `FTriple.mem`), so
a token proves that this allocator granted exactly that region in its current epoch.

A stale token stays valid but is useless: an invariant indexed by the epoch (`own e`) needs the
authority of its epoch, which is exclusive.
-/

namespace Zig
namespace Full

open FAssn

/-! ## Ledger cells -/

namespace GCell

open Classical in
/-- The authority `●(e, M)` of a ledger with parent tag `p`. -/
noncomputable def auth1 (e : Nat) (M : GMap) (p : STag) : GCell :=
  ⟨fun x => if x = (e, M, p) then 1 else 0, fun _ => 0, fun _ => Frac.zero⟩

/-- The token `◯(e, i ↦ g)`. -/
def frag1 (e i : Nat) (g : GRegion) : GCell :=
  ⟨fun _ => 0, fun t => if t = (e, i, g) then 1 else 0, fun _ => Frac.zero⟩

/-- The part `q` of epoch `e`'s token. -/
def ep1 (e : Nat) (q : Frac) : GCell := ⟨fun _ => 0, fun _ => 0, fun e' => if e' = e then q else Frac.zero⟩

@[simp] theorem auth1_ep_val (e : Nat) (M : GMap) (p : STag) (e' : Nat) : ((auth1 e M p).ep e').val = 0 := rfl

@[simp] theorem frag1_ep_val (e i : Nat) (g : GRegion) (e' : Nat) : ((frag1 e i g).ep e').val = 0 := rfl

theorem auth1_add_ep (e : Nat) (M : GMap) (p : STag) (d : GCell) : ((auth1 e M p).add d).ep = d.ep :=
  funext fun _ => Frac.zero_add _

theorem valid_auth1_add {e : Nat} {M : GMap} {p : STag} {d : GCell} :
    ((auth1 e M p).add d).Valid ↔
      (∀ x, d.auth x = 0) ∧ d.TokOk e M ∧ (∀ e' i g, e < e' → d.frag (e', i, g) = 0) ∧ d.EpOk e := by
  constructor
  · rintro (h | ⟨e', M', p', h1, h2, h3, h4, h5, h6⟩)
    · have := h (e, M, p); simp [add, auth1] at this
    · by_cases hx : (e', M', p') = (e, M, p)
      · simp only [Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl, rfl⟩ := hx
        refine ⟨fun x => ?_, fun i g => by simpa [add, auth1] using h3 i g,
          fun e'' i g he => by simpa [add, auth1] using h4 e'' i g he,
          fun e'' => by rw [auth1_add_ep] at h5; exact h5 e'',
          fun e'' he => by rw [auth1_add_ep] at h6; exact h6 e'' he⟩
        by_cases hx' : x = (e', M', p')
        · subst hx'; simp [add, auth1] at h1; omega
        · have := h2 x hx'; simp [add, auth1, hx'] at this; omega
      · have := h2 (e, M, p) (Ne.symm hx); simp [add, auth1] at this
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine .inr ⟨e, M, p, by simp [add, auth1, h1], fun x hx => by simp [add, auth1, hx, h1],
      fun i g => by simpa [add, auth1] using h2 i g, fun e' i g he => by simpa [add, auth1] using h3 e' i g he,
      fun e' => by rw [auth1_add_ep]; exact h4 e', fun e' he => by rw [auth1_add_ep]; exact h5 e' he⟩

theorem frag1_add (e i : Nat) (g : GRegion) (d : GCell) :
    (frag1 e i g).add d = ⟨d.auth, fun t => (if t = (e, i, g) then 1 else 0) + d.frag t, d.ep⟩ := by
  ext
  · simp [add, frag1]
  · simp [add, frag1]
  · simp only [add, frag1, Frac.zero_add]

/-- The statuses of a ledger cell with the authority `●(e, M)` under parent `p`: `(e, p)` and the
frame's. -/
theorem ls_auth1_add {e x : Nat} {M : GMap} {p q : STag} {d : GCell} :
    (∃ N, 0 < ((auth1 e M p).add d).auth (x, N, q)) ↔ (x = e ∧ q = p) ∨ ∃ N, 0 < d.auth (x, N, q) := by
  constructor
  · rintro ⟨N, h⟩
    simp only [add, auth1] at h
    by_cases hx : (x, N, q) = (e, M, p)
    · simp only [Prod.mk.injEq] at hx; exact .inl ⟨hx.1, hx.2.2⟩
    · rw [if_neg hx] at h; exact .inr ⟨N, by omega⟩
  · rintro (⟨rfl, rfl⟩ | ⟨N, h⟩)
    · exact ⟨M, by simp only [add, auth1, ↓reduceIte]; omega⟩
    · exact ⟨N, by simp only [add]; omega⟩

theorem frag1_add_auth (e i : Nat) (g : GRegion) (d : GCell) :
    ((frag1 e i g).add d).auth = d.auth := by
  funext x; simp [add, frag1]

@[simp] theorem ep1_ep_val (e : Nat) (q : Frac) (e' : Nat) :
    ((ep1 e q).ep e').val = if e' = e then q.val else 0 := by
  simp only [ep1]; split <;> rfl

theorem ep1_add (e : Nat) (q q' : Frac) : (ep1 e q).add (ep1 e q') = ep1 e (q.add q') := by
  ext
  · simp [add, ep1]
  · simp [add, ep1]
  · simp only [add, ep1]; split <;> simp

@[simp] theorem ep1_zero (e : Nat) : ep1 e Frac.zero = unit := by
  ext <;> simp [ep1, unit]

end GCell

/-! ## Ghost states with one name -/

/-- The ghost state with cell `c` at `γ` and nothing elsewhere. -/
def Ghost.at (γ : Nat) (c : GCell) : Ghost :=
  ⟨fun γ' => if γ' = γ then c else GCell.unit, fun _ => ECell.unit, fun _ _ => ECell.unit, ACell.unit⟩

@[simp] theorem Ghost.at_ac (γ : Nat) (c : GCell) : (Ghost.at γ c).ac = ACell.unit := rfl

theorem Ghost.at_add (γ : Nat) (c c' : GCell) : (Ghost.at γ c).add (Ghost.at γ c') = Ghost.at γ (c.add c') := by
  ext1
  · funext γ'; simp only [Ghost.add, Ghost.at]; split <;> simp
  · funext b; simp [Ghost.add, Ghost.at]
  · funext b x; simp [Ghost.add, Ghost.at]
  · simp

@[simp] theorem Ghost.at_unit (γ : Nat) : Ghost.at γ GCell.unit = Ghost.unit := by
  ext1 <;> (try funext x) <;> (try funext y) <;> simp [Ghost.at, Ghost.unit]

/-- Epoch tokens change no ledger status. -/
@[simp] theorem Ghost.ls_at_ep_add (γ e : Nat) (q : Frac) (g : Ghost) :
    ((Ghost.at γ (GCell.ep1 e q)).add g).ls = g.ls := by
  funext γ' x p
  simp only [Ghost.ls, Ghost.add, Ghost.at]
  split <;> simp [GCell.add, GCell.ep1, GCell.unit]

@[simp] theorem Ghost.at_cl (γ : Nat) (c : GCell) : (Ghost.at γ c).cl = fun _ _ => ECell.unit := rfl

theorem Ghost.at_add_cl (γ : Nat) (c : GCell) (g : Ghost) : ((Ghost.at γ c).add g).cl = g.cl := by
  funext b x; simp

theorem Ghost.at_add_ac (γ : Nat) (c : GCell) (g : Ghost) : ((Ghost.at γ c).add g).ac = g.ac := by
  simp

/-- The statuses next to an authority `●(e₀, M₀)` with parent `p₀` at `γ₀`, whose frame `g` holds
no authority at `γ₀`. -/
theorem Ghost.ls_at_add {γ₀ e₀ : Nat} {M₀ : GMap} {p₀ : STag} {g : Ghost}
    (h0 : ∀ x, (g.led γ₀).auth x = 0) {γ e : Nat} {p : STag} :
    ((Ghost.at γ₀ (GCell.auth1 e₀ M₀ p₀)).add g).ls γ e p ↔ (γ = γ₀ ∧ e = e₀ ∧ p = p₀) ∨
      (γ ≠ γ₀ ∧ g.ls γ e p) := by
  by_cases hγ : γ = γ₀
  · subst hγ
    simp only [Ghost.ls, Ghost.add, Ghost.at, ↓reduceIte]
    rw [GCell.ls_auth1_add]; simp [h0]
  · simp [Ghost.ls, Ghost.add, Ghost.at, hγ]

/-- `Ghost.ls_at_add` with an epoch token next to the authority (a new ledger or epoch). -/
theorem Ghost.ls_at_ep_add' {γ₀ e₀ e₁ : Nat} {M₀ : GMap} {p₀ : STag} {q : Frac} {g : Ghost}
    (h0 : ∀ x, (g.led γ₀).auth x = 0) {γ e : Nat} {p : STag} :
    ((Ghost.at γ₀ ((GCell.auth1 e₀ M₀ p₀).add (GCell.ep1 e₁ q))).add g).ls γ e p ↔
      (γ = γ₀ ∧ e = e₀ ∧ p = p₀) ∨ (γ ≠ γ₀ ∧ g.ls γ e p) := by
  rw [← Ghost.at_add, Ghost.add_assoc,
    Ghost.ls_at_add (fun x => by simp [Ghost.add, Ghost.at, GCell.add, GCell.ep1, h0 x]), Ghost.ls_at_ep_add]

/-! ## Changes of the ledgers -/

/-- **A change of the ledger statuses** from `ls` to `ls'` keeps one cell balanced (the per-cell
part of `Ghost.valid_led_change`, for extent cells and byte-claim cells alike). -/
theorem ECell.tagOk_led_change {ls ls' : LStat} (Z : STag → Prop) {c : ECell} (hc : c.TagOk ls)
    (hu' : ls'.Uniq)
    (hZ : ∀ γ e, Z (some (γ, e)) → ∀ k, (c.tsh γ e k).val = 0 ∧ (c.rc γ e k).val = 0)
    (hZn : ¬ Z none) (hZc : ∀ w γ e e', Z w → ls' γ e' w → e ≤ e' → Z (some (γ, e)))
    (hA : ∀ t, Act ls' t → Act ls t ∨ Z t) (hF : ∀ t, Fut ls' t → Fut ls t ∨ Z t)
    (hC : ∀ w γ e, Act ls' w → ¬ Z w → ¬ Z (some (γ, e)) → (∃ e', e ≤ e' ∧ ls' γ e' w) →
      (∃ e', e ≤ e' ∧ ls γ e' w) ∧ (ls' γ e w → ls γ e w)) :
    c.TagOk ls' := by
  have hZt : ∀ t, Z t → ∀ k, (c.tg t k).val = 0 := fun t ht k => by
    rcases t with _ | ⟨γ, e⟩
    · exact absurd ht hZn
    · exact (hZ γ e ht k).1
  classical
  let β' : (Nat → Nat → Rat) → Nat → Nat → Rat := fun β γ e => if Z (some (γ, e)) then 0 else β γ e
  have hcwZ : ∀ β w γ e n, Z (some (γ, e)) → cwt ls' w (β' β) γ e (c.rc γ e) n ≤ 0 :=
    fun β w γ e n hz => by
      have h0 : ftot (c.rc γ e) n = 0 := ftot_zero (fun k => (hZ γ e hz k).2) n
      have hb : β' β γ e = 0 := by simp [β', hz]
      unfold cwt; rw [h0, hb]; split
      · grind
      · split <;> grind
  have hmZ : ∀ β w n N E, Z w → c.mass ls' (β' β) w n N E ≤ 0 := fun β w n N E hw => by
    have h1 : ftot (c.tg w) n = 0 := ftot_zero (hZt w hw) n
    have h2 := gsum_zero (f := fun γ e => cwt ls' w (β' β) γ e (c.rc γ e) n)
      (fun γ e => by
        by_cases hze : Z (some (γ, e))
        · exact hcwZ β w γ e n hze
        · unfold cwt
          rw [if_neg (fun h => hze (hZc w γ e e hw h (Nat.le_refl _))),
            if_neg (fun ⟨e', he, h⟩ => hze (hZc w γ e e' hw h (Nat.le_of_lt he)))]
          exact Rat.le_refl) N E
    simp only [ECell.mass]; grind
  have hmW : ∀ β w n N E, Act ls' w → ¬ Z w → c.mass ls' (β' β) w n N E ≤ c.mass ls β w n N E :=
    fun β w n N E hw hz => by
      have := gsum_le (f := fun γ e => cwt ls' w (β' β) γ e (c.rc γ e) n)
        (g := fun γ e => cwt ls w β γ e (c.rc γ e) n) (fun γ e => by
          by_cases hze : Z (some (γ, e))
          · exact Rat.le_trans (hcwZ β w γ e n hze) (cwt_nonneg _ _ _ _ _ _ _)
          · have hb : β' β γ e = β γ e := by simp [β', hze]
            unfold cwt
            by_cases h1 : ls' γ e w
            · have := (hC w γ e hw hz hze ⟨e, Nat.le_refl _, h1⟩).2 h1
              rw [if_pos h1, if_pos this, hb]; exact Rat.le_refl
            · rw [if_neg h1]
              split
              · rename_i h2
                obtain ⟨e', he, h2⟩ := h2
                have := (hC w γ e hw hz hze ⟨e', Nat.le_of_lt he, h2⟩).1
                exact cwt_ge_R this
              · exact cwt_nonneg _ _ _ _ _ _ _) N E
      simp only [ECell.mass]; grind
  obtain ⟨hbal, hf⟩ := hc
  refine ⟨fun n N E => ?_, fun γ e k hfu => ?_⟩
  · obtain ⟨β, h1, h2⟩ := hbal n N E
    refine ⟨β' β, Rat.le_trans (hmW β none n N E .root hZn) h1, fun γ e hγ he ha => ?_⟩
    by_cases hz : Z (some (γ, e))
    · have := hmZ β _ n N E hz; simp only [β', hz, ↓reduceIte]; exact this
    · have hb : β' β γ e = β γ e := by simp [β', hz]
      rw [hb]
      exact Rat.le_trans (hmW β _ n N E ha hz) (h2 γ e hγ he ((hA _ ha).resolve_right hz))
  · rcases hF _ hfu with h | h
    · exact hf γ e k h
    · exact hZ γ e h k

/-- **A change of the ledgers** (statuses `G.ls` to `G'.ls`, same extent claims) keeps validity and
the truth of every claim. `Z` is a set of tags without claims, closed under children (under the new
statuses); every tag that the change makes active or future is in `Z` or was so before; and a child
tag outside `Z` of a world that stays active keeps a status as live as before (current stays
current, live stays live). A bump (`Upd.bump`: `Z` the future tags) turns the old epoch and every
tag below it dormant at once; a new ledger (`Upd.alloc`: `Z` also its name) adds an empty tree. -/
theorem Ghost.valid_led_change {G G' : Ghost} (Z : STag → Prop) (hx : G'.extent = G.extent)
    (hcl : G'.cl = G.cl) (hcr : G'.ac = G.ac) (hv : G.Valid) (hlv : ∀ γ, (G'.led γ).Valid)
    (hZ : ∀ γ e, Z (some (γ, e)) → ∀ b k, ((G.extent b).tsh γ e k).val = 0 ∧ ((G.extent b).rc γ e k).val = 0)
    (hZcl : ∀ γ e, Z (some (γ, e)) → ∀ b x k, ((G.cl b x).tsh γ e k).val = 0 ∧ ((G.cl b x).rc γ e k).val = 0)
    (hZn : ¬ Z none) (hZc : ∀ w γ e e', Z w → G'.ls γ e' w → e ≤ e' → Z (some (γ, e)))
    (hA : ∀ t, Act G'.ls t → Act G.ls t ∨ Z t) (hF : ∀ t, Fut G'.ls t → Fut G.ls t ∨ Z t)
    (hC : ∀ w γ e, Act G'.ls w → ¬ Z w → ¬ Z (some (γ, e)) → (∃ e', e ≤ e' ∧ G'.ls γ e' w) →
      (∃ e', e ≤ e' ∧ G.ls γ e' w) ∧ (G'.ls γ e w → G.ls γ e w)) :
    G'.Valid ∧ ∀ m, ExtTrue m G → ExtTrue m G' := by
  have hZt : ∀ t, Z t → ∀ b k, ((G.extent b).tg t k).val = 0 := fun t ht b k => by
    rcases t with _ | ⟨γ, e⟩
    · exact absurd ht hZn
    · exact (hZ γ e ht b k).1
  have hu' : G'.ls.Uniq := fun γ e e' p p' ⟨_, h1⟩ ⟨_, h2⟩ => (hlv γ).ls_uniq h1 h2
  refine ⟨⟨hlv, fun b => ?_, ⟨fun b x => ?_, ?_⟩, by rw [hcr]; exact hv.2.2.2⟩, fun m ht b => ?_⟩
  · rw [hx]
    obtain ⟨hvb, hbal⟩ := hv.2.1 b
    exact ⟨hvb, ECell.tagOk_led_change Z hbal hu' (fun γ e hz k => hZ γ e hz b k) hZn hZc hA hF hC⟩
  · rw [hcl]
    obtain ⟨hvb, hbal⟩ := hv.2.2.1.1 b x
    exact ⟨hvb, ECell.tagOk_led_change Z hbal hu' (fun γ e hz k => hZcl γ e hz b x k) hZn hZc hA hF hC⟩
  · rw [hcl]; exact hv.2.2.1.2
  · obtain ⟨ha, hs⟩ := ht b
    rw [hx]
    refine ⟨ha, fun k hk => hs k ?_⟩
    rcases hk with ⟨t, hact, hp⟩ | ⟨γ, e, ⟨w, e', hee, hls, hw⟩, hp⟩
    · rcases hA t hact with h | h
      · exact .inl ⟨t, h, hp⟩
      · rw [hZt t h b k] at hp; exact absurd hp Rat.lt_irrefl
    · by_cases hzw : Z w
      · rw [(hZ γ e (hZc w γ e e' hzw hls hee) b k).2] at hp; exact absurd hp Rat.lt_irrefl
      by_cases hze : Z (some (γ, e))
      · rw [(hZ γ e hze b k).2] at hp; exact absurd hp Rat.lt_irrefl
      obtain ⟨⟨e'', h1, h2⟩, -⟩ := hC w γ e hw hzw hze ⟨e', hee, hls⟩
      exact .inr ⟨γ, e, ⟨w, e'', h1, h2, (hA w hw).resolve_right hzw⟩, hp⟩

theorem ExtTrue.congr {m : Mem} {G G' : Ghost} (hx : G'.extent = G.extent)
    (hls : G'.ls = G.ls) (h : ExtTrue m G) : ExtTrue m G' := fun b => by
  rw [hx, hls]; exact h b

/-- **A local update** at one name: if every cell that `c` composes validly with also composes
validly with `c'`, with the same statuses, replacing `c` by `c'` keeps every frame valid and every
extent claim true. -/
theorem Ghost.Ok.update {γ : Nat} {c c' : GCell} {g : Ghost}
    (h : ∀ d, (c.add d).Valid → (c'.add d).Valid ∧
      ∀ e p, (∃ M, 0 < (c'.add d).auth (e, M, p)) ↔ (∃ M, 0 < (c.add d).auth (e, M, p)))
    (hok : Ghost.Ok (Ghost.at γ c) g) :
    Ghost.Ok (Ghost.at γ c') g ∧
      ∀ m, ExtTrue m ((Ghost.at γ c).add g) → ExtTrue m ((Ghost.at γ c').add g) := by
  obtain ⟨hv, N, hN⟩ := hok
  have hc := h (g.led γ) (by simpa [Ghost.add, Ghost.at] using hv.1 γ)
  have hx : ((Ghost.at γ c').add g).extent = ((Ghost.at γ c).add g).extent := by
    funext b; simp [Ghost.add, Ghost.at]
  have hcl : ((Ghost.at γ c').add g).cl = ((Ghost.at γ c).add g).cl := by
    rw [Ghost.at_add_cl, Ghost.at_add_cl]
  have hl : ∀ γ', γ' ≠ γ → ((Ghost.at γ c').add g).led γ' = ((Ghost.at γ c).add g).led γ' :=
    fun γ' hne => by simp [Ghost.add, Ghost.at, hne]
  have hep : ∀ γ' x p, ((Ghost.at γ c').add g).ls γ' x p ↔ ((Ghost.at γ c).add g).ls γ' x p := by
    intro γ' x p
    by_cases hne : γ' = γ
    · subst hne; simpa [Ghost.ls, Ghost.add, Ghost.at] using hc.2 x p
    · unfold Ghost.ls; rw [hl γ' hne]
  have e : ((Ghost.at γ c').add g).ls = ((Ghost.at γ c).add g).ls :=
    funext fun γ' => funext fun x => funext fun p => propext (hep γ' x p)
  refine ⟨⟨⟨fun γ' => ?_, fun b => ?_, hv.2.2.1.congr hcl e,
      by rw [Ghost.at_add_ac]; simpa using hv.2.2.2⟩, N + γ + 1,
    fun γ' hγ => ⟨?_, ?_, fun γ'' e' M e₀ => ?_⟩⟩, fun m ht => ExtTrue.congr hx e ht⟩
  · by_cases hne : γ' = γ
    · subst hne; simpa [Ghost.add, Ghost.at] using hc.1
    · rw [hl γ' hne]; exact hv.1 γ'
  · rw [hx, e]; exact hv.2.1 b
  · have := (hN γ' (by omega)).1
    rw [hl γ' (by omega)]; exact this
  · rw [hx]; exact (hN γ' (by omega)).2.1
  · refine Nat.eq_zero_of_not_pos fun hp => ?_
    obtain ⟨M', hM'⟩ := (hep γ'' e' (some (γ', e₀))).mp ⟨M, hp⟩
    have := (hN γ' (by omega)).2.2 γ'' e' M' e₀
    omega

/-! ## Grant maps -/

namespace GMap

/-- No grant. -/
def empty : GMap := fun _ => none

/-- `M` with grant `i` set to `v`. -/
def set (M : GMap) (i : Nat) (v : Option GRegion) : GMap := fun j => if j = i then v else M j

@[simp] theorem set_same (M : GMap) (i : Nat) (v : Option GRegion) : M.set i v i = v := by
  simp [set]

theorem set_ne (M : GMap) {i j : Nat} (v : Option GRegion) (h : j ≠ i) : M.set i v j = M j := by
  simp [set, h]

@[simp] theorem set_set (M : GMap) (i : Nat) (v v' : Option GRegion) :
    (M.set i v).set i v' = M.set i v' := by
  funext j; simp only [set]; split <;> rfl

/-- Finitely many grants, so a fresh id exists (`Fin.fresh`). -/
def Fin (M : GMap) : Prop := ∃ N, ∀ i, N ≤ i → M i = none

theorem Fin.fresh {M : GMap} (h : M.Fin) : ∃ i, M i = none := by
  obtain ⟨N, hN⟩ := h; exact ⟨N, hN N (Nat.le_refl _)⟩

theorem Fin.set {M : GMap} (h : M.Fin) (i : Nat) (v : Option GRegion) : (M.set i v).Fin := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N + i + 1, fun j hj => ?_⟩
  rw [set_ne _ _ (by omega)]; exact hN j (by omega)

theorem empty_fin : empty.Fin := ⟨0, fun _ _ => rfl⟩

end GMap

/-! ## Assertions -/

/-- The authority of ledger `γ`: epoch `e`, grant map `M`, parent tag `p` (the tag of the shares
the ledger's tags are lent from, `docs/sep-full-state.md` §Nested tags). Owns no bytes, no
knowledge. -/
def gauthP (γ e : Nat) (M : GMap) (p : STag) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.at γ (GCell.auth1 e M p)

/-- The authority of a ledger without parent (its tags are lent from untagged shares). -/
abbrev gauth (γ e : Nat) (M : GMap) : FAssn := gauthP γ e M none

/-- A token of ledger `γ`: grant `i` of epoch `e`, naming region `g`. -/
def gfrag (γ e i : Nat) (g : GRegion) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.at γ (GCell.frag1 e i g)

/-- The resource of `gauthP γ e M p ⋆ gfrag γ e i g`. -/
theorem gauth_gfrag {γ e i : Nat} {M : GMap} {p : STag} {g : GRegion} {r : Res}
    (h : (gauthP γ e M p ⋆ gfrag γ e i g) r) :
    r = ⟨FHeap.empty, Know.none, Ghost.at γ ((GCell.auth1 e M p).add (GCell.frag1 e i g))⟩ := by
  obtain ⟨r₁, r₂, -, rfl, ⟨h1, k1, g1⟩, ⟨h2, k2, g2⟩⟩ := h
  rw [h1, h2, k1, k2, g1, g2, FHeap.union_empty, Know.union_none, Ghost.at_add]

theorem gauth_gfrag_intro {γ e i : Nat} {M : GMap} {p : STag} {g : GRegion} :
    (gauthP γ e M p ⋆ gfrag γ e i g)
      ⟨FHeap.empty, Know.none, Ghost.at γ ((GCell.auth1 e M p).add (GCell.frag1 e i g))⟩ :=
  ⟨⟨FHeap.empty, Know.none, Ghost.at γ (GCell.auth1 e M p)⟩,
    ⟨FHeap.empty, Know.none, Ghost.at γ (GCell.frag1 e i g)⟩, FHeap.disjoint_empty _,
    by rw [FHeap.union_empty, Know.union_none, Ghost.at_add], ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-! ### Epoch tokens (`docs/sep-full-state.md` §Epoch tokens)

Each epoch of a ledger has one whole token, minted with the epoch (`Upd.alloc`, `Upd.bump`). Its
parts split and join (`epTok_add`). Next to the ledger's authority of epoch `e`, the parts of
epoch `e'`'s token held anywhere add up to at most one, and to nothing for `e' > e`
(`GCell.EpOk`): so whoever holds the whole token knows that nobody else holds a part of it
(`gauth_epTok_le`, `gauth_epTok_whole`). An allocator that takes a part of the token with each
grant and gives it back with the grant (an arena's fee, `FAllocInv.fee`) learns from the whole
token that no grant is outstanding. -/

/-- The part `q` of ledger `γ`'s token of epoch `e`. Owns no bytes, no knowledge. -/
def epTok (γ e : Nat) (q : Frac) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.at γ (GCell.ep1 e q)

/-- Parts of an epoch token split and join: an equality. -/
theorem epTok_add (γ e : Nat) (q q' : Frac) : epTok γ e (q.add q') = (epTok γ e q ⋆ epTok γ e q') := by
  funext r; apply propext; constructor
  · rintro ⟨h, k, g⟩
    exact ⟨⟨FHeap.empty, Know.none, Ghost.at γ (GCell.ep1 e q)⟩,
      ⟨FHeap.empty, Know.none, Ghost.at γ (GCell.ep1 e q')⟩, FHeap.disjoint_empty _,
      by rw [res_eta r, h, k, g, ← GCell.ep1_add, ← Ghost.at_add]; simp [Know.union_none],
      ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
  · rintro ⟨r₁, r₂, -, rfl, ⟨h1, k1, g1⟩, ⟨h2, k2, g2⟩⟩
    exact ⟨by simp [h1, h2], by simp [k1, k2, Know.union_none], by simp [g1, g2, Ghost.at_add, GCell.ep1_add]⟩

theorem epTok_zero (γ e : Nat) : epTok γ e Frac.zero = emp := by
  funext r; simp [epTok, emp]

/-- The resource of `gauthP γ e M p ⋆ epTok γ e' q`. -/
theorem gauth_epTok {γ e e' : Nat} {M : GMap} {p : STag} {q : Frac} {r : Res}
    (h : (gauthP γ e M p ⋆ epTok γ e' q) r) :
    r = ⟨FHeap.empty, Know.none, Ghost.at γ ((GCell.auth1 e M p).add (GCell.ep1 e' q))⟩ := by
  obtain ⟨r₁, r₂, -, rfl, ⟨h1, k1, g1⟩, ⟨h2, k2, g2⟩⟩ := h
  rw [h1, h2, k1, k2, g1, g2, FHeap.union_empty, Know.union_none, Ghost.at_add]

theorem gauth_epTok_intro {γ e e' : Nat} {M : GMap} {p : STag} {q : Frac} :
    (gauthP γ e M p ⋆ epTok γ e' q)
      ⟨FHeap.empty, Know.none, Ghost.at γ ((GCell.auth1 e M p).add (GCell.ep1 e' q))⟩ :=
  ⟨⟨FHeap.empty, Know.none, Ghost.at γ (GCell.auth1 e M p)⟩,
    ⟨FHeap.empty, Know.none, Ghost.at γ (GCell.ep1 e' q)⟩, FHeap.disjoint_empty _,
    by rw [FHeap.union_empty, Know.union_none, Ghost.at_add], ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-- **An epoch token is at most whole**: next to its ledger's authority of epoch `e`, a part `q` of
epoch `e'`'s token, in a ghost state that composes with a frame, is at most one, and nothing for a
later epoch. -/
theorem gauth_epTok_le {γ e e' : Nat} {M : GMap} {p : STag} {q : Frac} {r : Res} {gF : Ghost}
    (h : (gauthP γ e M p ⋆ epTok γ e' q) r) (hg : Ghost.Ok r.gh gF) :
    q.val ≤ 1 ∧ (e < e' → q.val = 0) := by
  rw [gauth_epTok h] at hg
  have hv := hg.1.1 γ
  simp only [Ghost.add, Ghost.at, ↓reduceIte] at hv
  rw [GCell.add_assoc, GCell.valid_auth1_add] at hv
  obtain ⟨-, -, -, h1, h2⟩ := hv
  have a := h1 e'
  have := ((gF.led γ).ep e').nonneg
  have := q.nonneg
  simp only [GCell.add_ep_val, GCell.ep1_ep_val, ↓reduceIte] at a
  refine ⟨by grind, fun he => ?_⟩
  have b := h2 e' he
  simp only [GCell.add_ep_val, GCell.ep1_ep_val, ↓reduceIte] at b; grind

/-- **The whole epoch token excludes every other part of it**: next to the ledger's authority, the
whole token of epoch `e'` and a part `q` of it, in a ghost state that composes with a frame, leave
`q` empty. -/
theorem gauth_epTok_whole {γ e e' : Nat} {M : GMap} {p : STag} {q : Frac} {r : Res} {gF : Ghost}
    (h : (gauthP γ e M p ⋆ (epTok γ e' Frac.one ⋆ epTok γ e' q)) r) (hg : Ghost.Ok r.gh gF) :
    q.val = 0 := by
  rw [← epTok_add] at h
  have hle := (gauth_epTok_le h hg).1
  have := q.nonneg
  simp only [Frac.add, Frac.one] at hle
  grind

/-! ## Frame-preserving updates -/

/-- `P` can become `P'` by a ghost update: every resource of `P` is replaced, with the same bytes,
knowledge, extent claims and counter cell, by one of `P'` that composes with every ghost frame the
old one composed with, and under whose ledgers every extent claim that was true stays true. (The
counter cell changes only with the memory's consent: `EUpd`.) -/
def Upd (P P' : FAssn) : Prop :=
  ∀ r, P r → ∀ g, Ghost.Ok r.gh g →
    ∃ r', P' r' ∧ r'.heap = r.heap ∧ r'.know = r.know ∧ r'.gh.extent = r.gh.extent ∧
      r'.gh.cl = r.gh.cl ∧ r'.gh.ac = r.gh.ac ∧ Ghost.Ok r'.gh g ∧
        ∀ m, ExtTrue m (r.gh.add g) → ExtTrue m (r'.gh.add g)

/-- What an authority `●(e, M)` and a token `◯(e, i ↦ g)` say about a frame `d` they compose
with: the map records the grant, and `d` holds no token for it. -/
theorem GCell.valid_pair {e i : Nat} {M : GMap} {p : STag} {g : GRegion} {d : GCell}
    (hv : ((GCell.auth1 e M p).add ((GCell.frag1 e i g).add d)).Valid) :
    (∀ x, d.auth x = 0) ∧ M i = some g ∧ d.frag (e, i, g) = 0 ∧ d.TokOk e M ∧
      (∀ e' j g', e < e' → d.frag (e', j, g') = 0) ∧ d.EpOk e := by
  rw [GCell.valid_auth1_add] at hv
  obtain ⟨h1, h2, h3, h4⟩ := hv
  rw [GCell.frag1_add] at h4
  simp only [GCell.TokOk, GCell.add, GCell.frag1] at h1 h2 h3
  have hi := h2 i g
  simp only [↓reduceIte] at hi
  refine ⟨fun x => by simpa using h1 x, hi.2 (by omega), by omega, fun j g' => ?_,
    fun e' j g' he => ?_, h4⟩
  · have := h2 j g'
    exact ⟨by omega, fun hp => this.2 (by omega)⟩
  · have := h3 e' j g' he; omega

/-- The name of a tag's ledger, plus one (`0` for the root). -/
def STag.name : STag → Nat
  | none => 0
  | some (γ, _) => γ + 1

namespace Upd

variable {P P' P'' R : FAssn}

theorem of_imp (h : ∀ r, P r → P' r) : Upd P P' := fun r hp _ hg =>
  ⟨r, h r hp, rfl, rfl, rfl, rfl, rfl, hg, fun _ h => h⟩

theorem trans (h₁ : Upd P P') (h₂ : Upd P' P'') : Upd P P'' := fun r hp g hg => by
  obtain ⟨r₁, h1, e1, k1, x1, c1, a1, g1, t1⟩ := h₁ r hp g hg
  obtain ⟨r₂, h2, e2, k2, x2, c2, a2, g2, t2⟩ := h₂ r₁ h1 g g1
  exact ⟨r₂, h2, e2.trans e1, k2.trans k1, x2.trans x1, c2.trans c1, a2.trans a1, g2,
    fun m h => t2 m (t1 m h)⟩

/-- Updates frame. -/
theorem frame (h : Upd P P') : Upd (P ⋆ R) (P' ⋆ R) := by
  rintro _ ⟨r₁, r₂, hd, rfl, hp, hr⟩ g hg
  obtain ⟨r₁', hp', e, k, x, xc, xa, hg', ht⟩ := h r₁ hp (r₂.gh.add g) (Ghost.Ok.assoc.mp hg)
  refine ⟨⟨r₁'.heap ∪ r₂.heap, r₁'.know.union r₂.know, r₁'.gh.add r₂.gh⟩,
    ⟨r₁', r₂, by rw [e]; exact hd, rfl, hp', hr⟩, by simp [e], by simp [k],
    by simp [Ghost.add, x], by simp [Ghost.add, xc], by simp [xa], Ghost.Ok.assoc.mpr hg', fun m hm => ?_⟩
  simp only [Ghost.add_assoc] at hm ⊢
  exact ht m hm

theorem frameL (h : Upd P P') : Upd (R ⋆ P) (R ⋆ P') :=
  trans (of_imp fun _ h => sep_comm h) (trans (frame h) (of_imp fun _ h => sep_comm h))

/-- A local update of a ghost-only resource at one name, with the same statuses. -/
theorem single {γ : Nat} {c c' : GCell} {P P' : FAssn}
    (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, Ghost.at γ c⟩)
    (hp' : P' ⟨FHeap.empty, Know.none, Ghost.at γ c'⟩)
    (h : ∀ d, (c.add d).Valid → (c'.add d).Valid ∧
      ∀ e p, (∃ M, 0 < (c'.add d).auth (e, M, p)) ↔ (∃ M, 0 < (c.add d).auth (e, M, p))) :
    Upd P P' := fun r hr g hg => by
  have e := hp r hr
  subst e
  obtain ⟨h1, h2⟩ := Ghost.Ok.update h hg
  exact ⟨_, hp', rfl, rfl, rfl, rfl, rfl, h1, h2⟩

/-- **A new ledger** with parent tag `p`, at a name no frame uses (no ledger, no tag, no parent
link), with no grant, and its epoch's whole token (`epTok`). Its tags are lent from shares tagged
`p` (`EUpd.lendT`) and die with `p`. -/
theorem alloc (p : STag) :
    Upd emp (FAssn.ex fun γ => gauthP γ 0 GMap.empty p ⋆ epTok γ 0 Frac.one) := by
  rintro r ⟨h0, k0, g0⟩ g hg
  rw [g0] at hg
  unfold Ghost.Ok at hg
  rw [Ghost.unit_add] at hg
  obtain ⟨hv, N, hN⟩ := hg
  obtain ⟨NC, hNC⟩ := hv.2.2.1.2
  let ν := N + NC + p.name
  have hνN : N ≤ ν := show N ≤ N + NC + p.name by omega
  have hNu := (hN ν hνN).1
  have hNt := (hN ν hνN).2.1
  have hNp := (hN ν hνN).2.2
  have hpν : ∀ e, p ≠ some (ν, e) := fun e he => by
    have h1 : p.name = ν + 1 := by rw [he]; rfl
    have h2 : ν = N + NC + p.name := rfl
    omega
  have h0ν : ∀ x, (g.led ν).auth x = 0 := fun x => by rw [hNu]; rfl
  let c' := (GCell.auth1 0 GMap.empty p).add (GCell.ep1 0 Frac.one)
  let G' := (Ghost.at ν c').add g
  have hx : G'.extent = g.extent := by funext b; simp [G', Ghost.add, Ghost.at]
  have hcl : G'.cl = g.cl := Ghost.at_add_cl _ _ _
  have hl : ∀ γ', γ' ≠ ν → G'.led γ' = g.led γ' := fun γ' hne => by
    simp [G', Ghost.add, Ghost.at, hne]
  have hlN : G'.led ν = c' := by simp [G', Ghost.add, Ghost.at, hNu]
  have hls : ∀ γ e q, G'.ls γ e q ↔ (γ = ν ∧ e = 0 ∧ q = p) ∨ (γ ≠ ν ∧ g.ls γ e q) :=
    fun γ e q => Ghost.ls_at_ep_add' h0ν
  -- no ledger names `ν` as its parent
  have hnoν : ∀ γ e e₀, ¬ g.ls γ e (some (ν, e₀)) := fun γ e e₀ ⟨M, h⟩ => by
    have := hNp γ e M e₀; omega
  let Z : STag → Prop := fun t => Fut g.ls t ∨ ∃ e, t = some (ν, e)
  obtain ⟨hv', ht'⟩ := Ghost.valid_led_change (G := g) (G' := G') Z hx hcl (Ghost.at_add_ac _ _ _) hv
    (fun γ => by
      by_cases h : γ = ν
      · subst h; rw [hlN]
        refine GCell.valid_auth1_add.mpr ⟨fun _ => rfl,
          fun _ _ => ⟨Nat.zero_le _, fun h => absurd h (Nat.lt_irrefl 0)⟩, fun _ _ _ _ => rfl,
          fun e' => ?_, fun e' he => ?_⟩
        · have : Frac.one.val = 1 := rfl
          simp only [GCell.ep1_ep_val]; split <;> grind
        · simp [show e' ≠ 0 by omega]
      · rw [hl γ h]; exact hv.1 γ)
    (fun γ e hz b k => by
      rcases hz with hz | ⟨e', he⟩
      · exact (hv.2.1 b).2.2 γ e k hz
      · cases he; exact hNt b e k)
    (fun γ e hz b x k => by
      rcases hz with hz | ⟨e', he⟩
      · exact (hv.2.2.1.1 b x).2.2 γ e k hz
      · cases he; exact hNC ν (show NC ≤ N + NC + p.name by omega) b x e k)
    (fun h => h.elim Fut.not_none fun ⟨_, h⟩ => nomatch h)
    (fun w γ e e' hw hl' hee => by
      rcases (hls γ e' w).mp hl' with ⟨rfl, -, rfl⟩ | ⟨hne, hl'⟩
      · exact .inr ⟨e, rfl⟩
      · rcases hw with hw | ⟨e₀, rfl⟩
        · exact .inl (.up hl' hw)
        · exact absurd hl' (hnoν _ _ _))
    (fun t ht => by
      induction ht with
      | root => exact .inl .root
      | @tag γ e q hq _ ih =>
        rcases (hls γ e q).mp hq with ⟨rfl, -, -⟩ | ⟨hne, hq⟩
        · exact .inr (.inr ⟨e, rfl⟩)
        · rcases ih with ih | ih | ⟨e₀, rfl⟩
          · exact .inl (.tag hq ih)
          · exact .inr (.inl (.up hq ih))
          · exact absurd hq (hnoν _ _ _))
    (fun t ht => by
      induction ht with
      | @own γ e e' q hq hlt =>
        rcases (hls γ e' q).mp hq with ⟨rfl, -, -⟩ | ⟨hne, hq⟩
        · exact .inr (.inr ⟨e, rfl⟩)
        · exact .inl (.own hq hlt)
      | @up γ e e' q hq _ ih =>
        rcases (hls γ e' q).mp hq with ⟨rfl, -, -⟩ | ⟨hne, hq⟩
        · exact .inr (.inr ⟨e, rfl⟩)
        · rcases ih with ih | ih | ⟨e₀, rfl⟩
          · exact .inl (.up hq ih)
          · exact .inl (.up hq ih)
          · exact absurd hq (hnoν _ _ _))
    (fun w γ e _ _ hze ⟨e', hee, hl'⟩ => by
      have hγ : γ ≠ ν := fun h => hze (.inr ⟨e, by rw [h]⟩)
      have hq : ∀ x, G'.ls γ x w ↔ g.ls γ x w := fun x => by
        rw [hls]; simp [hγ]
      exact ⟨⟨e', hee, (hq e').mp hl'⟩, (hq e).mp⟩)
  refine ⟨⟨FHeap.empty, Know.none, Ghost.at ν c'⟩, ⟨ν, gauth_epTok_intro⟩,
    h0.symm, k0.symm, by rw [g0]; funext b; simp [Ghost.at, Ghost.unit], by rw [g0]; rfl,
    by rw [g0]; rfl,
    ⟨hv', ν + 1, fun γ hγ => ⟨?_, ?_, fun γ' e' M e => ?_⟩⟩, fun m hm => ?_⟩
  · rw [hl γ (by omega)]; exact (hN γ (by omega)).1
  · rw [hx]; exact (hN γ (by omega)).2.1
  · show (G'.led γ').auth _ = 0
    by_cases h : γ' = ν
    · rw [h, hlN]; simp only [c', GCell.add, GCell.auth1, GCell.ep1, Nat.add_zero]
      refine if_neg fun x => ?_
      simp only [Prod.mk.injEq] at x
      have h1 : p.name = γ + 1 := by rw [← x.2.2]; rfl
      have h2 : ν = N + NC + p.name := rfl
      omega
    · rw [hl γ' h]; exact (hN γ (by omega)).2.2 γ' e' M e
  · rw [g0, Ghost.unit_add] at hm; exact ht' m hm

/-- **Issue a grant** of the current epoch under an unused id `i`, naming region `g`. -/
theorem issue {γ e i : Nat} {M : GMap} {p : STag} (g : GRegion) (hi : M i = none) :
    Upd (gauthP γ e M p) (gauthP γ e (M.set i (some g)) p ⋆ gfrag γ e i g) :=
  single (c := GCell.auth1 e M p) (fun r ⟨h, k, gh⟩ => by rw [res_eta r, h, k, gh])
    gauth_gfrag_intro fun d hv => by
      refine ⟨?_, fun x q => ?_⟩
      · rw [GCell.add_assoc, GCell.valid_auth1_add]
        obtain ⟨h1, h2, h3, h4⟩ := GCell.valid_auth1_add.mp hv
        refine ⟨fun x => by simpa [GCell.add, GCell.frag1] using h1 x, fun j g' => ?_,
          fun e' j g' he => ?_, by rw [GCell.frag1_add]; exact h4⟩ <;> simp only [GCell.add, GCell.frag1]
        · by_cases hji : j = i
          · subst hji
            have h0 : d.frag (e, j, g') = 0 :=
              Nat.eq_zero_of_not_pos fun hp => by simpa [hi] using (h2 j g').2 hp
            by_cases hg : g' = g
            · subst hg; simp [h0]
            · simp [hg, h0]
          · have hne : (e, j, g') ≠ (e, i, g) := fun h => hji (by cases h; rfl)
            simp only [hne, ↓reduceIte, Nat.zero_add, GMap.set_ne _ _ hji]
            exact h2 j g'
        · have hne : (e', j, g') ≠ (e, i, g) := fun h => by cases h; omega
          simp [hne, h3 e' j g' he]
      · rw [GCell.add_assoc, GCell.ls_auth1_add, GCell.ls_auth1_add, GCell.frag1_add_auth]

/-- **Give back a grant** of the current epoch. -/
theorem retire {γ e i : Nat} {M : GMap} {p : STag} {g : GRegion} :
    Upd (gauthP γ e M p ⋆ gfrag γ e i g) (gauthP γ e (M.set i none) p) :=
  single (c := (GCell.auth1 e M p).add (GCell.frag1 e i g)) (fun _ h => gauth_gfrag h)
    ⟨rfl, rfl, rfl⟩ fun d hv => by
      refine ⟨?_, fun x q => ?_⟩
      · rw [GCell.add_assoc] at hv
        obtain ⟨h1, hM, h0, h2, h3, h4⟩ := GCell.valid_pair hv
        refine GCell.valid_auth1_add.mpr ⟨h1, fun j g' => ⟨(h2 j g').1, fun hp => ?_⟩, h3, h4⟩
        have hj := (h2 j g').2 hp
        by_cases hji : j = i
        · subst hji; rw [hM] at hj; cases hj; omega
        · rw [GMap.set_ne _ _ hji]; exact hj
      · rw [GCell.add_assoc, GCell.ls_auth1_add, GCell.ls_auth1_add, GCell.frag1_add_auth]

/-- **Re-point a grant** of the current epoch at another region (a resize in place). -/
theorem reassign {γ e i : Nat} {M : GMap} {p : STag} {g : GRegion} (g' : GRegion) :
    Upd (gauthP γ e M p ⋆ gfrag γ e i g) (gauthP γ e (M.set i (some g')) p ⋆ gfrag γ e i g') := by
  have h := issue (γ := γ) (e := e) (p := p) g' (GMap.set_same M i none)
  rw [GMap.set_set] at h
  exact trans retire h

/-- **The next epoch**, with no grant and the same parent, and its whole token (`epTok`): every
outstanding token becomes stale, and so does every share tagged with the old epoch or with a tag
below it (`Ghost.valid_led_change` with the future tags as `Z`); the old epoch's receipts stay
live (`EUpd.revoke`). No frame holds a part of the new epoch's token (`GCell.EpOk`). -/
theorem bump {γ e : Nat} {M : GMap} {p : STag} :
    Upd (gauthP γ e M p) (gauthP γ (e + 1) GMap.empty p ⋆ epTok γ (e + 1) Frac.one) := by
  rintro r ⟨h0, k0, g0⟩ g hg
  rw [g0] at hg
  obtain ⟨hv, N, hN⟩ := hg
  let c' := (GCell.auth1 (e + 1) GMap.empty p).add (GCell.ep1 (e + 1) Frac.one)
  let G := (Ghost.at γ (GCell.auth1 e M p)).add g
  let G' := (Ghost.at γ c').add g
  have hlv := hv.1 γ
  simp only [Ghost.add, Ghost.at, ↓reduceIte] at hlv
  obtain ⟨hd1, -, hd3, hd4⟩ := GCell.valid_auth1_add.mp hlv
  have hx : G'.extent = G.extent := by funext b; simp [G, G', Ghost.add, Ghost.at]
  have hcl : G'.cl = G.cl := by simp only [G, G', Ghost.at_add_cl]
  have hl : ∀ γ', γ' ≠ γ → G'.led γ' = G.led γ' := fun γ' hne => by
    simp [G, G', Ghost.add, Ghost.at, hne]
  have hls : ∀ γ' x q, G.ls γ' x q ↔ (γ' = γ ∧ x = e ∧ q = p) ∨ (γ' ≠ γ ∧ g.ls γ' x q) :=
    fun γ' x q => Ghost.ls_at_add hd1
  have hls' : ∀ γ' x q, G'.ls γ' x q ↔ (γ' = γ ∧ x = e + 1 ∧ q = p) ∨ (γ' ≠ γ ∧ g.ls γ' x q) :=
    fun γ' x q => Ghost.ls_at_ep_add' hd1
  have hG : G.ls γ e p := (hls γ e p).mpr (.inl ⟨rfl, rfl, rfl⟩)
  -- a tag of another ledger has the same status
  have hoth : ∀ γ' x q, γ' ≠ γ → (G'.ls γ' x q ↔ G.ls γ' x q) := fun γ' x q hne => by
    rw [hls, hls']; simp [hne]
  obtain ⟨hv', ht'⟩ := Ghost.valid_led_change (G := G) (G' := G') (Fut G.ls) hx hcl
    (by simp only [G, G', Ghost.at_add_ac]) hv
    (fun γ' => by
      by_cases h : γ' = γ
      · subst h
        simp only [G', c', Ghost.add, Ghost.at, ↓reduceIte]
        rw [GCell.add_assoc]
        refine GCell.valid_auth1_add.mpr ⟨fun x => by simp [GCell.add, GCell.ep1, hd1 x],
          fun i g => by simp [GCell.add, GCell.ep1, hd3 (e + 1) i g (by omega)],
          fun e' i g he => by simp [GCell.add, GCell.ep1, hd3 e' i g (by omega)], fun e' => ?_,
          fun e' he => ?_⟩
        · have h1 := hd4.1 e'
          by_cases he : e' = e + 1
          · have h2 := hd4.2 e' (by omega)
            have : Frac.one.val = 1 := rfl
            simp only [GCell.add_ep_val, GCell.ep1_ep_val, if_pos he, h2]; grind
          · simp only [GCell.add_ep_val, GCell.ep1_ep_val, if_neg he]; grind
        · have h2 := hd4.2 e' (by omega)
          simp only [GCell.add_ep_val, GCell.ep1_ep_val, if_neg (show e' ≠ e + 1 by omega), h2]; grind
      · rw [hl γ' h]; exact hv.1 γ')
    (fun γ' x hz b k => (hv.2.1 b).2.2 γ' x k hz)
    (fun γ' x hz b y k => (hv.2.2.1.1 b y).2.2 γ' x k hz)
    Fut.not_none
    (fun w γ' x x' hw hl' _ => by
      rcases (hls' γ' x' w).mp hl' with ⟨rfl, -, rfl⟩ | ⟨hne, hl'⟩
      · exact .up hG hw
      · exact .up ((hoth γ' x' w hne).mp ((hls' γ' x' w).mpr (.inr ⟨hne, hl'⟩))) hw)
    (fun t ht => by
      induction ht with
      | root => exact .inl .root
      | @tag γ' x q hq _ ih =>
        rcases (hls' γ' x q).mp hq with ⟨rfl, rfl, rfl⟩ | ⟨hne, hq'⟩
        · exact .inr (.own hG (by omega))
        · have hq := (hoth γ' x q hne).mp hq
          rcases ih with ih | ih
          · exact .inl (.tag hq ih)
          · exact .inr (.up hq ih))
    (fun t ht => by
      induction ht with
      | @own γ' x x' q hq hlt =>
        rcases (hls' γ' x' q).mp hq with ⟨rfl, rfl, rfl⟩ | ⟨hne, -⟩
        · exact .inl (.own hG (by omega))
        · exact .inl (.own ((hoth γ' x' q hne).mp hq) hlt)
      | @up γ' x x' q hq _ ih =>
        have ih : Fut G.ls q := by rcases ih with ih | ih <;> exact ih
        rcases (hls' γ' x' q).mp hq with ⟨rfl, rfl, rfl⟩ | ⟨hne, -⟩
        · exact .inl (.up hG ih)
        · exact .inl (.up ((hoth γ' x' q hne).mp hq) ih))
    (fun w γ' x _ _ hze ⟨x', hxx, hl'⟩ => by
      by_cases hγ : γ' = γ
      · rcases (hls' γ' x' w).mp hl' with ⟨-, -, hw⟩ | ⟨hne, -⟩
        · rw [hγ, hw]
          have hx : x ≤ e := Nat.le_of_not_lt fun hc => hze (by rw [hγ]; exact .own hG hc)
          refine ⟨⟨e, hx, hG⟩, fun h => ?_⟩
          rcases (hls' γ x p).mp h with ⟨-, h2, -⟩ | ⟨hne, -⟩
          · omega
          · exact absurd rfl hne
        · exact absurd hγ hne
      · exact ⟨⟨x', hxx, (hoth γ' x' w hγ).mp hl'⟩, (hoth γ' x w hγ).mp⟩)
  refine ⟨⟨FHeap.empty, Know.none, Ghost.at γ c'⟩, gauth_epTok_intro,
    h0.symm, k0.symm, by rw [g0]; funext b; simp [Ghost.at], by rw [g0]; rfl, by rw [g0]; rfl,
    ⟨hv', N + γ + 1, fun γ' hγ => ⟨?_, ?_, fun γ'' x' M' x => ?_⟩⟩,
    fun m hm => by rw [g0] at hm; exact ht' m hm⟩
  · rw [hl γ' (by omega)]; exact (hN γ' (by omega)).1
  · rw [hx]; exact (hN γ' (by omega)).2.1
  · have hold := (hN γ' (by omega)).2.2
    by_cases h : γ'' = γ
    · subst h
      have h1 := hold γ'' x' M' x
      have h2 := hold γ'' e M x
      simp only [G, G', c', Ghost.add, Ghost.at, ↓reduceIte, GCell.add, GCell.auth1, GCell.ep1,
        Nat.add_zero] at h1 h2 ⊢
      by_cases hp : p = some (γ', x)
      · subst hp; simp at h2
      · rw [if_neg (fun y => hp (by simp only [Prod.mk.injEq] at y; exact y.2.2.symm))]
        rw [if_neg (fun y => hp (by simp only [Prod.mk.injEq] at y; exact y.2.2.symm))] at h1
        exact h1
    · rw [hl γ'' h]; exact hold γ'' x' M' x

end Upd


/-- **A token of the current epoch names a recorded grant.** -/
theorem gfrag_mem {γ e i : Nat} {M : GMap} {p : STag} {g : GRegion} {r : Res} {gF : Ghost}
    (h : (gauthP γ e M p ⋆ gfrag γ e i g) r) (hg : Ghost.Ok r.gh gF) : M i = some g := by
  rw [gauth_gfrag h] at hg
  have := hg.1.1 γ
  simp only [Ghost.add, Ghost.at, ↓reduceIte] at this
  rw [GCell.add_assoc] at this
  exact (GCell.valid_pair this).2.1

/-! ## Triple rules -/

namespace FTriple

variable {α : Type} {P P' : FAssn} {c : MemM α} {Q Q' : α → FAssn}

/-- A ghost update of the precondition. -/
theorem upd (hu : Upd P P') (ht : FTriple P' c Q) : FTriple P c Q := by
  intro m r rF hh hp hs
  obtain ⟨r', hp', e, k, x, xc, xa, hg, ht'⟩ := hu r hp rF.gh hh.ghost.1
  exact ht m r' rF ⟨by rw [e]; exact hh.disj, by rw [e]; exact hh.heap, by rw [k]; exact hh.know,
    hh.knowF, ⟨hg, ht' m hh.ghost.2.1, hh.ghost.2.2.1.congr (by funext x y; simp [xc]),
      by simpa [xa] using hh.ghost.2.2.2⟩⟩ hp' hs

/-- A ghost update of the postcondition. -/
theorem upd_post (ht : FTriple P c Q) (hu : ∀ v, Upd (Q v) (Q' v)) : FTriple P c Q' := by
  intro m r rF hh hp hs
  have := ht m r rF hh hp hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', hh', hq, hs'⟩ := this
    obtain ⟨r'', hq', e, k, x, xc, xa, hg, ht'⟩ := hu _ r' hq rF.gh hh'.ghost.1
    exact ⟨r'', ⟨by rw [e]; exact hh'.disj, by rw [e]; exact hh'.heap, by rw [k]; exact hh'.know,
      hh'.knowF, ⟨hg, ht' _ hh'.ghost.2.1, hh'.ghost.2.2.1.congr (by funext x y; simp [xc]),
        by simpa [xa] using hh'.ghost.2.2.2⟩⟩, hq', hs'⟩

/-- The fact `M i = some g` of a token of the current epoch, in a precondition. -/
theorem mem {γ e i : Nat} {M : GMap} {p : STag} {g : GRegion} {R : FAssn}
    (ht : M i = some g → FTriple ((gauthP γ e M p ⋆ gfrag γ e i g) ⋆ R) c Q) :
    FTriple ((gauthP γ e M p ⋆ gfrag γ e i g) ⋆ R) c Q := by
  intro m r rF hh hp hs
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := id hp
  have hg := hh.ghost
  have : Ghost.Ok r₁.gh (r₂.gh.add rF.gh) := Ghost.Ok.assoc.mp hg.1
  exact ht (gfrag_mem h1 this) m _ rF hh hp hs

end FTriple

/-! ## Credits (`docs/sep-full-state.md` §Credits and room)

`credits n` (`£n`) are fragments of an authoritative supply `creditAuth N` (`●N`), the key `cred`
of the counter cell (`Ghost.ac`): a valid ghost state holds at most one authority and at most `N`
credits next to it (`ACell.Valid`), and the memory meters the authority: the credits plus the
steps run so far are at most `N` (`TickAuth`). No rule creates a credit: every judgment
quantifies over every frame, among them one that holds `●N` with all credits out
(`tests/roadmap/sep-full/CreditsCX.lean`). Only the adequacy theorem keeps `●N` in the frame and
hands `credits` to the program. Credits own no bytes, no knowledge and no stack token, so
`EUpd.drop` drops them. -/

/-- The ghost state with the counter cell `c` and nothing else. -/
def Ghost.ofAC (c : KCell) : Ghost := { Ghost.unit with ac := c }

@[simp] theorem Ghost.ofAC_ac (c : KCell) : (Ghost.ofAC c).ac = c := rfl

theorem Ghost.ofAC_add (a b : KCell) : (Ghost.ofAC a).add (Ghost.ofAC b) = Ghost.ofAC (a.add b) := by
  ext1 <;> (try funext x) <;> (try funext y) <;> simp [Ghost.ofAC, Ghost.add, Ghost.unit]

@[simp] theorem Ghost.ofAC_unit : Ghost.ofAC ACell.unit = Ghost.unit := rfl

/-- The ghost state with `n` credits and nothing else. -/
def Ghost.cred (n : Nat) : Ghost := Ghost.ofAC (ACell.fragAt .cred n)

/-- The ghost state with the credit authority `●N` and nothing else. -/
def Ghost.credAuth (N : Nat) : Ghost := Ghost.ofAC (ACell.authAt .cred N)

/-- **`n` credits** (`£n`). -/
def credits (n : Nat) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.cred n

/-- **`n` step receipts** (`docs/sep-full-state.md` §Step ticks): at least `n` steps (`Zig.tick`)
have run (`TickAuth`). -/
def spent (n : Nat) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.ofAC (ACell.fragAt .spent n)

/-- **Plain-mode steps**: no meter runs, so a step needs no credit (`TickAuth`). -/
def unmetered : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.ofAC (ACell.fragAt .unmetered 1)

/-- **No thread has a stack budget** (`Mem.NoStack`, `MemAuth`): a stack push needs no stack
token. -/
def noStack : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.ofAC (ACell.fragAt .noStack 1)

/-- **The plain mode** of a statement that bounds neither steps nor stack depth: no meter runs
and no thread has a stack budget (`docs/sep-full-state.md` §Plain mode). Duplicable
(`EUpd.plain_dup`). Statements use this name, so its body can change (a thread-relative
"the current thread has no budget", step 5) without changing them. -/
def plain : FAssn := noStack ⋆ unmetered

/-- A resource with a `noStack` fragment is held only in a memory without stack budgets. -/
theorem Holds.noStack {m : Mem} {r rF : Res} (hh : Holds m r rF) (h : 0 < r.gh.ac.frag .noStack) :
    m.NoStack :=
  hh.ghost.2.2.2.noStack (by simp only [Ghost.add_ac, ACell.add_frag]; omega)

/-- The plain mode owns no bytes, no knowledge and no stack token. -/
theorem plain_ghost {r : Res} (h : plain r) :
    r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh.Affine := by
  obtain ⟨r₁, r₂, -, rfl, ⟨h1, k1, g1⟩, ⟨h2, k2, g2⟩⟩ := h
  refine ⟨by simp [h1, h2], by simp [k1, k2, Know.union_none], fun k v => ?_⟩
  simp [g1, g2, Ghost.ofAC]

/-- The plain mode holds a `noStack` fragment. -/
theorem plain_noStack {r : Res} {R : FAssn} (h : (plain ⋆ R) r) : 0 < r.gh.ac.frag .noStack := by
  obtain ⟨r₁, r₂, -, rfl, ⟨r₃, r₄, -, rfl, ⟨-, -, g3⟩, ⟨-, -, g4⟩⟩, -⟩ := h
  simp [g3, g4, Ghost.ofAC]; omega

/-- **The credit supply** `●N`: at most `N` credits exist next to it. Never given to a program. -/
def creditAuth (N : Nat) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.credAuth N

theorem Ghost.cred_add (a b : Nat) : (Ghost.cred a).add (Ghost.cred b) = Ghost.cred (a + b) := by
  rw [Ghost.cred, Ghost.cred, Ghost.ofAC_add, ACell.fragAt_add]; rfl

@[simp] theorem Ghost.cred_zero : Ghost.cred 0 = Ghost.unit := by
  simp [Ghost.cred]

/-- Credits split and join: an equality. -/
theorem credits_add (a b : Nat) : credits (a + b) = (credits a ⋆ credits b) := by
  funext r; apply propext; constructor
  · rintro ⟨h, k, g⟩
    exact ⟨⟨FHeap.empty, Know.none, Ghost.cred a⟩, ⟨FHeap.empty, Know.none, Ghost.cred b⟩,
      FHeap.disjoint_empty _, by rw [res_eta r, h, k, g, ← Ghost.cred_add]; simp [Know.union_none],
      ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩
  · rintro ⟨r₁, r₂, -, rfl, ⟨h1, k1, g1⟩, ⟨h2, k2, g2⟩⟩
    exact ⟨by simp [h1, h2], by simp [k1, k2, Know.union_none], by simp [g1, g2, Ghost.cred_add]⟩

theorem credits_zero : credits 0 = emp := by
  funext r; simp [credits, emp]

/-- **Credits are bounded by the supply**: a resource with `n` credits and a frame with `●N` give
`n ≤ N`. -/
theorem Holds.credits_le {m : Mem} {r rF : Res} {R R' : FAssn} {n N : Nat} (hh : Holds m r rF)
    (hr : (credits n ⋆ R) r) (hF : (creditAuth N ⋆ R') rF) : n ≤ N := by
  obtain ⟨r₁, r₂, -, rfl, ⟨-, -, g1⟩, -⟩ := hr
  obtain ⟨f₁, f₂, -, rfl, ⟨-, -, g2⟩, -⟩ := hF
  obtain ⟨-, -, h3, -⟩ := hh.ghost.1.1.2.2.2 .cred
  have := h3 N (by
    simp only [Ghost.add_ac, g2, Ghost.credAuth, Ghost.ofAC_ac, ACell.add_auth, ACell.authAt_auth,
      and_self, ↓reduceIte]
    omega)
  simp only [Ghost.add_ac, g1, Ghost.cred, Ghost.ofAC_ac, ACell.add_frag, ACell.fragAt_frag,
    ↓reduceIte] at this
  omega

/-- A change of the counter cells only keeps `GOk` when the new cell is valid and authorized. -/
theorem GOk.ac_change {m : Mem} {g gF g' gF' : Ghost} (h : GOk m g gF)
    (hl : (g'.add gF').led = (g.add gF).led) (hx : (g'.add gF').extent = (g.add gF).extent)
    (hc : (g'.add gF').cl = (g.add gF).cl) (hv : (g'.add gF').ac.Valid)
    (hM : MemAuth m (g'.add gF').ac) : GOk m g' gF' := by
  obtain ⟨⟨hV, hF⟩, ht, hcf, -⟩ := h
  unfold GOk Ghost.Ok
  generalize g.add gF = G at hV hF ht hcf hl hx hc
  generalize g'.add gF' = G' at hl hx hc hv hM ⊢
  obtain ⟨l, x, c, ac⟩ := G'
  subst hl hx hc
  exact ⟨⟨⟨hV.1, hV.2.1, hV.2.2.1, hv⟩, hF⟩, ht, hcf, hM⟩

/-- **The adequacy step of credits** (`docs/sep-full-state.md` §Step ticks): a memory that holds
`r` with frame `rF`, which hold no credit, no credit authority and no plain-mode step fact
(`unmetered`), holds `r` with `N` credits and the frame with the meter `●(m.ticks + N)`: `N` more
steps can be paid. Only an adequacy theorem uses it: no judgment can (the frame is fixed). -/
theorem Holds.addCredits {m : Mem} {r rF : Res} (N : Nat) (hh : Holds m r rF)
    (hf : (r.gh.add rF.gh).ac.frag .cred = 0) (ha : ∀ n, (r.gh.add rF.gh).ac.auth .cred n = 0)
    (hu : (r.gh.add rF.gh).ac.frag .unmetered = 0) :
    Holds m ⟨r.heap, r.know, r.gh.add (Ghost.cred N)⟩
      ⟨rF.heap, rF.know, rF.gh.add (Ghost.credAuth (m.ticks + N))⟩ := by
  obtain ⟨hd, hm, hk, hkF, hg⟩ := hh
  have hM := hg.2.2.2
  have hV : (r.gh.add rF.gh).ac.Valid := hg.1.1.2.2.2
  generalize hc : (r.gh.add rF.gh).ac = c at hf ha hu hM hV
  have e : ((r.gh.add (Ghost.cred N)).add (rF.gh.add (Ghost.credAuth (m.ticks + N)))).ac =
      (ACell.fragAt .cred N).add ((ACell.authAt .cred (m.ticks + N)).add c) := by
    rw [← hc]; ext <;> simp [Ghost.cred, Ghost.credAuth] <;> omega
  refine ⟨hd, hm, hk, hkF, hg.ac_change ?_ ?_ ?_ ?_ ?_⟩
  · funext γ; simp [Ghost.add, Ghost.cred, Ghost.credAuth, Ghost.ofAC, Ghost.unit]
  · funext b; simp [Ghost.add, Ghost.cred, Ghost.credAuth, Ghost.ofAC, Ghost.unit]
  · funext b x; simp [Ghost.add, Ghost.cred, Ghost.credAuth, Ghost.ofAC, Ghost.unit]
  · rw [e]; exact ACell.Valid.addAuthLe (Nat.le_add_left _ _) hV hf ha
  · rw [e]
    obtain ⟨hs, ⟨t1, t2, t3⟩, hn, ho, hcur⟩ := hM
    refine ⟨hs.congr fun k v => by simp, ⟨fun L hL => ?_, by simpa using t2, fun hp => ?_⟩,
      fun hp => hn (by simpa using hp), fun k L hk => by simp [hk, ho k L hk],
      fun v hv => hcur v (by simpa using hv)⟩
    · have hL' : L = m.ticks + N := by
        refine Classical.byContradiction fun hne => ?_
        simp [ha, hne] at hL
      subst hL'; simp [hf]; omega
    · simp [hu] at hp

/-- The ghost state of the plain mode. -/
def Ghost.plain : Ghost := Ghost.ofAC ((ACell.fragAt .noStack 1).add (ACell.fragAt .unmetered 1))

/-- The plain mode's resource. -/
theorem plain_intro : plain ⟨FHeap.empty, Know.none, Ghost.plain⟩ :=
  ⟨⟨FHeap.empty, Know.none, Ghost.ofAC (ACell.fragAt .noStack 1)⟩,
    ⟨FHeap.empty, Know.none, Ghost.ofAC (ACell.fragAt .unmetered 1)⟩, FHeap.disjoint_empty _,
    by simp [Ghost.plain, Ghost.ofAC_add, FHeap.empty_union, Know.union_none], ⟨rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl⟩⟩

/-- **The adequacy step of the plain mode** (`docs/sep-full-state.md` §Plain mode): a memory
without stack budgets, whose resource and frame hold no credit authority (no meter runs), holds
the resource with the plain mode added. An adequacy theorem uses it (`Full/Init`); a judgment
cannot (the frame is fixed, and with a meter in it `TickAuth` rules plain mode out). -/
theorem Holds.addPlain {m : Mem} {r rF : Res} (hh : Holds m r rF) (hns : m.NoStack)
    (ha : ∀ L, (r.gh.add rF.gh).ac.auth .cred L = 0) :
    Holds m ⟨r.heap, r.know, r.gh.add Ghost.plain⟩ rF := by
  obtain ⟨hd, hm, hk, hkF, hg⟩ := hh
  have hM := hg.2.2.2
  have hV : (r.gh.add rF.gh).ac.Valid := hg.1.1.2.2.2
  have ho := hM.onlyCred
  generalize hc : (r.gh.add rF.gh).ac = c at ha hM hV ho
  have e : ((r.gh.add Ghost.plain).add rF.gh).ac =
      (ACell.fragAt .noStack 1).add ((ACell.fragAt .unmetered 1).add c) := by
    rw [← hc]; ext <;> simp [Ghost.plain] <;> omega
  refine ⟨hd, hm, hk, hkF, hg.ac_change ?_ ?_ ?_ ?_ ?_⟩
  · funext γ; simp [Ghost.add, Ghost.plain, Ghost.ofAC, Ghost.unit]
  · funext b; simp [Ghost.add, Ghost.plain, Ghost.ofAC, Ghost.unit]
  · funext b x; simp [Ghost.add, Ghost.plain, Ghost.ofAC, Ghost.unit]
  · rw [e]; intro k
    obtain ⟨h1, h2, h3, h4, h5⟩ := hV k
    by_cases hk : k = .cred
    · subst hk; exact (hV .cred).congr (by simp) (by simp) (by simp)
    · refine ⟨by simpa using h1, by simpa using h2, fun n hn => ?_, by simpa using h4, by simpa using h5⟩
      simp [ho k n hk] at hn
  · rw [e]
    obtain ⟨hs, ⟨t1, t2, t3⟩, -, -, hcur⟩ := hM
    exact ⟨hs.congr fun k v => by simp, ⟨fun L hL => by simp [ha] at hL, by simpa using t2,
      fun _ L => by simpa using ha L⟩, fun _ => hns, fun k L hk => by simp [ho k L hk],
      fun v hv => hcur v (by simpa using hv)⟩

/-- **`r` holds the plain mode**: both of its fragments (`noStack`, `unmetered`), whatever else
it holds. A thread's part with them can split off a copy of `plain` (`Holds.splitPlain`). -/
def Res.Plain (r : Res) : Prop := 0 < r.gh.ac.frag .noStack ∧ 0 < r.gh.ac.frag .unmetered

/-- The plain mode's resource holds the plain mode. -/
theorem Res.plain_of {r : Res} (h : plain r) : r.Plain := by
  obtain ⟨r₁, r₂, -, rfl, ⟨-, -, g1⟩, ⟨-, -, g2⟩⟩ := h
  constructor <;> simp [g1, g2, Ghost.ofAC]

/-- A resource with the plain mode next to anything holds the plain mode. -/
theorem Res.plain_of_sep {P : FAssn} {r : Res} (h : (P ⋆ plain) r) : r.Plain := by
  obtain ⟨r₁, r₂, -, rfl, -, h2⟩ := h
  obtain ⟨a, b⟩ := Res.plain_of h2
  exact ⟨by simp only [Ghost.add_ac, ACell.add_frag]; omega,
    by simp only [Ghost.add_ac, ACell.add_frag]; omega⟩

/-- **The plain mode is duplicable**: next to a frame that holds it (both of its fragments), a
resource can take another copy (`Holds.addPlain`: the frame's `noStack` fact and its plain-mode
steps rule out a budget and a meter). -/
theorem Holds.dupPlain {m : Mem} {r rF : Res} (hh : Holds m r rF) (hF : rF.Plain) :
    Holds m ⟨r.heap, r.know, r.gh.add Ghost.plain⟩ rF :=
  hh.addPlain (hh.swap.noStack hF.1) fun L =>
    hh.ghost.2.2.2.tick.plain (by have := hF.2; simp only [Ghost.add_ac, ACell.add_frag]; omega) L

/-- **The plain mode splits off its fragments**: a resource that holds the plain mode (`Res.Plain`)
can take another copy (`Holds.addPlain`: its own `noStack` fact and plain-mode steps rule out a
budget and a meter). -/
theorem Holds.splitPlain {m : Mem} {r rF : Res} (hh : Holds m r rF) (hr : r.Plain) :
    Holds m ⟨r.heap, r.know, r.gh.add Ghost.plain⟩ rF :=
  hh.addPlain (hh.noStack hr.1) fun L =>
    hh.ghost.2.2.2.tick.plain (by have := hr.2; simp only [Ghost.add_ac, ACell.add_frag]; omega) L

/-- A resource with the plain mode added. -/
theorem sep_plain_intro {R : FAssn} {r : Res} (h : R r) :
    (R ⋆ plain) ⟨r.heap, r.know, r.gh.add Ghost.plain⟩ :=
  ⟨r, ⟨FHeap.empty, Know.none, Ghost.plain⟩, fun _ => .inr rfl,
    by simp [FHeap.union_empty, Know.union_none], h, plain_intro⟩

/-! ## Stack tokens and the running thread (`docs/sep-full-state.md` §Stack depth)

The resources of a stack budget (`ZigLean/Sep/Full/StackDepth.lean`): `sp t S D` (thread `t`'s
budget `S` and depth bound `D`), `ent t o ℓ c` (a live stack entry of `t`) and `cur t` (thread
`t` runs). The memory decides which of them exist (`MemAuth`), so no rule creates one; the
adequacy theorem hands `sp 0 S 0` and `cur 0` to `main` (`Full/Init`), and the thread rules give
a thread `cur t` for its own steps (`Full/ThreadOwned`). -/

/-- **`sp t S D`**: thread `t` has the stack budget `S`, and its stack depth is at most `D`
(`spCell`). Exclusive: one per thread with a budget. -/
def sp (t : ThreadId) (S D : Nat) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.ofAC (spCell t S D)

/-- **`ent t o ℓ c`**: a live stack entry of thread `t` (its block `o = some b`, or a frame
`o = none`), pushed at the logical depth `ℓ` with the charge `c` (`entCell`). -/
def ent (t : ThreadId) (o : Option BlockId) (ℓ c : Nat) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.ofAC (entCell t o ℓ c)

/-- The ghost state of `cur t`. -/
def Ghost.cur (t : ThreadId) : Ghost := Ghost.ofAC (curCell t)

/-- **`cur t`**: thread `t` runs (`m.current = t`, `MemAuth.cur`). At most one exists, so a
thread holds it only while it runs. -/
def cur (t : ThreadId) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.cur t

/-- `r` holds no `cur` token. -/
def Res.NoCur (r : Res) : Prop := ∀ v, r.gh.ac.ex .cur v = 0

/-- **`cur t` names the running thread.** -/
theorem Holds.current {m : Mem} {r rF : Res} {R : FAssn} {t : ThreadId} (hh : Holds m r rF)
    (h : (cur t ⋆ R) r) : m.current = t := by
  obtain ⟨r₁, r₂, -, rfl, ⟨-, -, g1⟩, -⟩ := h
  have := hh.ghost.2.2.2.cur (t, 0) (by simp [g1, Ghost.cur, Ghost.ofAC, curCell]; omega)
  exact this.symm

/-- **The running thread's token is authorized** next to a resource and a frame without one. -/
theorem Holds.addCur {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hnc : ∀ v, (r.gh.add rF.gh).ac.ex .cur v = 0) :
    Holds m ⟨r.heap, r.know, r.gh.add (Ghost.cur m.current)⟩ rF := by
  obtain ⟨hd, hm, hk, hkF, hg⟩ := hh
  have hM := hg.2.2.2
  have hV : (r.gh.add rF.gh).ac.Valid := hg.1.1.2.2.2
  have e : ((r.gh.add (Ghost.cur m.current)).add rF.gh).ac = (curCell m.current).add (r.gh.add rF.gh).ac := by
    ext <;> simp [Ghost.cur] <;> omega
  refine ⟨hd, hm, hk, hkF, hg.ac_change ?_ ?_ ?_ ?_ ?_⟩
  · funext γ; simp [Ghost.add, Ghost.cur, Ghost.ofAC, Ghost.unit]
  · funext b; simp [Ghost.add, Ghost.cur, Ghost.ofAC, Ghost.unit]
  · funext b x; simp [Ghost.add, Ghost.cur, Ghost.ofAC, Ghost.unit]
  · rw [e]; exact ACell.Valid.add_ex _ hV hnc
  · rw [e]; exact hM.addCur

/-- `Holds.addCur` with the token in the frame. -/
theorem Holds.addCurF {m : Mem} {r rF : Res} (hh : Holds m r rF)
    (hnc : ∀ v, (r.gh.add rF.gh).ac.ex .cur v = 0) :
    Holds m r ⟨rF.heap, rF.know, rF.gh.add (Ghost.cur m.current)⟩ :=
  (hh.swap.addCur fun v => by rw [Ghost.add_comm]; exact hnc v).swap

/-- **A frame's `cur` token**: the resource holds none, and the token can be dropped. -/
theorem Holds.dropCurF {m : Mem} {r rF : Res} {t : ThreadId}
    (hh : Holds m r ⟨rF.heap, rF.know, rF.gh.add (Ghost.cur t)⟩) : r.NoCur ∧ Holds m r rF := by
  obtain ⟨hd, hm, hk, hkF, hg⟩ := hh
  have hM := hg.2.2.2
  have hV := hg.1.1.2.2.2
  have e : (r.gh.add (rF.gh.add (Ghost.cur t))).ac = (curCell t).add (r.gh.add rF.gh).ac := by
    ext <;> simp [Ghost.cur] <;> omega
  simp only at hM hV
  rw [e] at hM hV
  refine ⟨fun v => ?_, hd, hm, hk, hkF, hg.ac_change ?_ ?_ ?_ hV.of_add_right hM.dropCur⟩
  · have := hV.ex_zero v; simp at this; exact this.1
  · funext γ; simp [Ghost.add, Ghost.cur, Ghost.ofAC, Ghost.unit]
  · funext b; simp [Ghost.add, Ghost.cur, Ghost.ofAC, Ghost.unit]
  · funext b x; simp [Ghost.add, Ghost.cur, Ghost.ofAC, Ghost.unit]

end Full
end Zig
