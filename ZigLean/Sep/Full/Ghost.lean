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
  ⟨fun x => if x = (e, M, p) then 1 else 0, fun _ => 0⟩

/-- The token `◯(e, i ↦ g)`. -/
def frag1 (e i : Nat) (g : GRegion) : GCell := ⟨fun _ => 0, fun t => if t = (e, i, g) then 1 else 0⟩

theorem valid_auth1_add {e : Nat} {M : GMap} {p : STag} {d : GCell} :
    ((auth1 e M p).add d).Valid ↔
      (∀ x, d.auth x = 0) ∧ d.TokOk e M ∧ ∀ e' i g, e < e' → d.frag (e', i, g) = 0 := by
  constructor
  · rintro (h | ⟨e', M', p', h1, h2, h3, h4⟩)
    · have := h (e, M, p); simp [add, auth1] at this
    · by_cases hx : (e', M', p') = (e, M, p)
      · simp only [Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl, rfl⟩ := hx
        refine ⟨fun x => ?_, fun i g => by simpa [add, auth1] using h3 i g,
          fun e'' i g he => by simpa [add, auth1] using h4 e'' i g he⟩
        by_cases hx' : x = (e', M', p')
        · subst hx'; simp [add, auth1] at h1; omega
        · have := h2 x hx'; simp [add, auth1, hx'] at this; omega
      · have := h2 (e, M, p) (Ne.symm hx); simp [add, auth1] at this
  · rintro ⟨h1, h2, h3⟩
    refine .inr ⟨e, M, p, by simp [add, auth1, h1], fun x hx => by simp [add, auth1, hx, h1],
      fun i g => by simpa [add, auth1] using h2 i g, fun e' i g he => by simpa [add, auth1] using h3 e' i g he⟩

theorem frag1_add (e i : Nat) (g : GRegion) (d : GCell) :
    (frag1 e i g).add d = ⟨d.auth, fun t => (if t = (e, i, g) then 1 else 0) + d.frag t⟩ := by
  ext <;> simp [add, frag1]

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

end GCell

/-! ## Ghost states with one name -/

/-- The ghost state with cell `c` at `γ` and nothing elsewhere. -/
def Ghost.at (γ : Nat) (c : GCell) : Ghost :=
  ⟨fun γ' => if γ' = γ then c else GCell.unit, fun _ => ECell.unit⟩

theorem Ghost.at_add (γ : Nat) (c c' : GCell) : (Ghost.at γ c).add (Ghost.at γ c') = Ghost.at γ (c.add c') := by
  ext1
  · funext γ'; simp only [Ghost.add, Ghost.at]; split <;> simp
  · funext b; simp [Ghost.add, Ghost.at]

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

/-! ## Changes of the ledgers -/

/-- **A change of the ledgers** (statuses `G.ls` to `G'.ls`, same extent claims) keeps validity and
the truth of every claim. `Z` is a set of tags without claims, closed under children (under the new
statuses); every tag that the change makes active or future is in `Z` or was so before; and a child
tag outside `Z` of a world that stays active keeps a status as live as before (current stays
current, live stays live). A bump (`Upd.bump`: `Z` the future tags) turns the old epoch and every
tag below it dormant at once; a new ledger (`Upd.alloc`: `Z` also its name) adds an empty tree. -/
theorem Ghost.valid_led_change {G G' : Ghost} (Z : STag → Prop) (hx : G'.extent = G.extent)
    (hv : G.Valid) (hlv : ∀ γ, (G'.led γ).Valid)
    (hZ : ∀ γ e, Z (some (γ, e)) → ∀ b k, ((G.extent b).tsh γ e k).val = 0 ∧ ((G.extent b).rc γ e k).val = 0)
    (hZn : ¬ Z none) (hZc : ∀ w γ e e', Z w → G'.ls γ e' w → e ≤ e' → Z (some (γ, e)))
    (hA : ∀ t, Act G'.ls t → Act G.ls t ∨ Z t) (hF : ∀ t, Fut G'.ls t → Fut G.ls t ∨ Z t)
    (hC : ∀ w γ e, Act G'.ls w → ¬ Z w → ¬ Z (some (γ, e)) → (∃ e', e ≤ e' ∧ G'.ls γ e' w) →
      (∃ e', e ≤ e' ∧ G.ls γ e' w) ∧ (G'.ls γ e w → G.ls γ e w)) :
    G'.Valid ∧ ∀ m, ExtTrue m G → ExtTrue m G' := by
  have hZt : ∀ t, Z t → ∀ b k, ((G.extent b).tg t k).val = 0 := fun t ht b k => by
    rcases t with _ | ⟨γ, e⟩
    · exact absurd ht hZn
    · exact (hZ γ e ht b k).1
  -- a world of `Z` weighs nothing with zero budgets on `Z`
  classical
  let β' : (Nat → Nat → Rat) → Nat → Nat → Rat := fun β γ e => if Z (some (γ, e)) then 0 else β γ e
  have hcwZ : ∀ b β w γ e n, Z (some (γ, e)) →
      cwt G'.ls w (β' β) γ e ((G.extent b).rc γ e) n ≤ 0 := fun b β w γ e n hz => by
    have h0 : ftot ((G.extent b).rc γ e) n = 0 := ftot_zero (fun k => (hZ γ e hz b k).2) n
    have hb : β' β γ e = 0 := by simp [β', hz]
    unfold cwt; rw [h0, hb]; split
    · grind
    · split <;> grind
  have hmZ : ∀ b β w n N E, Z w → (G.extent b).mass G'.ls (β' β) w n N E ≤ 0 :=
    fun b β w n N E hw => by
      have h1 : ftot ((G.extent b).tg w) n = 0 := ftot_zero (hZt w hw b) n
      have h2 := gsum_zero (f := fun γ e => cwt G'.ls w (β' β) γ e ((G.extent b).rc γ e) n)
        (fun γ e => by
          by_cases hze : Z (some (γ, e))
          · exact hcwZ b β w γ e n hze
          · unfold cwt
            rw [if_neg (fun h => hze (hZc w γ e e hw h (Nat.le_refl _))),
              if_neg (fun ⟨e', he, h⟩ => hze (hZc w γ e e' hw h (Nat.le_of_lt he)))]
            exact Rat.le_refl) N E
      simp only [ECell.mass]; grind
  -- a world outside `Z` weighs at most what it weighed before
  have hmW : ∀ b β w n N E, Act G'.ls w → ¬ Z w →
      (G.extent b).mass G'.ls (β' β) w n N E ≤ (G.extent b).mass G.ls β w n N E :=
    fun b β w n N E hw hz => by
      have := gsum_le (f := fun γ e => cwt G'.ls w (β' β) γ e ((G.extent b).rc γ e) n)
        (g := fun γ e => cwt G.ls w β γ e ((G.extent b).rc γ e) n) (fun γ e => by
          by_cases hze : Z (some (γ, e))
          · exact Rat.le_trans (hcwZ b β w γ e n hze) (cwt_nonneg _ _ _ _ _ _ _)
          · have hb : β' β γ e = β γ e := by simp [β', hze]
            unfold cwt
            by_cases h1 : G'.ls γ e w
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
  have hu' : G'.ls.Uniq := fun γ e e' p p' ⟨_, h1⟩ ⟨_, h2⟩ => (hlv γ).ls_uniq h1 h2
  refine ⟨⟨hlv, fun b => ?_⟩, fun m ht b => ?_⟩
  · rw [hx]
    obtain ⟨hvb, hbal, hf⟩ := hv.2 b
    refine ⟨hvb, fun n N E => ?_, fun γ e k hfu => ?_⟩
    · obtain ⟨β, h1, h2⟩ := hbal n N E
      refine ⟨β' β, Rat.le_trans (hmW b β none n N E .root hZn) h1, fun γ e hγ he ha => ?_⟩
      by_cases hz : Z (some (γ, e))
      · have := hmZ b β _ n N E hz; simp only [β', hz, ↓reduceIte]; exact this
      · have hb : β' β γ e = β γ e := by simp [β', hz]
        rw [hb]
        exact Rat.le_trans (hmW b β _ n N E ha hz) (h2 γ e hγ he ((hA _ ha).resolve_right hz))
    · rcases hF _ hfu with h | h
      · exact hf γ e k h
      · exact hZ γ e h b k
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
  have hl : ∀ γ', γ' ≠ γ → ((Ghost.at γ c').add g).led γ' = ((Ghost.at γ c).add g).led γ' :=
    fun γ' hne => by simp [Ghost.add, Ghost.at, hne]
  have hep : ∀ γ' x p, ((Ghost.at γ c').add g).ls γ' x p ↔ ((Ghost.at γ c).add g).ls γ' x p := by
    intro γ' x p
    by_cases hne : γ' = γ
    · subst hne; simpa [Ghost.ls, Ghost.add, Ghost.at] using hc.2 x p
    · unfold Ghost.ls; rw [hl γ' hne]
  have e : ((Ghost.at γ c').add g).ls = ((Ghost.at γ c).add g).ls :=
    funext fun γ' => funext fun x => funext fun p => propext (hep γ' x p)
  refine ⟨⟨⟨fun γ' => ?_, fun b => ?_⟩, N + γ + 1, fun γ' hγ => ⟨?_, ?_, fun γ'' e' M e₀ => ?_⟩⟩,
    fun m ht => ExtTrue.congr hx e ht⟩
  · by_cases hne : γ' = γ
    · subst hne; simpa [Ghost.add, Ghost.at] using hc.1
    · rw [hl γ' hne]; exact hv.1 γ'
  · rw [hx, e]; exact hv.2 b
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

/-! ## Frame-preserving updates -/

/-- `P` can become `P'` by a ghost update: every resource of `P` is replaced, with the same bytes,
knowledge and extent claims, by one of `P'` that composes with every ghost frame the old one
composed with, and under whose ledgers every extent claim that was true stays true. -/
def Upd (P P' : FAssn) : Prop :=
  ∀ r, P r → ∀ g, Ghost.Ok r.gh g →
    ∃ r', P' r' ∧ r'.heap = r.heap ∧ r'.know = r.know ∧ r'.gh.extent = r.gh.extent ∧ Ghost.Ok r'.gh g ∧
      ∀ m, ExtTrue m (r.gh.add g) → ExtTrue m (r'.gh.add g)

/-- What an authority `●(e, M)` and a token `◯(e, i ↦ g)` say about a frame `d` they compose
with: the map records the grant, and `d` holds no token for it. -/
theorem GCell.valid_pair {e i : Nat} {M : GMap} {p : STag} {g : GRegion} {d : GCell}
    (hv : ((GCell.auth1 e M p).add ((GCell.frag1 e i g).add d)).Valid) :
    (∀ x, d.auth x = 0) ∧ M i = some g ∧ d.frag (e, i, g) = 0 ∧ d.TokOk e M ∧
      ∀ e' j g', e < e' → d.frag (e', j, g') = 0 := by
  rw [GCell.valid_auth1_add] at hv
  obtain ⟨h1, h2, h3⟩ := hv
  simp only [GCell.TokOk, GCell.add, GCell.frag1] at h1 h2 h3
  have hi := h2 i g
  simp only [↓reduceIte] at hi
  refine ⟨fun x => by simpa using h1 x, hi.2 (by omega), by omega, fun j g' => ?_,
    fun e' j g' he => ?_⟩
  · have := h2 j g'
    exact ⟨by omega, fun hp => this.2 (by omega)⟩
  · have := h3 e' j g' he; omega

/-- The name of a tag's ledger, plus one (`0` for the root). -/
def STag.name : STag → Nat
  | none => 0
  | some (γ, _) => γ + 1

namespace Upd

variable {P P' P'' R : FAssn}

theorem of_imp (h : ∀ r, P r → P' r) : Upd P P' := fun r hp _ hg => ⟨r, h r hp, rfl, rfl, rfl, hg, fun _ h => h⟩

theorem trans (h₁ : Upd P P') (h₂ : Upd P' P'') : Upd P P'' := fun r hp g hg => by
  obtain ⟨r₁, h1, e1, k1, x1, g1, t1⟩ := h₁ r hp g hg
  obtain ⟨r₂, h2, e2, k2, x2, g2, t2⟩ := h₂ r₁ h1 g g1
  exact ⟨r₂, h2, e2.trans e1, k2.trans k1, x2.trans x1, g2, fun m h => t2 m (t1 m h)⟩

/-- Updates frame. -/
theorem frame (h : Upd P P') : Upd (P ⋆ R) (P' ⋆ R) := by
  rintro _ ⟨r₁, r₂, hd, rfl, hp, hr⟩ g hg
  obtain ⟨r₁', hp', e, k, x, hg', ht⟩ := h r₁ hp (r₂.gh.add g) (Ghost.Ok.assoc.mp hg)
  refine ⟨⟨r₁'.heap ∪ r₂.heap, r₁'.know.union r₂.know, r₁'.gh.add r₂.gh⟩,
    ⟨r₁', r₂, by rw [e]; exact hd, rfl, hp', hr⟩, by simp [e], by simp [k],
    by simp [Ghost.add, x], Ghost.Ok.assoc.mpr hg', fun m hm => ?_⟩
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
  exact ⟨_, hp', rfl, rfl, rfl, h1, h2⟩

/-- **A new ledger** with parent tag `p`, at a name no frame uses (no ledger, no tag, no parent
link), with no grant. Its tags are lent from shares tagged `p` (`EUpd.lendT`) and die with `p`. -/
theorem alloc (p : STag) : Upd emp (FAssn.ex fun γ => gauthP γ 0 GMap.empty p) := by
  rintro r ⟨h0, k0, g0⟩ g hg
  rw [g0] at hg
  unfold Ghost.Ok at hg
  rw [Ghost.unit_add] at hg
  obtain ⟨hv, N, hN⟩ := hg
  let ν := N + p.name
  have hνN : N ≤ ν := Nat.le_add_right _ _
  have hNu := (hN ν hνN).1
  have hNt := (hN ν hνN).2.1
  have hNp := (hN ν hνN).2.2
  have hpν : ∀ e, p ≠ some (ν, e) := fun e he => by
    have h1 : p.name = ν + 1 := by rw [he]; rfl
    have h2 : ν = N + p.name := rfl
    omega
  have h0ν : ∀ x, (g.led ν).auth x = 0 := fun x => by rw [hNu]; rfl
  let G' := (Ghost.at ν (GCell.auth1 0 GMap.empty p)).add g
  have hx : G'.extent = g.extent := by funext b; simp [G', Ghost.add, Ghost.at]
  have hl : ∀ γ', γ' ≠ ν → G'.led γ' = g.led γ' := fun γ' hne => by
    simp [G', Ghost.add, Ghost.at, hne]
  have hlN : G'.led ν = GCell.auth1 0 GMap.empty p := by simp [G', Ghost.add, Ghost.at, hNu]
  have hls : ∀ γ e q, G'.ls γ e q ↔ (γ = ν ∧ e = 0 ∧ q = p) ∨ (γ ≠ ν ∧ g.ls γ e q) :=
    fun γ e q => Ghost.ls_at_add h0ν
  -- no ledger names `ν` as its parent
  have hnoν : ∀ γ e e₀, ¬ g.ls γ e (some (ν, e₀)) := fun γ e e₀ ⟨M, h⟩ => by
    have := hNp γ e M e₀; omega
  let Z : STag → Prop := fun t => Fut g.ls t ∨ ∃ e, t = some (ν, e)
  obtain ⟨hv', ht'⟩ := Ghost.valid_led_change (G := g) (G' := G') Z hx hv
    (fun γ => by
      by_cases h : γ = ν
      · subst h; rw [hlN]
        have h := (GCell.valid_auth1_add (e := 0) (M := GMap.empty) (p := p) (d := GCell.unit)).mpr
          ⟨fun _ => rfl, fun _ _ => ⟨Nat.zero_le _, fun h => absurd h (Nat.lt_irrefl 0)⟩, fun _ _ _ _ => rfl⟩
        rwa [GCell.add_unit] at h
      · rw [hl γ h]; exact hv.1 γ)
    (fun γ e hz b k => by
      rcases hz with hz | ⟨e', he⟩
      · exact (hv.2 b).2.2 γ e k hz
      · cases he; exact hNt b e k)
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
  refine ⟨⟨FHeap.empty, Know.none, Ghost.at ν (GCell.auth1 0 GMap.empty p)⟩, ⟨ν, rfl, rfl, rfl⟩,
    h0.symm, k0.symm, by rw [g0]; funext b; simp [Ghost.at, Ghost.unit],
    ⟨hv', ν + 1, fun γ hγ => ⟨?_, ?_, fun γ' e' M e => ?_⟩⟩, fun m hm => ?_⟩
  · rw [hl γ (by omega)]; exact (hN γ (by omega)).1
  · rw [hx]; exact (hN γ (by omega)).2.1
  · show (G'.led γ').auth _ = 0
    by_cases h : γ' = ν
    · rw [h, hlN]; simp only [GCell.auth1]
      refine if_neg fun x => ?_
      simp only [Prod.mk.injEq] at x
      have h1 : p.name = γ + 1 := by rw [← x.2.2]; rfl
      have h2 : ν = N + p.name := rfl
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
        obtain ⟨h1, h2, h3⟩ := GCell.valid_auth1_add.mp hv
        simp only [GCell.add, GCell.frag1]
        refine ⟨fun x => by simpa using h1 x, fun j g' => ?_, fun e' j g' he => ?_⟩
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
        obtain ⟨h1, hM, h0, h2, h3⟩ := GCell.valid_pair hv
        refine GCell.valid_auth1_add.mpr ⟨h1, fun j g' => ⟨(h2 j g').1, fun hp => ?_⟩, h3⟩
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

/-- **The next epoch**, with no grant and the same parent: every outstanding token becomes stale,
and so does every share tagged with the old epoch or with a tag below it (`Ghost.valid_led_change`
with the future tags as `Z`); the old epoch's receipts stay live (`EUpd.revoke`). -/
theorem bump {γ e : Nat} {M : GMap} {p : STag} : Upd (gauthP γ e M p) (gauthP γ (e + 1) GMap.empty p) := by
  rintro r ⟨h0, k0, g0⟩ g hg
  rw [g0] at hg
  obtain ⟨hv, N, hN⟩ := hg
  let G := (Ghost.at γ (GCell.auth1 e M p)).add g
  let G' := (Ghost.at γ (GCell.auth1 (e + 1) GMap.empty p)).add g
  have hlv := hv.1 γ
  simp only [Ghost.add, Ghost.at, ↓reduceIte] at hlv
  obtain ⟨hd1, -, hd3⟩ := GCell.valid_auth1_add.mp hlv
  have hx : G'.extent = G.extent := by funext b; simp [G, G', Ghost.add, Ghost.at]
  have hl : ∀ γ', γ' ≠ γ → G'.led γ' = G.led γ' := fun γ' hne => by
    simp [G, G', Ghost.add, Ghost.at, hne]
  have hls : ∀ γ' x q, G.ls γ' x q ↔ (γ' = γ ∧ x = e ∧ q = p) ∨ (γ' ≠ γ ∧ g.ls γ' x q) :=
    fun γ' x q => Ghost.ls_at_add hd1
  have hls' : ∀ γ' x q, G'.ls γ' x q ↔ (γ' = γ ∧ x = e + 1 ∧ q = p) ∨ (γ' ≠ γ ∧ g.ls γ' x q) :=
    fun γ' x q => Ghost.ls_at_add hd1
  have hG : G.ls γ e p := (hls γ e p).mpr (.inl ⟨rfl, rfl, rfl⟩)
  -- a tag of another ledger has the same status
  have hoth : ∀ γ' x q, γ' ≠ γ → (G'.ls γ' x q ↔ G.ls γ' x q) := fun γ' x q hne => by
    rw [hls, hls']; simp [hne]
  obtain ⟨hv', ht'⟩ := Ghost.valid_led_change (G := G) (G' := G') (Fut G.ls) hx hv
    (fun γ' => by
      by_cases h : γ' = γ
      · subst h
        simp only [G', Ghost.add, Ghost.at, ↓reduceIte]
        exact GCell.valid_auth1_add.mpr ⟨hd1, fun i g => by simp [hd3 (e + 1) i g (by omega)],
          fun e' i g he => hd3 e' i g (by omega)⟩
      · rw [hl γ' h]; exact hv.1 γ')
    (fun γ' x hz b k => (hv.2 b).2.2 γ' x k hz)
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
  refine ⟨⟨FHeap.empty, Know.none, Ghost.at γ (GCell.auth1 (e + 1) GMap.empty p)⟩, ⟨rfl, rfl, rfl⟩,
    h0.symm, k0.symm, by rw [g0]; funext b; simp [Ghost.at],
    ⟨hv', N + γ + 1, fun γ' hγ => ⟨?_, ?_, fun γ'' x' M' x => ?_⟩⟩,
    fun m hm => by rw [g0] at hm; exact ht' m hm⟩
  · rw [hl γ' (by omega)]; exact (hN γ' (by omega)).1
  · rw [hx]; exact (hN γ' (by omega)).2.1
  · have hold := (hN γ' (by omega)).2.2
    by_cases h : γ'' = γ
    · subst h
      have h1 := hold γ'' x' M' x
      have h2 := hold γ'' e M x
      simp only [G, G', Ghost.add, Ghost.at, ↓reduceIte, GCell.add, GCell.auth1] at h1 h2 ⊢
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
  obtain ⟨r', hp', e, k, x, hg, ht'⟩ := hu r hp rF.gh hh.ghost.1
  exact ht m r' rF ⟨by rw [e]; exact hh.disj, by rw [e]; exact hh.heap, by rw [k]; exact hh.know,
    hh.knowF, ⟨hg, ht' m hh.ghost.2⟩⟩ hp' hs

/-- A ghost update of the postcondition. -/
theorem upd_post (ht : FTriple P c Q) (hu : ∀ v, Upd (Q v) (Q' v)) : FTriple P c Q' := by
  intro m r rF hh hp hs
  have := ht m r rF hh hp hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', hh', hq, hs'⟩ := this
    obtain ⟨r'', hq', e, k, x, hg, ht'⟩ := hu _ r' hq rF.gh hh'.ghost.1
    exact ⟨r'', ⟨by rw [e]; exact hh'.disj, by rw [e]; exact hh'.heap, by rw [k]; exact hh'.know,
      hh'.knowF, ⟨hg, ht' _ hh'.ghost.2⟩⟩, hq', hs'⟩

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

end Full
end Zig
