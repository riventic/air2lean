import ZigLean.Sep.Full.Triple

/-!
# Ghost epoch ledgers of named grants (`docs/sep-full-state.md` §Ghost state)

A ghost name `γ` holds a ledger: an authority `gauth γ e M` (the current epoch `e` and the grant
map `M`: grant id ↦ the region granted under it) and tokens `gfrag γ e i g` (grant `i` of epoch
`e`, naming region `g`). Ghost state lives only in resources (`Res.gh`); no primitive reads or
changes it, and `Holds` requires the ghost states of a resource and its frame to compose
(`Ghost.Ok`). It changes only by **frame-preserving updates** (`Upd`), applied to a triple's pre-
or postcondition (`FTriple.upd`, `FTriple.upd_post`):

* `Upd.alloc`: a new ledger `gauth γ 0 GMap.empty` at a name no frame uses;
* `Upd.issue`: a new grant under an unused id, and its token;
* `Upd.retire`: a token of the current epoch given back, its grant removed;
* `Upd.reassign`: a grant of the current epoch re-pointed at another region (resize in place);
* `Upd.bump`: the next epoch with no grant, every outstanding token stale (revocation without
  collection).

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
/-- The authority `●(e, M)`. -/
noncomputable def auth1 (e : Nat) (M : GMap) : GCell := ⟨fun x => if x = (e, M) then 1 else 0, fun _ => 0⟩

/-- The token `◯(e, i ↦ g)`. -/
def frag1 (e i : Nat) (g : GRegion) : GCell := ⟨fun _ => 0, fun t => if t = (e, i, g) then 1 else 0⟩

theorem valid_auth1_add {e : Nat} {M : GMap} {d : GCell} :
    ((auth1 e M).add d).Valid ↔ (∀ x, d.auth x = 0) ∧ d.TokOk e M ∧ ∀ e' i g, e < e' → d.frag (e', i, g) = 0 := by
  constructor
  · rintro (h | ⟨e', M', h1, h2, h3, h4⟩)
    · have := h (e, M); simp [add, auth1] at this
    · by_cases hx : (e', M') = (e, M)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
        refine ⟨fun x => ?_, fun i g => by simpa [add, auth1] using h3 i g,
          fun e'' i g he => by simpa [add, auth1] using h4 e'' i g he⟩
        by_cases hx' : x = (e', M')
        · subst hx'; simp [add, auth1] at h1; omega
        · have := h2 x hx'; simp [add, auth1, hx'] at this; omega
      · have := h2 (e, M) (Ne.symm hx); simp [add, auth1] at this
  · rintro ⟨h1, h2, h3⟩
    refine .inr ⟨e, M, by simp [add, auth1, h1], fun x hx => by simp [add, auth1, hx, h1],
      fun i g => by simpa [add, auth1] using h2 i g, fun e' i g he => by simpa [add, auth1] using h3 e' i g he⟩

theorem frag1_add (e i : Nat) (g : GRegion) (d : GCell) :
    (frag1 e i g).add d = ⟨d.auth, fun t => (if t = (e, i, g) then 1 else 0) + d.frag t⟩ := by
  ext <;> simp [add, frag1]

end GCell

/-! ## Ghost states with one name -/

/-- The ghost state with cell `c` at `γ` and nothing elsewhere. -/
def Ghost.at (γ : Nat) (c : GCell) : Ghost :=
  ⟨fun γ' => if γ' = γ then c else GCell.unit, fun _ => ECell.unit⟩

theorem Ghost.at_add (γ : Nat) (c c' : GCell) : (Ghost.at γ c).add (Ghost.at γ c') = Ghost.at γ (c.add c') := by
  ext1
  · funext γ'; simp only [Ghost.add, Ghost.at]; split <;> simp
  · funext b; simp [Ghost.add, Ghost.at]

theorem tagWt_congr {ep ep' : Nat → Nat → Prop} {γ : Nat} (h : ∀ x, ep' γ x ↔ ep γ x) :
    tagWt ep' γ = tagWt ep γ := by
  funext e T R n; unfold tagWt
  have h1 : (∃ e', e < e' ∧ ep' γ e') ↔ (∃ e', e < e' ∧ ep γ e') :=
    exists_congr fun x => and_congr_right fun _ => h x
  by_cases a : ep γ e
  · rw [if_pos ((h e).mpr a), if_pos a]
  · rw [if_neg (fun x => a ((h e).mp x)), if_neg a]
    by_cases b : ∃ e', e < e' ∧ ep γ e'
    · rw [if_pos (h1.mpr b), if_pos b]
    · rw [if_neg (fun x => b (h1.mp x)), if_neg b]

/-- **A change of one ledger** keeps validity and the truth of the extent claims when every tag of
that ledger weighs at most as much as before, no tag lies after its new epoch, and no claim that was
dormant becomes live. -/
theorem Ghost.valid_led_change {G G' : Ghost} {γ : Nat}
    (hx : G'.extent = G.extent) (hl : ∀ γ', γ' ≠ γ → G'.led γ' = G.led γ')
    (hv : G.Valid) (hlv : (G'.led γ).Valid)
    (hW : ∀ b x n, tagWt G'.ep γ x ((G.extent b).tsh γ x) ((G.extent b).rc γ x) n ≤
      tagWt G.ep γ x ((G.extent b).tsh γ x) ((G.extent b).rc γ x) n)
    (hF : ∀ b x x' k, G'.ep γ x → x < x' →
      ((G.extent b).tsh γ x' k).val = 0 ∧ ((G.extent b).rc γ x' k).val = 0)
    (hR : ∀ b k, (G.extent b).Req G'.ep k → (G.extent b).Req G.ep k) :
    G'.Valid ∧ ∀ m, ExtTrue m G → ExtTrue m G' := by
  have hep : ∀ γ', γ' ≠ γ → ∀ x, G'.ep γ' x ↔ G.ep γ' x := fun γ' h x => by
    unfold Ghost.ep; rw [hl γ' h]
  refine ⟨⟨fun γ' => ?_, fun b => ?_⟩, fun m ht b => ?_⟩
  · by_cases h : γ' = γ
    · subst h; exact hlv
    · rw [hl γ' h]; exact hv.1 γ'
  · rw [hx]
    obtain ⟨hvb, hw, hf⟩ := hv.2 b
    refine ⟨hvb, fun n N E => Rat.le_trans ?_ (hw n N E), fun γ' x x' k he hlt => ?_⟩
    · have := gsum_le (f := fun γ' e => tagWt G'.ep γ' e ((G.extent b).tsh γ' e) ((G.extent b).rc γ' e) n)
        (g := fun γ' e => tagWt G.ep γ' e ((G.extent b).tsh γ' e) ((G.extent b).rc γ' e) n)
        (fun γ' x => by
          by_cases h : γ' = γ
          · subst h; exact hW b x n
          · rw [tagWt_congr (hep γ' h)]; exact Rat.le_refl) N E
      simp only [ECell.wsum]; grind
    · by_cases h : γ' = γ
      · subst h; exact hF b x x' k he hlt
      · exact hf γ' x x' k ((hep γ' h x).mp he) hlt
  · obtain ⟨ha, hs⟩ := ht b
    rw [hx]
    exact ⟨ha, fun k hk => hs k (hR b k hk)⟩

theorem ExtTrue.congr {m : Mem} {G G' : Ghost} (hx : G'.extent = G.extent)
    (hep : ∀ γ x, G'.ep γ x ↔ G.ep γ x) (h : ExtTrue m G) : ExtTrue m G' := fun b => by
  have e : G'.ep = G.ep := funext fun γ => funext fun x => propext (hep γ x)
  rw [hx, e]; exact h b

/-- **A local update** at one name: if every cell that `c` composes validly with also composes
validly with `c'`, at the same epoch, replacing `c` by `c'` keeps every frame valid and every
extent claim true. -/
theorem Ghost.Ok.update {γ : Nat} {c c' : GCell} {g : Ghost}
    (h : ∀ d, (c.add d).Valid → (c'.add d).Valid ∧
      ∀ e, (∃ M, 0 < (c'.add d).auth (e, M)) ↔ (∃ M, 0 < (c.add d).auth (e, M)))
    (hok : Ghost.Ok (Ghost.at γ c) g) :
    Ghost.Ok (Ghost.at γ c') g ∧
      ∀ m, ExtTrue m ((Ghost.at γ c).add g) → ExtTrue m ((Ghost.at γ c').add g) := by
  obtain ⟨hv, N, hN⟩ := hok
  have hc := h (g.led γ) (by simpa [Ghost.add, Ghost.at] using hv.1 γ)
  have hx : ((Ghost.at γ c').add g).extent = ((Ghost.at γ c).add g).extent := by
    funext b; simp [Ghost.add, Ghost.at]
  have hl : ∀ γ', γ' ≠ γ → ((Ghost.at γ c').add g).led γ' = ((Ghost.at γ c).add g).led γ' :=
    fun γ' hne => by simp [Ghost.add, Ghost.at, hne]
  have hep : ∀ γ' x, ((Ghost.at γ c').add g).ep γ' x ↔ ((Ghost.at γ c).add g).ep γ' x := by
    intro γ' x
    by_cases hne : γ' = γ
    · subst hne; simpa [Ghost.ep, Ghost.add, Ghost.at] using hc.2 x
    · unfold Ghost.ep; rw [hl γ' hne]
  have e : ((Ghost.at γ c').add g).ep = ((Ghost.at γ c).add g).ep :=
    funext fun γ' => funext fun x => propext (hep γ' x)
  refine ⟨⟨⟨fun γ' => ?_, fun b => ?_⟩, N + γ + 1, fun γ' hγ => ⟨?_, ?_⟩⟩,
    fun m ht => ExtTrue.congr hx hep ht⟩
  · by_cases hne : γ' = γ
    · subst hne; simpa [Ghost.add, Ghost.at] using hc.1
    · rw [hl γ' hne]; exact hv.1 γ'
  · rw [hx, e]; exact hv.2 b
  · have := (hN γ' (by omega)).1
    rw [hl γ' (by omega)]; exact this
  · rw [hx]; exact (hN γ' (by omega)).2

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

/-- The authority of ledger `γ`: epoch `e`, grant map `M`. Owns no bytes, no knowledge. -/
def gauth (γ e : Nat) (M : GMap) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.at γ (GCell.auth1 e M)

/-- A token of ledger `γ`: grant `i` of epoch `e`, naming region `g`. -/
def gfrag (γ e i : Nat) (g : GRegion) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.at γ (GCell.frag1 e i g)

/-- The resource of `gauth γ e M ⋆ gfrag γ e i g`. -/
theorem gauth_gfrag {γ e i : Nat} {M : GMap} {g : GRegion} {r : Res}
    (h : (gauth γ e M ⋆ gfrag γ e i g) r) :
    r = ⟨FHeap.empty, Know.none, Ghost.at γ ((GCell.auth1 e M).add (GCell.frag1 e i g))⟩ := by
  obtain ⟨r₁, r₂, -, rfl, ⟨h1, k1, g1⟩, ⟨h2, k2, g2⟩⟩ := h
  rw [h1, h2, k1, k2, g1, g2, FHeap.union_empty, Know.union_none, Ghost.at_add]

theorem gauth_gfrag_intro {γ e i : Nat} {M : GMap} {g : GRegion} :
    (gauth γ e M ⋆ gfrag γ e i g)
      ⟨FHeap.empty, Know.none, Ghost.at γ ((GCell.auth1 e M).add (GCell.frag1 e i g))⟩ :=
  ⟨⟨FHeap.empty, Know.none, Ghost.at γ (GCell.auth1 e M)⟩,
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

/-- The epochs of a ledger cell with the authority `●(e, M)`: `e` and the frame's. -/
theorem GCell.ep_auth1_add {e x : Nat} {M : GMap} {d : GCell} :
    (∃ N, 0 < ((GCell.auth1 e M).add d).auth (x, N)) ↔ x = e ∨ ∃ N, 0 < d.auth (x, N) := by
  constructor
  · rintro ⟨N, h⟩
    simp only [GCell.add, GCell.auth1] at h
    by_cases hx : (x, N) = (e, M)
    · exact .inl (by cases hx; rfl)
    · rw [if_neg hx] at h; exact .inr ⟨N, by omega⟩
  · rintro (rfl | ⟨N, h⟩)
    · exact ⟨M, by simp [GCell.add, GCell.auth1]; omega⟩
    · exact ⟨N, by simp only [GCell.add]; omega⟩

theorem GCell.frag1_add_auth (e i : Nat) (g : GRegion) (d : GCell) :
    ((GCell.frag1 e i g).add d).auth = d.auth := by
  funext x; simp [GCell.add, GCell.frag1]

/-- What an authority `●(e, M)` and a token `◯(e, i ↦ g)` say about a frame `d` they compose
with: the map records the grant, and `d` holds no token for it. -/
theorem GCell.valid_pair {e i : Nat} {M : GMap} {g : GRegion} {d : GCell}
    (hv : ((GCell.auth1 e M).add ((GCell.frag1 e i g).add d)).Valid) :
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

/-- A local update of a ghost-only resource at one name, at the same epoch. -/
theorem single {γ : Nat} {c c' : GCell} {P P' : FAssn}
    (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, Ghost.at γ c⟩)
    (hp' : P' ⟨FHeap.empty, Know.none, Ghost.at γ c'⟩)
    (h : ∀ d, (c.add d).Valid → (c'.add d).Valid ∧
      ∀ e, (∃ M, 0 < (c'.add d).auth (e, M)) ↔ (∃ M, 0 < (c.add d).auth (e, M))) :
    Upd P P' := fun r hr g hg => by
  have e := hp r hr
  subst e
  obtain ⟨h1, h2⟩ := Ghost.Ok.update h hg
  exact ⟨_, hp', rfl, rfl, rfl, h1, h2⟩

/-- **A new ledger** at a name no frame uses (no ledger and no tag), with no grant. -/
theorem alloc : Upd emp (FAssn.ex fun γ => gauth γ 0 GMap.empty) := by
  rintro r ⟨h0, k0, g0⟩ g hg
  rw [g0] at hg
  unfold Ghost.Ok at hg
  rw [Ghost.unit_add] at hg
  obtain ⟨hv, N, hN⟩ := hg
  have hNu := (hN N (Nat.le_refl _)).1
  have hNt := (hN N (Nat.le_refl _)).2
  let G' := (Ghost.at N (GCell.auth1 0 GMap.empty)).add g
  have hx : G'.extent = g.extent := by funext b; simp [G', Ghost.add, Ghost.at]
  have hl : ∀ γ', γ' ≠ N → G'.led γ' = g.led γ' := fun γ' hne => by
    simp [G', Ghost.add, Ghost.at, hne]
  have hlN : G'.led N = GCell.auth1 0 GMap.empty := by simp [G', Ghost.add, Ghost.at, hNu]
  have hepN : ∀ x, ¬ g.ep N x := fun x ⟨M, h⟩ => by rw [hNu] at h; simp [GCell.unit] at h
  have hz : ∀ b x, ftot ((g.extent b).tsh N x) = fun _ => 0 := fun b x => funext (ftot_zero fun k => (hNt b x k).1)
  have hzr : ∀ b x, ftot ((g.extent b).rc N x) = fun _ => 0 := fun b x => funext (ftot_zero fun k => (hNt b x k).2)
  obtain ⟨hv', ht'⟩ := Ghost.valid_led_change (G := g) (G' := G') (γ := N) hx hl hv
    (by
      rw [hlN]
      have h := (GCell.valid_auth1_add (e := 0) (M := GMap.empty) (d := GCell.unit)).mpr
        ⟨fun _ => rfl, fun _ _ => ⟨Nat.zero_le _, fun h => absurd h (Nat.lt_irrefl 0)⟩, fun _ _ _ _ => rfl⟩
      rwa [GCell.add_unit] at h)
    (fun b x n => by
      have := tagWt_nonneg g.ep N x ((g.extent b).tsh N x) ((g.extent b).rc N x) n
      unfold tagWt; rw [hz, hzr]; split
      · grind
      · split <;> grind)
    (fun b x x' k _ _ => hNt b x' k)
    (fun b k hk => by
      rcases hk with hk | ⟨γ, x, ⟨he, hp⟩ | ⟨he, hp⟩⟩
      · exact .inl hk
      · by_cases hγ : γ = N
        · subst hγ; rw [(hNt b x k).1] at hp; exact absurd hp (Rat.lt_irrefl)
        · have : G'.ep γ x ↔ g.ep γ x := by unfold Ghost.ep; rw [hl γ hγ]
          exact .inr ⟨γ, x, .inl ⟨this.mp he, hp⟩⟩
      · by_cases hγ : γ = N
        · subst hγ; rw [(hNt b x k).2] at hp; exact absurd hp (Rat.lt_irrefl)
        · have : ∀ x, G'.ep γ x ↔ g.ep γ x := fun x => by unfold Ghost.ep; rw [hl γ hγ]
          refine .inr ⟨γ, x, .inr ⟨?_, hp⟩⟩
          rcases he with he | ⟨x', h1, h2⟩
          · exact .inl ((this x).mp he)
          · exact .inr ⟨x', h1, (this x').mp h2⟩)
  refine ⟨⟨FHeap.empty, Know.none, Ghost.at N (GCell.auth1 0 GMap.empty)⟩, ⟨N, rfl, rfl, rfl⟩,
    h0.symm, k0.symm, by rw [g0]; funext b; simp [Ghost.at, Ghost.unit], ⟨hv', N + 1, fun γ hγ => ⟨?_, ?_⟩⟩,
    fun m hm => ?_⟩
  · rw [hl γ (by omega)]; exact (hN γ (by omega)).1
  · rw [hx]; exact (hN γ (by omega)).2
  · rw [g0, Ghost.unit_add] at hm; exact ht' m hm

/-- **Issue a grant** of the current epoch under an unused id `i`, naming region `g`. -/
theorem issue {γ e i : Nat} {M : GMap} (g : GRegion) (hi : M i = none) :
    Upd (gauth γ e M) (gauth γ e (M.set i (some g)) ⋆ gfrag γ e i g) :=
  single (c := GCell.auth1 e M) (fun r ⟨h, k, gh⟩ => by rw [res_eta r, h, k, gh])
    gauth_gfrag_intro fun d hv => by
      refine ⟨?_, fun x => ?_⟩
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
      · rw [GCell.add_assoc, GCell.ep_auth1_add, GCell.ep_auth1_add, GCell.frag1_add_auth]

/-- **Give back a grant** of the current epoch. -/
theorem retire {γ e i : Nat} {M : GMap} {g : GRegion} :
    Upd (gauth γ e M ⋆ gfrag γ e i g) (gauth γ e (M.set i none)) :=
  single (c := (GCell.auth1 e M).add (GCell.frag1 e i g)) (fun _ h => gauth_gfrag h)
    ⟨rfl, rfl, rfl⟩ fun d hv => by
      refine ⟨?_, fun x => ?_⟩
      · rw [GCell.add_assoc] at hv
        obtain ⟨h1, hM, h0, h2, h3⟩ := GCell.valid_pair hv
        refine GCell.valid_auth1_add.mpr ⟨h1, fun j g' => ⟨(h2 j g').1, fun hp => ?_⟩, h3⟩
        have hj := (h2 j g').2 hp
        by_cases hji : j = i
        · subst hji; rw [hM] at hj; cases hj; omega
        · rw [GMap.set_ne _ _ hji]; exact hj
      · rw [GCell.add_assoc, GCell.ep_auth1_add, GCell.ep_auth1_add, GCell.frag1_add_auth]

/-- **Re-point a grant** of the current epoch at another region (a resize in place). -/
theorem reassign {γ e i : Nat} {M : GMap} {g : GRegion} (g' : GRegion) :
    Upd (gauth γ e M ⋆ gfrag γ e i g) (gauth γ e (M.set i (some g')) ⋆ gfrag γ e i g') := by
  have h := issue (γ := γ) (e := e) g' (GMap.set_same M i none)
  rw [GMap.set_set] at h
  exact trans retire h

/-- **The next epoch**, with no grant: every outstanding token becomes stale, and so does every
share tagged with the old epoch (its receipts stay live, `EUpd.revoke`). -/
theorem bump {γ e : Nat} {M : GMap} : Upd (gauth γ e M) (gauth γ (e + 1) GMap.empty) := by
  rintro r ⟨h0, k0, g0⟩ g hg
  rw [g0] at hg
  obtain ⟨hv, N, hN⟩ := hg
  let G := (Ghost.at γ (GCell.auth1 e M)).add g
  let G' := (Ghost.at γ (GCell.auth1 (e + 1) GMap.empty)).add g
  have hlv := hv.1 γ
  simp only [Ghost.add, Ghost.at, ↓reduceIte] at hlv
  obtain ⟨hd1, -, hd3⟩ := GCell.valid_auth1_add.mp hlv
  have hx : G'.extent = G.extent := by funext b; simp [G, G', Ghost.add, Ghost.at]
  have hl : ∀ γ', γ' ≠ γ → G'.led γ' = G.led γ' := fun γ' hne => by
    simp [G, G', Ghost.add, Ghost.at, hne]
  have hep : ∀ x, G.ep γ x ↔ x = e := fun x => by
    simp only [G, Ghost.ep, Ghost.add, Ghost.at, ↓reduceIte]
    rw [GCell.ep_auth1_add]; simp [hd1]
  have hep' : ∀ x, G'.ep γ x ↔ x = e + 1 := fun x => by
    simp only [G', Ghost.ep, Ghost.add, Ghost.at, ↓reduceIte]
    rw [GCell.ep_auth1_add]; simp [hd1]
  have hF : ∀ b x' k, e < x' → ((G.extent b).tsh γ x' k).val = 0 ∧ ((G.extent b).rc γ x' k).val = 0 :=
    fun b x' k hlt => (hv.2 b).2.2 γ e x' k ((hep e).mpr rfl) hlt
  obtain ⟨hv', ht'⟩ := Ghost.valid_led_change (G := G) (G' := G') (γ := γ) hx hl hv
    (by
      simp only [G', Ghost.add, Ghost.at, ↓reduceIte]
      exact GCell.valid_auth1_add.mpr ⟨hd1, fun i g => by simp [hd3 (e + 1) i g (by omega)],
        fun e' i g he => hd3 e' i g (by omega)⟩)
    (fun b x n => by
      have hnn := tagWt_nonneg G.ep γ x ((G.extent b).tsh γ x) ((G.extent b).rc γ x) n
      unfold tagWt
      by_cases h1 : x = e + 1
      · subst h1
        rw [if_pos ((hep' _).mpr rfl), ftot_zero (fun k => (hF b (e + 1) k (by omega)).1),
          ftot_zero (fun k => (hF b (e + 1) k (by omega)).2)]
        unfold tagWt at hnn; grind
      · rw [if_neg (fun h => h1 ((hep' x).mp h))]
        by_cases h2 : x ≤ e
        · rw [if_pos ⟨e + 1, by omega, (hep' _).mpr rfl⟩]
          by_cases h3 : x = e
          · subst h3; rw [if_pos ((hep x).mpr rfl)]; grind
          · rw [if_neg (fun h => h3 ((hep x).mp h)), if_pos ⟨e, by omega, (hep e).mpr rfl⟩]
            exact Rat.le_refl
        · rw [if_neg (fun ⟨x', h, h'⟩ => by have := (hep' x').mp h'; omega)]
          unfold tagWt at hnn; exact hnn)
    (fun b x x' k he hlt => hF b x' k (by have := (hep' x).mp he; omega))
    (fun b k hk => by
      rcases hk with hk | ⟨γ', x, ⟨he, hp⟩ | ⟨he, hp⟩⟩
      · exact .inl hk
      · by_cases hγ : γ' = γ
        · subst hγ
          have := (hep' x).mp he; subst this
          rw [(hF b (e + 1) k (by omega)).1] at hp; exact absurd hp Rat.lt_irrefl
        · have : G'.ep γ' x ↔ G.ep γ' x := by unfold Ghost.ep; rw [hl γ' hγ]
          exact .inr ⟨γ', x, .inl ⟨this.mp he, hp⟩⟩
      · by_cases hγ : γ' = γ
        · subst hγ
          refine .inr ⟨γ', x, .inr ⟨?_, hp⟩⟩
          rcases he with he | ⟨x', h1, h2⟩
          · have := (hep' x).mp he; subst this
            rw [(hF b (e + 1) k (by omega)).2] at hp; exact absurd hp Rat.lt_irrefl
          · have := (hep' x').mp h2
            by_cases h3 : x = e
            · exact .inl ((hep x).mpr h3)
            · exact .inr ⟨e, by omega, (hep e).mpr rfl⟩
        · have : ∀ x, G'.ep γ' x ↔ G.ep γ' x := fun x => by unfold Ghost.ep; rw [hl γ' hγ]
          refine .inr ⟨γ', x, .inr ⟨?_, hp⟩⟩
          rcases he with he | ⟨x', h1, h2⟩
          · exact .inl ((this x).mp he)
          · exact .inr ⟨x', h1, (this x').mp h2⟩)
  refine ⟨⟨FHeap.empty, Know.none, Ghost.at γ (GCell.auth1 (e + 1) GMap.empty)⟩, ⟨rfl, rfl, rfl⟩,
    h0.symm, k0.symm, by rw [g0]; funext b; simp [Ghost.at], ⟨hv', N + γ + 1, fun γ' hγ => ⟨?_, ?_⟩⟩,
    fun m hm => by rw [g0] at hm; exact ht' m hm⟩
  · rw [hl γ' (by omega)]; exact (hN γ' (by omega)).1
  · rw [hx]; exact (hN γ' (by omega)).2

end Upd

/-- **A token of the current epoch names a recorded grant.** -/
theorem gfrag_mem {γ e i : Nat} {M : GMap} {g : GRegion} {r : Res} {gF : Ghost}
    (h : (gauth γ e M ⋆ gfrag γ e i g) r) (hg : Ghost.Ok r.gh gF) : M i = some g := by
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
theorem mem {γ e i : Nat} {M : GMap} {g : GRegion} {R : FAssn}
    (ht : M i = some g → FTriple ((gauth γ e M ⋆ gfrag γ e i g) ⋆ R) c Q) :
    FTriple ((gauth γ e M ⋆ gfrag γ e i g) ⋆ R) c Q := by
  intro m r rF hh hp hs
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := id hp
  have hg := hh.ghost
  have : Ghost.Ok r₁.gh (r₂.gh.add rF.gh) := Ghost.Ok.assoc.mp hg.1
  exact ht (gfrag_mem h1 this) m _ rF hh hp hs

end FTriple

end Full
end Zig
