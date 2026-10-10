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
def Ghost.at (γ : Nat) (c : GCell) : Ghost := fun γ' => if γ' = γ then c else GCell.unit

theorem Ghost.at_add (γ : Nat) (c c' : GCell) : (Ghost.at γ c).add (Ghost.at γ c') = Ghost.at γ (c.add c') := by
  funext γ'; simp only [Ghost.add, Ghost.at]; split <;> simp

/-- **A local update** at one name: if every cell that `c` composes validly with also composes
validly with `c'`, replacing `c` by `c'` keeps every frame valid. -/
theorem Ghost.Ok.update {γ : Nat} {c c' : GCell} {g : Ghost}
    (h : ∀ d, (c.add d).Valid → (c'.add d).Valid) (hok : Ghost.Ok (Ghost.at γ c) g) :
    Ghost.Ok (Ghost.at γ c') g := by
  obtain ⟨hv, N, hN⟩ := hok
  refine ⟨fun γ' => ?_, N + γ + 1, fun γ' hγ => ?_⟩
  · have := hv γ'
    simp only [Ghost.add, Ghost.at] at this ⊢
    split at this
    · subst γ'; simp only [↓reduceIte]; exact h _ this
    · rename_i hne; simp only [hne, ↓reduceIte]; exact this
  · have hne : γ' ≠ γ := by omega
    have := hN γ' (by omega)
    simp only [Ghost.add, Ghost.at, hne, ↓reduceIte] at this ⊢
    exact this

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

/-- `P` can become `P'` by a ghost update: every resource of `P` is replaced, with the same bytes
and knowledge, by one of `P'` that composes with every ghost frame the old one composed with. -/
def Upd (P P' : FAssn) : Prop :=
  ∀ r, P r → ∀ g, Ghost.Ok r.gh g →
    ∃ r', P' r' ∧ r'.heap = r.heap ∧ r'.know = r.know ∧ Ghost.Ok r'.gh g

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

theorem of_imp (h : ∀ r, P r → P' r) : Upd P P' := fun r hp _ hg => ⟨r, h r hp, rfl, rfl, hg⟩

theorem trans (h₁ : Upd P P') (h₂ : Upd P' P'') : Upd P P'' := fun r hp g hg => by
  obtain ⟨r₁, h1, e1, k1, g1⟩ := h₁ r hp g hg
  obtain ⟨r₂, h2, e2, k2, g2⟩ := h₂ r₁ h1 g g1
  exact ⟨r₂, h2, e2.trans e1, k2.trans k1, g2⟩

/-- Updates frame. -/
theorem frame (h : Upd P P') : Upd (P ⋆ R) (P' ⋆ R) := by
  rintro _ ⟨r₁, r₂, hd, rfl, hp, hr⟩ g hg
  obtain ⟨r₁', hp', e, k, hg'⟩ := h r₁ hp (r₂.gh.add g) (Ghost.Ok.assoc.mp hg)
  refine ⟨⟨r₁'.heap ∪ r₂.heap, r₁'.know.union r₂.know, r₁'.gh.add r₂.gh⟩,
    ⟨r₁', r₂, by rw [e]; exact hd, rfl, hp', hr⟩, by simp [e], by simp [k],
    Ghost.Ok.assoc.mpr hg'⟩

theorem frameL (h : Upd P P') : Upd (R ⋆ P) (R ⋆ P') :=
  trans (of_imp fun _ h => sep_comm h) (trans (frame h) (of_imp fun _ h => sep_comm h))

/-- A local update of a ghost-only resource at one name. -/
theorem single {γ : Nat} {c c' : GCell} {P P' : FAssn}
    (hp : ∀ r, P r → r = ⟨FHeap.empty, Know.none, Ghost.at γ c⟩)
    (hp' : P' ⟨FHeap.empty, Know.none, Ghost.at γ c'⟩)
    (h : ∀ d, (c.add d).Valid → (c'.add d).Valid) : Upd P P' := fun r hr g hg => by
  have e := hp r hr
  subst e
  exact ⟨_, hp', rfl, rfl, Ghost.Ok.update h hg⟩

/-- **A new ledger** at a name no frame uses, with no grant. -/
theorem alloc : Upd emp (FAssn.ex fun γ => gauth γ 0 GMap.empty) := by
  rintro r ⟨h0, k0, g0⟩ g hg
  rw [g0] at hg
  obtain ⟨hv, N, hN⟩ := hg
  refine ⟨⟨FHeap.empty, Know.none, Ghost.at N (GCell.auth1 0 GMap.empty)⟩, ⟨N, rfl, rfl, rfl⟩,
    h0.symm, k0.symm, fun γ => ?_, N + 1, fun γ hγ => ?_⟩
  · have hv' := hv γ
    simp only [Ghost.unit_add] at hv'
    simp only [Ghost.add, Ghost.at]
    split
    · subst γ
      have := hN N (Nat.le_refl _)
      simp only [Ghost.unit_add] at this
      rw [this]
      exact GCell.valid_auth1_add.mpr ⟨fun _ => rfl, fun _ _ => ⟨by simp [GCell.unit],
        by simp [GCell.unit]⟩, fun _ _ _ _ => rfl⟩
    · simpa using hv'
  · have := hN γ (by omega)
    simp only [Ghost.unit_add] at this
    simp only [Ghost.add, Ghost.at, show γ ≠ N by omega, ↓reduceIte, this, GCell.add_unit]

/-- **Issue a grant** of the current epoch under an unused id `i`, naming region `g`. -/
theorem issue {γ e i : Nat} {M : GMap} (g : GRegion) (hi : M i = none) :
    Upd (gauth γ e M) (gauth γ e (M.set i (some g)) ⋆ gfrag γ e i g) :=
  single (c := GCell.auth1 e M) (fun r ⟨h, k, gh⟩ => by rw [res_eta r, h, k, gh])
    gauth_gfrag_intro fun d hv => by
      rw [GCell.add_assoc, GCell.valid_auth1_add]
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

/-- **Give back a grant** of the current epoch. -/
theorem retire {γ e i : Nat} {M : GMap} {g : GRegion} :
    Upd (gauth γ e M ⋆ gfrag γ e i g) (gauth γ e (M.set i none)) :=
  single (c := (GCell.auth1 e M).add (GCell.frag1 e i g)) (fun _ h => gauth_gfrag h)
    ⟨rfl, rfl, rfl⟩ fun d hv => by
      rw [GCell.add_assoc] at hv
      obtain ⟨h1, hM, h0, h2, h3⟩ := GCell.valid_pair hv
      refine GCell.valid_auth1_add.mpr ⟨h1, fun j g' => ⟨(h2 j g').1, fun hp => ?_⟩, h3⟩
      have hj := (h2 j g').2 hp
      by_cases hji : j = i
      · subst hji; rw [hM] at hj; cases hj; omega
      · rw [GMap.set_ne _ _ hji]; exact hj

/-- **Re-point a grant** of the current epoch at another region (a resize in place). -/
theorem reassign {γ e i : Nat} {M : GMap} {g : GRegion} (g' : GRegion) :
    Upd (gauth γ e M ⋆ gfrag γ e i g) (gauth γ e (M.set i (some g')) ⋆ gfrag γ e i g') := by
  have h := issue (γ := γ) (e := e) g' (GMap.set_same M i none)
  rw [GMap.set_set] at h
  exact trans retire h

/-- **The next epoch**, with no grant: every outstanding token becomes stale. -/
theorem bump {γ e : Nat} {M : GMap} : Upd (gauth γ e M) (gauth γ (e + 1) GMap.empty) :=
  single (c := GCell.auth1 e M) (fun r ⟨h, k, gh⟩ => by rw [res_eta r, h, k, gh])
    ⟨rfl, rfl, rfl⟩ fun d hv => by
      obtain ⟨h1, -, h3⟩ := GCell.valid_auth1_add.mp hv
      exact GCell.valid_auth1_add.mpr ⟨h1, fun i g => by simp [h3 (e + 1) i g (by omega)],
        fun e' i g he => h3 e' i g (by omega)⟩

end Upd

/-- **A token of the current epoch names a recorded grant.** -/
theorem gfrag_mem {γ e i : Nat} {M : GMap} {g : GRegion} {r : Res} {gF : Ghost}
    (h : (gauth γ e M ⋆ gfrag γ e i g) r) (hg : Ghost.Ok r.gh gF) : M i = some g := by
  rw [gauth_gfrag h] at hg
  have := hg.1 γ
  simp only [Ghost.add, Ghost.at, ↓reduceIte] at this
  rw [GCell.add_assoc] at this
  exact (GCell.valid_pair this).2.1

/-! ## Triple rules -/

namespace FTriple

variable {α : Type} {P P' : FAssn} {c : MemM α} {Q Q' : α → FAssn}

/-- A ghost update of the precondition. -/
theorem upd (hu : Upd P P') (ht : FTriple P' c Q) : FTriple P c Q := by
  intro m r rF hh hp hs
  obtain ⟨r', hp', e, k, hg⟩ := hu r hp rF.gh hh.ghost
  exact ht m r' rF ⟨by rw [e]; exact hh.disj, by rw [e]; exact hh.heap, by rw [k]; exact hh.know,
    hh.knowF, hg⟩ hp' hs

/-- A ghost update of the postcondition. -/
theorem upd_post (ht : FTriple P c Q) (hu : ∀ v, Upd (Q v) (Q' v)) : FTriple P c Q' := by
  intro m r rF hh hp hs
  have := ht m r rF hh hp hs
  split at this
  · trivial
  · exact this
  · obtain ⟨r', hh', hq, hs'⟩ := this
    obtain ⟨r'', hq', e, k, hg⟩ := hu _ r' hq rF.gh hh'.ghost
    exact ⟨r'', ⟨by rw [e]; exact hh'.disj, by rw [e]; exact hh'.heap, by rw [k]; exact hh'.know,
      hh'.knowF, hg⟩, hq', hs'⟩

/-- The fact `M i = some g` of a token of the current epoch, in a precondition. -/
theorem mem {γ e i : Nat} {M : GMap} {g : GRegion} {R : FAssn}
    (ht : M i = some g → FTriple ((gauth γ e M ⋆ gfrag γ e i g) ⋆ R) c Q) :
    FTriple ((gauth γ e M ⋆ gfrag γ e i g) ⋆ R) c Q := by
  intro m r rF hh hp hs
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := id hp
  have hg := hh.ghost
  have : Ghost.Ok r₁.gh (r₂.gh.add rF.gh) := Ghost.Ok.assoc.mp hg
  exact ht (gfrag_mem h1 this) m _ rF hh hp hs

end FTriple

end Full
end Zig
