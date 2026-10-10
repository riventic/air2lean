import ZigLean.Sep.Full.Triple

/-!
# Ghost epoch ledgers (`docs/sep-full-state.md` §Ghost state)

A ghost name `γ` holds a ledger: an authority `gauth γ e n` (the current epoch `e`, `n` tokens
outstanding in it) and tokens `gfrag γ e`. Ghost state lives only in resources (`Res.gh`); no
primitive reads or changes it, and `Holds` requires the ghost states of a resource and its frame
to compose (`Ghost.Ok`). It changes only by **frame-preserving updates** (`Upd`), applied to a
triple's pre- or postcondition (`FTriple.upd`, `FTriple.upd_post`):

* `Upd.alloc`: a new ledger `gauth γ 0 0` at a name no frame uses;
* `Upd.issue`: a new token of the current epoch;
* `Upd.retire`: a token of the current epoch given back;
* `Upd.bump`: the next epoch, every outstanding token stale (revocation without collection);
* `Upd.count`: a token of the current epoch shows that `n ≥ 1`.

A stale token stays valid but is useless: an invariant indexed by the epoch (`own e`) needs the
authority of its epoch, which is exclusive.
-/

namespace Zig
namespace Full

open FAssn

/-! ## Ledger cells -/

namespace GCell

/-- The authority `●(e, n)`. -/
def auth1 (e n : Nat) : GCell := ⟨fun x => if x = (e, n) then 1 else 0, fun _ => 0⟩

/-- `k` tokens `◯e`. -/
def frag1 (e k : Nat) : GCell := ⟨fun _ => 0, fun e' => if e' = e then k else 0⟩

theorem valid_auth1_add {e n : Nat} {d : GCell} :
    ((auth1 e n).add d).Valid ↔ (∀ x, d.auth x = 0) ∧ d.frag e ≤ n ∧ ∀ e', e < e' → d.frag e' = 0 := by
  constructor
  · rintro (h | ⟨e', n', h1, h2, h3, h4⟩)
    · have := h (e, n); simp [add, auth1] at this
    · by_cases hx : (e', n') = (e, n)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
        refine ⟨fun x => ?_, by simpa [add, auth1] using h3, fun e'' he => by
          simpa [add, auth1] using h4 e'' he⟩
        by_cases hx' : x = (e', n')
        · subst hx'; simp [add, auth1] at h1; omega
        · have := h2 x hx'; simp [add, auth1, hx'] at this; omega
      · have := h2 (e, n) (Ne.symm hx); simp [add, auth1] at this
  · rintro ⟨h1, h2, h3⟩
    refine .inr ⟨e, n, by simp [add, auth1, h1], fun x hx => by simp [add, auth1, hx, h1],
      by simpa [add, auth1] using h2, fun e' he => by simpa [add, auth1] using h3 e' he⟩

theorem frag1_add_frag (e k : Nat) (d : GCell) :
    (frag1 e k).add d = ⟨d.auth, fun e' => (if e' = e then k else 0) + d.frag e'⟩ := by
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

/-! ## Assertions -/

/-- The authority of ledger `γ`: epoch `e`, `n` tokens outstanding. Owns no bytes, no knowledge. -/
def gauth (γ e n : Nat) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.at γ (GCell.auth1 e n)

/-- A token of ledger `γ`, epoch `e`. -/
def gfrag (γ e : Nat) : FAssn := fun r =>
  r.heap = FHeap.empty ∧ r.know = Know.none ∧ r.gh = Ghost.at γ (GCell.frag1 e 1)

/-- A ghost-only assertion owns no bytes. -/
theorem gauth_heap {γ e n : Nat} {r : Res} (h : gauth γ e n r) : r.heap = FHeap.empty := h.1

theorem gfrag_heap {γ e : Nat} {r : Res} (h : gfrag γ e r) : r.heap = FHeap.empty := h.1

/-- The resource of `gauth γ e n ⋆ gfrag γ e`. -/
theorem gauth_gfrag {γ e n : Nat} {r : Res} (h : (gauth γ e n ⋆ gfrag γ e) r) :
    r = ⟨FHeap.empty, Know.none, Ghost.at γ ((GCell.auth1 e n).add (GCell.frag1 e 1))⟩ := by
  obtain ⟨r₁, r₂, -, rfl, ⟨h1, k1, g1⟩, ⟨h2, k2, g2⟩⟩ := h
  rw [h1, h2, k1, k2, g1, g2, FHeap.union_empty, Know.union_none, Ghost.at_add]

theorem gauth_gfrag_intro {γ e n : Nat} :
    (gauth γ e n ⋆ gfrag γ e) ⟨FHeap.empty, Know.none, Ghost.at γ ((GCell.auth1 e n).add (GCell.frag1 e 1))⟩ :=
  ⟨⟨FHeap.empty, Know.none, Ghost.at γ (GCell.auth1 e n)⟩,
    ⟨FHeap.empty, Know.none, Ghost.at γ (GCell.frag1 e 1)⟩, FHeap.disjoint_empty _,
    by rw [FHeap.union_empty, Know.union_none, Ghost.at_add], ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/-! ## Frame-preserving updates -/

/-- `P` can become `P'` by a ghost update: every resource of `P` is replaced, with the same bytes
and knowledge, by one of `P'` that composes with every ghost frame the old one composed with. -/
def Upd (P P' : FAssn) : Prop :=
  ∀ r, P r → ∀ g, Ghost.Ok r.gh g →
    ∃ r', P' r' ∧ r'.heap = r.heap ∧ r'.know = r.know ∧ Ghost.Ok r'.gh g

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

/-- **A new ledger** at a name no frame uses. -/
theorem alloc : Upd emp (FAssn.ex fun γ => gauth γ 0 0) := by
  rintro r ⟨h0, k0, g0⟩ g hg
  rw [g0] at hg
  obtain ⟨hv, N, hN⟩ := hg
  refine ⟨⟨FHeap.empty, Know.none, Ghost.at N (GCell.auth1 0 0)⟩, ⟨N, rfl, rfl, rfl⟩, h0.symm,
    k0.symm, fun γ => ?_, N + 1, fun γ hγ => ?_⟩
  · have hv' := hv γ
    simp only [Ghost.unit_add] at hv'
    simp only [Ghost.add, Ghost.at]
    split
    · subst γ
      have := hN N (Nat.le_refl _)
      simp only [Ghost.unit_add] at this
      rw [this]
      exact GCell.valid_auth1_add.mpr ⟨fun _ => rfl, Nat.le_refl _, fun _ _ => rfl⟩
    · simpa using hv'
  · have := hN γ (by omega)
    simp only [Ghost.unit_add] at this
    simp only [Ghost.add, Ghost.at, show γ ≠ N by omega, ↓reduceIte, this, GCell.add_unit]

/-- **Issue a token** of the current epoch. -/
theorem issue {γ e n : Nat} : Upd (gauth γ e n) (gauth γ e (n + 1) ⋆ gfrag γ e) :=
  single (c := GCell.auth1 e n) (fun r ⟨h, k, g⟩ => by rw [res_eta r, h, k, g])
    gauth_gfrag_intro fun d hv => by
      rw [GCell.add_assoc, GCell.valid_auth1_add, GCell.frag1_add_frag]
      obtain ⟨h1, h2, h3⟩ := GCell.valid_auth1_add.mp hv
      refine ⟨h1, by simp; omega, fun e' he => by simp [Nat.ne_of_gt he, h3 e' he]⟩

/-- **Give back a token** of the current epoch. -/
theorem retire {γ e n : Nat} : Upd (gauth γ e n ⋆ gfrag γ e) (gauth γ e (n - 1)) :=
  single (c := (GCell.auth1 e n).add (GCell.frag1 e 1)) (fun _ h => gauth_gfrag h)
    ⟨rfl, rfl, rfl⟩ fun d hv => by
      rw [GCell.add_assoc, GCell.valid_auth1_add, GCell.frag1_add_frag] at hv
      obtain ⟨h1, h2, h3⟩ := hv
      refine GCell.valid_auth1_add.mpr ⟨h1, by simp at h2; omega, fun e' he => ?_⟩
      have := h3 e' he; simp [Nat.ne_of_gt he] at this; exact this

/-- **The next epoch**: every outstanding token becomes stale. -/
theorem bump {γ e n : Nat} : Upd (gauth γ e n) (gauth γ (e + 1) 0) :=
  single (c := GCell.auth1 e n) (fun r ⟨h, k, g⟩ => by rw [res_eta r, h, k, g])
    ⟨rfl, rfl, rfl⟩ fun d hv => by
      obtain ⟨h1, -, h3⟩ := GCell.valid_auth1_add.mp hv
      exact GCell.valid_auth1_add.mpr ⟨h1, by simp [h3 (e + 1) (by omega)],
        fun e' he => h3 e' (by omega)⟩

end Upd

/-- **A token of the current epoch shows that one is outstanding.** -/
theorem gfrag_count {γ e n : Nat} {r : Res} {g : Ghost} (h : (gauth γ e n ⋆ gfrag γ e) r)
    (hg : Ghost.Ok r.gh g) : 1 ≤ n := by
  rw [gauth_gfrag h] at hg
  have := hg.1 γ
  simp only [Ghost.add, Ghost.at, ↓reduceIte] at this
  rw [GCell.add_assoc, GCell.valid_auth1_add, GCell.frag1_add_frag] at this
  have := this.2.1
  simp at this; omega

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

/-- The count fact `1 ≤ n` of a token of the current epoch, in a precondition. -/
theorem count {γ e n : Nat} {R : FAssn} (ht : 1 ≤ n → FTriple ((gauth γ e n ⋆ gfrag γ e) ⋆ R) c Q) :
    FTriple ((gauth γ e n ⋆ gfrag γ e) ⋆ R) c Q := by
  intro m r rF hh hp hs
  obtain ⟨r₁, r₂, hd, rfl, h1, h2⟩ := id hp
  have hg := hh.ghost
  have : Ghost.Ok r₁.gh (r₂.gh.add rF.gh) := Ghost.Ok.assoc.mp hg
  exact ht (gfrag_count h1 this) m _ rF hh hp hs

end FTriple

end Full
end Zig
