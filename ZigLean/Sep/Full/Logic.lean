import ZigLean.Sep.Full.Triple
import ZigLean.Sep.Total

/-!
# Total full-state triples and the `FLogic` record (`docs/sep-full-state.md`, migration stage 1)

`FTotalTriple P c Q`: `FTriple P c Q`, and `c` returns from every memory that holds `P` with a
frame (`FReturns`). `FLogic` is `Logic` (`ZigLean/Sep/AllocSpec.lean`) over full-state
assertions: a Hoare logic over `MemM` with the structural rules, instantiated by `FTriple`
(`FLogic.partial`) and `FTotalTriple` (`FLogic.total`). Its `congr` quantifies over `Mem.FSeq`
memories.

`FTotalTriple.ofTotal` lifts a legacy `TotalTriple` of a `Tame` program, as `FTriple.ofTriple`
lifts a `Triple`.
-/

namespace Zig
namespace Full

open FAssn

variable {α β : Type} {P P' R : FAssn} {Q Q' : α → FAssn} {c c' : MemM α}

/-- `m` holds `r₁ ⋆ r₂` with frame `rF` iff it holds `r₁` with frame `r₂ ⋆ rF`. -/
theorem Holds.split {m : Mem} {r₁ r₂ rF : Res} (hd : FHeap.Disjoint r₁.heap r₂.heap)
    (hh : Holds m ⟨r₁.heap ∪ r₂.heap, r₁.know.union r₂.know, r₁.gh.add r₂.gh⟩ rF) :
    Holds m r₁ ⟨r₂.heap ∪ rF.heap, r₂.know.union rF.know, r₂.gh.add rF.gh⟩ := by
  obtain ⟨hdisj, hheap, hk, hkF, hg⟩ := hh
  obtain ⟨h1F, -⟩ := FHeap.disjoint_union_left.mp hdisj
  have h2F := (FHeap.disjoint_union_left.mp hdisj).2
  exact ⟨FHeap.disjoint_union_right.mpr ⟨hd, h1F⟩, by rw [← FHeap.union_assoc]; exact hheap,
    hk.left, hk.right.union hkF, GOk.assoc.mp hg⟩

/-- `c` returns from every memory that holds `P` with some frame. -/
def FReturns (P : FAssn) (c : MemM α) : Prop :=
  ∀ m r rF, Holds m r rF → P r → m.FSeq → ∃ v m', c.run m = pure (v, m')

/-- Total correctness without a panic, over full-state resources. -/
def FTotalTriple (P : FAssn) (c : MemM α) (Q : α → FAssn) : Prop :=
  FTriple P c Q ∧ FReturns P c

namespace FTotalTriple

theorem toPartial (ht : FTotalTriple P c Q) : FTriple P c Q := ht.1

theorem conseq (ht : FTotalTriple P c Q) (hp : ∀ r, P' r → P r) (hq : ∀ v r, Q v r → Q' v r) :
    FTotalTriple P' c Q' :=
  ⟨ht.1.conseq hp hq, fun m r rF hh hp' hs => ht.2 m r rF hh (hp _ hp') hs⟩

theorem pre (ht : FTotalTriple P c Q) (hp : ∀ r, P' r → P r) : FTotalTriple P' c Q :=
  ht.conseq hp fun _ _ h => h

theorem post (ht : FTotalTriple P c Q) (hq : ∀ v r, Q v r → Q' v r) : FTotalTriple P c Q' :=
  ht.conseq (fun _ h => h) hq

theorem frame (ht : FTotalTriple P c Q) : FTotalTriple (P ⋆ R) c (fun v => Q v ⋆ R) := by
  refine ⟨ht.1.frame, fun m r rF hh hpr hs => ?_⟩
  obtain ⟨rP, rR, hd, rfl, hp, -⟩ := hpr
  exact ht.2 m rP _ (Holds.split hd hh) hp hs

theorem ret (v : α) : FTotalTriple (Q v) (pure v : MemM α) Q :=
  ⟨FTriple.ret v, fun m _ _ _ _ _ => ⟨v, m, rfl⟩⟩

theorem bind {S : β → FAssn} {f : α → MemM β} (hc : FTotalTriple P c Q)
    (hf : ∀ v, FTotalTriple (Q v) (f v) S) : FTotalTriple P (c >>= f) S := by
  refine ⟨hc.1.bind fun v => (hf v).1, fun m r rF hh hp hs => ?_⟩
  obtain ⟨v, m', hr⟩ := hc.2 m r rF hh hp hs
  have h1 := hc.1 m r rF hh hp hs
  rw [hr] at h1
  obtain ⟨r', hh', hq, hs'⟩ := h1
  obtain ⟨w, m'', hr'⟩ := (hf v).2 m' r' rF hh' hq hs'
  refine ⟨w, m'', ?_⟩
  simp only [StateT.run_bind] at hr ⊢
  rw [hr]
  exact hr'

theorem ex {γ : Type} {P : γ → FAssn} (h : ∀ x, FTotalTriple (P x) c Q) :
    FTotalTriple (FAssn.ex P) c Q :=
  ⟨FTriple.ex fun x => (h x).1, fun m r rF hh ⟨x, hp⟩ hs => (h x).2 m r rF hh hp hs⟩

theorem lift {φ : Prop} (h : φ → FTotalTriple P c Q) : FTotalTriple (⟪φ⟫ ⋆ P) c Q := by
  refine ⟨FTriple.lift fun hφ => (h hφ).1, fun m r rF hh hp hs => ?_⟩
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact (h hφ).2 m r rF hh hp hs

end FTotalTriple

theorem FTriple.congr (he : ∀ m, m.FSeq → c'.run m = c.run m) (ht : FTriple P c Q) :
    FTriple P c' Q := by
  intro m r rF hh hp hs
  rw [he m hs]; exact ht m r rF hh hp hs

theorem FTotalTriple.congr (he : ∀ m, m.FSeq → c'.run m = c.run m) (ht : FTotalTriple P c Q) :
    FTotalTriple P c' Q :=
  ⟨ht.1.congr he, fun m r rF hh hp hs => by rw [he m hs]; exact ht.2 m r rF hh hp hs⟩

/-- **Lifting a total triple** (`FTriple.ofTriple`; it returns because the legacy triple returns
from the memory's actual cells). -/
theorem FTotalTriple.ofTotal {P : Assn} {Q : α → Assn} {E : BlockId → Option (Nat × BlockKind)}
    {B : BlockId → Prop} (ht : TotalTriple P c Q) (hc : Tame c)
    (hB : ∀ h, P h → ∀ l c, h l = some c → B l.1)
    (hpin : ∀ h, P h → ∀ l c S K, h l = some c → E l.1 = some (S, K) → c.size = S ∧ c.kind = K)
    (hsf : SizeFree E P) (hk : (∀ b, B b → (E b).isSome) ∨ Keeps (fun b => (E b).isSome) c) :
    FTotalTriple (upE P E) c (fun v => upPost (Q v) B E) := by
  refine ⟨FTriple.ofTriple ht.toPartial hc hB hpin hsf hk, fun m r rF hh hp hs => ?_⟩
  obtain ⟨v, m', -, hr, -⟩ := ht m _ _ (FHeap.erase_disjoint (FHeap.fix_disjoint hh.disj))
    (hh.fix.heap_exact hh.fix_exact hh.fix_exactF) (upE_fix hsf hpin hh hp) hs.1
  exact ⟨v, m', hr⟩

/-- `FTotalTriple.ofTotal` for a size-free precondition and a program that keeps every block. -/
theorem FTotalTriple.ofTotal_up {P : Assn} {Q : α → Assn} (ht : TotalTriple P c Q) (hc : Tame c)
    (hsf : SizeFree (fun _ => none) P) (hk : Keeps (fun _ => False) c) :
    FTotalTriple (up P) c (fun v => up (Q v)) :=
  ⟨FTriple.ofTriple_up ht.toPartial hc hsf hk, fun m r rF hh hp hs =>
    (FTotalTriple.ofTotal (E := fun _ => none) (B := fun _ => True) ht hc (fun _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ _ h => by cases h) hsf (.inr (fun m v m' h b blk _ => hk m v m' h b blk id))).2
      m r rF hh (upE_none.mpr hp) hs⟩

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

variable {P P' P'' : FAssn}

theorem of_imp (h : ∀ r, P r → P' r) : EUpd P P' := fun _ r _ hh hp _ => ⟨r, hh, h r hp⟩

theorem trans (h₁ : EUpd P P') (h₂ : EUpd P' P'') : EUpd P P'' := fun m r rF hh hp hs => by
  obtain ⟨r₁, hh₁, hp₁⟩ := h₁ m r rF hh hp hs
  exact h₂ m r₁ rF hh₁ hp₁ hs

/-- A lifted post with its extents forgotten. -/
theorem upPost_up {Q : Assn} {B : BlockId → Prop} {E : BlockId → Option (Nat × BlockKind)} :
    EUpd (upPost Q B E) (up Q) := fun m r rF hh h hs => by
  obtain ⟨E', ⟨hq, hk, hg⟩, -⟩ := h
  refine ⟨⟨r.heap, Know.none, Ghost.unit⟩, ⟨hh.disj, hh.heap, Know.sub_none _, hh.knowF,
    GOk.mono (b := Ghost.exts E') ?_ fun _ _ => rfl⟩, hq, rfl, rfl⟩
  rw [Ghost.unit_add, ← hg]; exact hh.ghost

end EUpd

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

/-! ## The logic record -/

/-- `Logic` (`ZigLean/Sep/AllocSpec.lean`) over full-state assertions. A total triple is a triple
of every such logic (`ofTotal`), and a triple of any of them is a partial one (`toPartial`). -/
structure FLogic where
  T : {α : Type} → FAssn → MemM α → (α → FAssn) → Prop
  ofTotal : ∀ {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}, FTotalTriple P c Q → T P c Q
  toPartial : ∀ {α : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn}, T P c Q → FTriple P c Q
  conseq : ∀ {α : Type} {P P' : FAssn} {c : MemM α} {Q Q' : α → FAssn}, T P c Q →
    (∀ r, P' r → P r) → (∀ v r, Q v r → Q' v r) → T P' c Q'
  frame : ∀ {α : Type} {P R : FAssn} {c : MemM α} {Q : α → FAssn}, T P c Q →
    T (P ⋆ R) c (fun v => Q v ⋆ R)
  bind : ∀ {α β : Type} {P : FAssn} {c : MemM α} {Q : α → FAssn} {R : β → FAssn}
    {f : α → MemM β}, T P c Q → (∀ v, T (Q v) (f v) R) → T P (c >>= f) R
  ex : ∀ {α γ : Type} {P : γ → FAssn} {c : MemM α} {Q : α → FAssn}, (∀ x, T (P x) c Q) →
    T (FAssn.ex P) c Q
  lift : ∀ {α : Type} {φ : Prop} {P : FAssn} {c : MemM α} {Q : α → FAssn}, (φ → T P c Q) →
    T (⟪φ⟫ ⋆ P) c Q
  /-- Two programs with the same runs from every full-state sequential memory. -/
  congr : ∀ {α : Type} {P : FAssn} {c c' : MemM α} {Q : α → FAssn},
    (∀ m, m.FSeq → c'.run m = c.run m) → T P c Q → T P c' Q
  /-- An update of the postcondition in the final memory (`EUpd`: it may change extent claims). -/
  eupdPost : ∀ {α : Type} {P : FAssn} {c : MemM α} {Q Q' : α → FAssn}, T P c Q →
    (∀ v, EUpd (Q v) (Q' v)) → T P c Q'

/-- Partial correctness: `FTriple`. -/
def FLogic.partial : FLogic where
  T := FTriple
  ofTotal := FTotalTriple.toPartial
  toPartial := id
  conseq := FTriple.conseq
  frame := FTriple.frame
  bind := FTriple.bind
  ex := FTriple.ex
  lift := FTriple.lift
  congr := FTriple.congr
  eupdPost := FTriple.eupd_post

/-- Total correctness: `FTotalTriple`. -/
def FLogic.total : FLogic where
  T := FTotalTriple
  ofTotal := id
  toPartial := FTotalTriple.toPartial
  conseq := FTotalTriple.conseq
  frame := FTotalTriple.frame
  bind := FTotalTriple.bind
  ex := FTotalTriple.ex
  lift := FTotalTriple.lift
  congr := FTotalTriple.congr
  eupdPost := FTotalTriple.eupd_post

namespace FLogic

variable (L : FLogic)

theorem ret (v : α) : L.T (Q v) (pure v : MemM α) Q := L.ofTotal (FTotalTriple.ret v)

theorem ret' (v : α) (hq : ∀ r, P r → Q v r) : L.T P (pure v : MemM α) Q :=
  L.conseq (L.ret v) hq (fun _ _ h => h)

theorem pre (ht : L.T P c Q) (hp : ∀ r, P' r → P r) : L.T P' c Q :=
  L.conseq ht hp (fun _ _ h => h)

theorem post (ht : L.T P c Q) (hq : ∀ v r, Q v r → Q' v r) : L.T P c Q' :=
  L.conseq ht (fun _ h => h) hq

theorem frameL (ht : L.T P c Q) : L.T (R ⋆ P) c (fun v => R ⋆ Q v) :=
  L.conseq (L.frame (R := R) ht) (fun _ h => sep_comm h) (fun _ _ h => sep_comm h)

end FLogic

end Full
end Zig
