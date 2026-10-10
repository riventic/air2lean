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
  exact ⟨FHeap.disjoint_union_right.mpr ⟨hd, h1F⟩, by rw [hheap]; exact FHeap.union_assoc ..,
    hk.left, hk.right.union hkF, Ghost.Ok.assoc.mp hg⟩

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

/-- **Lifting a total triple** of a program that keeps the atomic layout and the block addresses
(`FTriple.ofTriple`, and it returns because the legacy triple returns from the erased heaps). -/
theorem FTotalTriple.ofTotal {P : Assn} {Q : α → Assn} (ht : TotalTriple P c Q) (hc : Tame c) :
    FTotalTriple (up P) c (fun v => up (Q v)) := by
  refine ⟨FTriple.ofTriple ht.toPartial hc, fun m r rF hh hp hs => ?_⟩
  have hm : m.heap = r.heap.erase ∪ rF.heap.erase := by
    rw [← fheap_erase, hh.heap, FHeap.erase_union]
  obtain ⟨v, m', -, hr, -⟩ := ht m _ _ (FHeap.erase_disjoint hh.disj) hm hp.1 hs.1
  exact ⟨v, m', hr⟩

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
