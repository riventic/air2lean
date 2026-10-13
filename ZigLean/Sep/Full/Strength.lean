import ZigLean.Sep.Full.Init

/-!
# Strength of the full-state logic against the legacy one (`docs/proof-framework.md`, Plan A decision D1a)

A theorem migrated from the legacy logic (`Triple`, `TotalTriple`) to the full-state logic
(`FTriple`, `FTotalTriple`) must not be weaker. `FTriple.toTriple_on` and
`FTotalTriple.toTotal_on` give the legacy statement back from the full one, on every `Mem.FSeq`
memory (`Mem.FSeq` holds of the start memory, `Mem.init_fseq`, and every rule keeps it):

    FTriple (up P) c (fun v => up (Q v))  ⟹  `Triple P c Q`'s statement on every FSeq memory
    FTotalTriple (up P) c (fun v => up (Q v))  ⟹  `TotalTriple P c Q`'s statement on every FSeq memory

when each `Q v` is size-free (`SizeFree`: it does not read the size labels of its cells, which a
full-state postcondition cannot pin without the block's extent; `region`, `pts` and every
assertion of the form `∃ A S K, bytesAt …` are). The frame is kept exactly, size labels included:
the proof gives the frame the full extents (`bext`) of its blocks, so the program cannot resize
them, as in the legacy logic.

The strength harness (`tests/roadmap/one-logic/Strength.lean`) applies these to every migrated
theorem and checks the result against the legacy statement before the legacy one is deleted.
This module is a bridge: it is deleted with the legacy logic.
-/

namespace Zig
namespace Full

open FAssn Assn

variable {α : Type}

/-- A legacy heap as a full heap, each byte with its tag in the layout `sh`. -/
def FHeap.ofHeap (sh : List Shape) (h : Heap) : FHeap := fun l =>
  (h l).map fun c => ⟨c, tagOf sh l.1 l.2⟩

@[simp] theorem FHeap.ofHeap_erase (sh : List Shape) (h : Heap) : (FHeap.ofHeap sh h).erase = h := by
  funext l; simp only [FHeap.erase, FHeap.ofHeap, Option.map_map]; cases h l <;> rfl

theorem FHeap.ofHeap_disjoint {sh : List Shape} {h₁ h₂ : Heap} (hd : Heap.Disjoint h₁ h₂) :
    FHeap.Disjoint (FHeap.ofHeap sh h₁) (FHeap.ofHeap sh h₂) := fun l => by
  rcases hd l with e | e <;> simp [FHeap.ofHeap, e]

theorem FHeap.ofHeap_union (sh : List Shape) (h₁ h₂ : Heap) :
    FHeap.ofHeap sh (h₁ ∪ h₂) = FHeap.ofHeap sh h₁ ∪ FHeap.ofHeap sh h₂ := by
  funext l; simp only [FHeap.ofHeap, FHeap.union_apply, Heap.union_apply]; cases h₁ l <;> rfl

open Classical in
/-- The full extents of the blocks that `h` has a byte of, read from `m`. -/
noncomputable def heapExts (m : Mem) (h : Heap) : BlockId → Option (Nat × BlockKind) := fun b =>
  if ∃ x, h (b, x) ≠ none then (m.blocks[b]?).map fun blk => (blk.bytes.size, blk.kind) else none

/-- A byte of the second part of `m`'s live bytes is a live byte of `m`. -/
theorem heap_of_right {m : Mem} {hP h : Heap} (hd : Heap.Disjoint hP h) (hm : m.heap = hP ∪ h)
    {l : Loc} {c : Cell} (hc : h l = some c) : m.heap l = some c := by
  rw [hm, Heap.union_apply, hc]
  rcases hd l with e | e
  · simp [e]
  · simp [hc] at e

/-- The extents of a part of `m`'s live bytes are true in `m`. -/
theorem heapExts_true {m : Mem} {h hP : Heap} (hd : Heap.Disjoint hP h) (hm : m.heap = hP ∪ h) :
    ExtTrue m (Ghost.exts (heapExts m h)) := by
  refine exts_true fun b S K hE => ?_
  unfold heapExts at hE
  split at hE
  · rename_i hx
    obtain ⟨x, hx'⟩ := hx
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hx'
    have hmc := heap_of_right hd hm hc
    obtain ⟨blk, hb, hlo⟩ := Mem.heap_some_lo hmc
    obtain ⟨blk', hb', hl, hs, -⟩ := Mem.heap_some hmc
    rw [hb] at hb'; cases hb'
    simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hE
    obtain ⟨rfl, rfl⟩ := hE
    exact ⟨blk, hb, hl, rfl, rfl, by omega⟩
  · cases hE

/-- A `Mem.FSeq` memory split into `hP` and `hF` holds `hP` with the frame `hF` and the full
extents of `hF`'s blocks. -/
theorem holds_ofHeap {m : Mem} {hP hF : Heap} (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF) :
    Holds m ⟨FHeap.ofHeap (shapes m) hP, Know.none, Ghost.unit⟩
      ⟨FHeap.ofHeap (shapes m) hF, Know.none, Ghost.exts (heapExts m hF)⟩ := by
  have hok := exts_ok (heapExts m hF)
  refine ⟨FHeap.ofHeap_disjoint hd, ?_, fun _ h => h.elim, fun _ h => h.elim, ?_, ?_, ?_⟩
  · have : FHeap.ofHeap (shapes m) hP ∪ FHeap.ofHeap (shapes m) hF = m.fheap := by
      rw [← FHeap.ofHeap_union, ← hm]; rfl
    show FMatch m (_ ∪ _); rw [this]; exact FMatch.fheap m
  · show Ghost.Ok _ _; rw [Ghost.Ok, Ghost.add_comm]; exact hok
  · show ExtTrue m (Ghost.unit.add _); rw [Ghost.unit_add]; exact heapExts_true hd hm
  · show ClFresh m (Ghost.unit.add _); rw [Ghost.unit_add]; exact fun _ _ _ => rfl

/-- The frame `hF` with its full extents comes back exactly, size labels included. -/
theorem frame_back {m m' : Mem} {hP hF : Heap} (hd : Heap.Disjoint hP hF) (hm : m.heap = hP ∪ hF)
    {r' : Res}
    (hh : Holds m' r' ⟨FHeap.ofHeap (shapes m) hF, Know.none, Ghost.exts (heapExts m hF)⟩) :
    (Res.fix m' ⟨FHeap.ofHeap (shapes m) hF, Know.none, Ghost.exts (heapExts m hF)⟩).heap.erase = hF := by
  funext l
  obtain ⟨b, x⟩ := l
  cases hc : hF (b, x) with
  | none => simp [FHeap.erase, Res.fix, FHeap.fix, FHeap.ofHeap, hc]
  | some c =>
    obtain ⟨blk, hb, -, _, hce⟩ := Mem.heap_some (heap_of_right hd hm hc)
    have hE : heapExts m hF b = some (blk.bytes.size, blk.kind) := by
      have hx : ∃ x, hF (b, x) ≠ none := ⟨x, by rw [hc]; exact Option.some_ne_none _⟩
      simp only [heapExts, ite_eq_left hx, hb, Option.map_some]
    have ht : ExtTrue m' (Ghost.exts (heapExts m hF)) := by
      have := hh.ghost.2.1; rw [Ghost.add_comm] at this; exact ExtTrue.of_add this
    have hauth : 0 < ((Ghost.exts (heapExts m hF)).extent b).auth (blk.bytes.size, blk.kind) := by
      simp [Ghost.exts, hE, ECell.auth1]
    obtain ⟨blk', hb', -, hs, hk, -⟩ := (ht b).1 _ _ hauth
    simp [FHeap.erase, Res.fix, FHeap.fix, FHeap.ofHeap, hc, hb', hs, hk, hce]

/-! ## Size-free postconditions -/

theorem SizeFree.emp {E : BlockId → Option (Nat × BlockKind)} : SizeFree E Assn.emp := by
  intro h h' hp hn _ _
  funext l; have := hn l; rw [show h l = none by rw [hp]; rfl] at this
  cases e : h' l <;> simp_all [Heap.empty]

theorem SizeFree.lift {E : BlockId → Option (Nat × BlockKind)} {φ : Prop} :
    SizeFree E (⌜φ⌝ : Assn) := fun h h' hp hn hpin hsz =>
  ⟨hp.1, SizeFree.emp h h' hp.2 hn hpin hsz⟩

theorem SizeFree.ex {E : BlockId → Option (Nat × BlockKind)} {γ : Type} {P : γ → Assn}
    (h : ∀ x, SizeFree E (P x)) : SizeFree E (Assn.ex P) := fun h₀ h' ⟨x, hp⟩ hn hpin hsz =>
  ⟨x, h x h₀ h' hp hn hpin hsz⟩

/-- Size-free assertions are closed under `∗`: split the other heap along the first one's split. -/
theorem SizeFree.sep {E : BlockId → Option (Nat × BlockKind)} {P Q : Assn} (hP : SizeFree E P)
    (hQ : SizeFree E Q) : SizeFree E (P ∗ Q) := by
  rintro h h' ⟨h₁, h₂, hd, rfl, hp, hq⟩ hn hpin hsz
  have hn' := hn
  let k₁ : Heap := fun l => if h₁ l = none then none else h' l
  let k₂ : Heap := fun l => if h₁ l = none then h' l else none
  have hsplit : ∀ l, h₁ l ≠ none → h₂ l = none := fun l hl => (hd l).resolve_left hl
  refine ⟨k₁, k₂, fun l => ?_, ?_, hP h₁ k₁ hp (fun l => ?_) (fun l c hc hE => ?_)
    (fun l l' c c' e e' hb => ?_), hQ h₂ k₂ hq (fun l => ?_) (fun l c hc hE => ?_)
    (fun l l' c c' e e' hb => ?_)⟩
  · by_cases e : h₁ l = none <;> simp [k₁, k₂, e]
  · funext l; by_cases e : h₁ l = none <;> simp [k₁, k₂, e, Heap.union_apply]
  · have := hn l; simp only [Heap.union_apply] at this
    by_cases e : h₁ l = none
    · simp [k₁, e]
    · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp e
      rw [show k₁ l = h' l from ite_eq_right e, ← this, hc]; rfl
  · have := hpin l c (by simp [Heap.union_apply, hc]) hE
    simp [k₁, hc, this]
  · simp only [k₁] at e e'; split at e <;> split at e' <;> first | cases e | cases e' | exact hsz l l' c c' e e' hb
  · have := hn l; simp only [Heap.union_apply] at this
    by_cases e : h₁ l = none
    · rw [show k₂ l = h' l from ite_eq_left e, ← this, e]; rfl
    · simp [k₂, e, hsplit l e]
  · have h1n : h₁ l = none := (hd l).resolve_right (by simp [hc])
    have := hpin l c (by simp [Heap.union_apply, h1n, hc]) hE
    simp [k₂, h1n, this]
  · simp only [k₂] at e e'; split at e <;> split at e' <;> first | cases e | cases e' | exact hsz l l' c c' e e' hb

/-- **Strength (D1a)**: a full-state triple over legacy assertions gives the legacy triple on
every `Mem.FSeq` memory, for a size-free postcondition. -/
theorem FTriple.toTriple_on {c : MemM α} {P : Assn} {Q : α → Assn}
    (ht : FTriple (up P) c (fun v => up (Q v))) (hQ : ∀ v, SizeFree (fun _ => none) (Q v)) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.Seq → m.FSeq →
      match (c.run m).run with
      | none => True
      | some (.error e) => e = .stackOverflow
      | some (.ok (v, m')) =>
        ∃ hQ, Heap.Disjoint hQ hF ∧ m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Seq := by
  intro m hP hF hd hm hp _ hs
  have hh := holds_ofHeap hd hm
  have := ht m _ _ hh ⟨by simpa using hp, rfl, rfl⟩ hs
  revert this
  cases (c.run m).run with
  | none => intro; trivial
  | some x =>
    cases x with
    | error e => intro h; exact h
    | ok x =>
      obtain ⟨v, m'⟩ := x
      rintro ⟨r', hh', hq, hs'⟩
      have hF' := frame_back hd hm hh'
      refine ⟨(r'.fix m').heap.erase, ?_, ?_, ?_, hs'.1⟩
      · rw [← hF']; exact FHeap.erase_disjoint (FHeap.fix_disjoint hh'.disj)
      · rw [← hF']; exact hh'.fix.heap_exact hh'.fix_exact hh'.fix_exactF
      · exact upE_fix (hQ v) (fun _ _ _ _ _ _ _ h => by cases h) hh' (upE_none.mpr hq)

/-- **Strength (D1a), total form**: a total full-state triple over legacy assertions gives the
legacy total triple's statement on every `Mem.FSeq` memory, for a size-free postcondition. -/
theorem FTotalTriple.toTotal_on {c : MemM α} {P : Assn} {Q : α → Assn}
    (ht : FTotalTriple (up P) c (fun v => up (Q v))) (hQ : ∀ v, SizeFree (fun _ => none) (Q v)) :
    ∀ m hP hF, Heap.Disjoint hP hF → m.heap = hP ∪ hF → P hP → m.Seq → m.FSeq →
      ∃ v m' hQ, c.run m = pure (v, m') ∧ Heap.Disjoint hQ hF ∧
        m'.heap = hQ ∪ hF ∧ Q v hQ ∧ m'.Seq := by
  intro m hP hF hd hm hp hseq hs
  obtain ⟨v, m', hrun⟩ := ht.2 m _ _ (holds_ofHeap hd hm) ⟨by simpa using hp, rfl, rfl⟩ hs
  have := FTriple.toTriple_on ht.1 hQ m hP hF hd hm hp hseq hs
  rw [hrun] at this
  obtain ⟨hQ', h1, h2, h3, h4⟩ := this
  exact ⟨v, m', hQ', hrun, h1, h2, h3, h4⟩

end Full
end Zig
