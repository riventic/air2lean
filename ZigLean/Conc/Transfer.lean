import ZigLean.Conc.Csl
import ZigLean.Conc.Capture

/-!
# Per-argument ownership transfer at a spawn

The generated `Tgt.captures` lists every captured field of a spawn target
(`ZigLean/Conc/Capture.lean`). A proof chooses, for every captured pointer, how the parent hands
its region to the child (`Transfer`):

- `owned R`: the parent moves exactly the cells of `R` to the child for the child's lifetime;
- `shared part`: the pointee lies in `part`, which no thread part may hold (for example an
  atomic cell under the protocol's global invariant); the child receives none of it.

`Capture.grant mode cs` is the resulting obligation on the child's private heap: it is the
separating conjunction of the cells of every field (a copied value contributes `emp`) and is
disjoint from every shared part. A field classified `other` makes the obligation unprovable.

`Capture.fork_grant` discharges the obligation at a spawn with `Owned.fork`, and
`Capture.join_regain` returns the child's whole part to the parent at the join (`Owned.join`).
`Capture.not_grant_of_unowned` is the negative side: a parent cannot hand over a region that
its part does not contain, for example a region already handed to another thread.

The obligation is a choice of `mode`, not a proof of exclusivity on its own: `shared` is not
tied to the pointer, so marking a pointer `shared` hands the child nothing. A worker proof that
then accesses the pointee has no cells for it and must justify every access through the
protocol's global invariant.
-/

namespace Zig.Conc

/-- How a spawn hands the region of one captured pointer to the child. -/
inductive Transfer where
  /-- The child receives exactly the cells of `R` until it is joined. -/
  | owned (R : Assn)
  /-- The pointee lies in `part`, outside every thread part; the child receives none of it. -/
  | shared (part : Heap)

namespace Transfer

/-- The cells the child receives. -/
def cells : Transfer → Assn
  | .owned R => R
  | .shared _ => Assn.emp

/-- The constraint on the child's whole private heap. -/
def excludes : Transfer → Heap → Prop
  | .owned _, _ => True
  | .shared part, h => Heap.Disjoint h part

end Transfer

namespace Capture

variable {mode : Ptr → Transfer}

/-- The cells the child receives for one captured field. -/
def cells (mode : Ptr → Transfer) : Capture → Assn
  | .value => Assn.emp
  | .ptr p => (mode p).cells
  | .slice s => (mode s.ptr).cells
  | .other => fun _ => False

theorem cells_ptr {p : Ptr} {t : Transfer} (hp : mode p = t) :
    (Capture.ptr p).cells mode = t.cells := by
  simp [cells, hp]

/-- The constraint one captured field puts on the child's whole private heap. -/
def excludes (mode : Ptr → Transfer) : Capture → Heap → Prop
  | .ptr p, h => (mode p).excludes h
  | .slice s, h => (mode s.ptr).excludes h
  | _, _ => True

theorem excludes_ptr {p : Ptr} {t : Transfer} (hp : mode p = t) {h : Heap} :
    (Capture.ptr p).excludes mode h = t.excludes h := by
  simp [excludes, hp]

/-- The separating conjunction of the cells of every field. -/
def cellsOf (mode : Ptr → Transfer) (cs : List Capture) : Assn :=
  cs.foldr (fun c A => Assn.sep (c.cells mode) A) Assn.emp

/-- The ownership obligation of a spawn with captured fields `cs`: the child's private heap is
the separating conjunction of the cells of every field, disjoint from every shared part. -/
def grant (mode : Ptr → Transfer) (cs : List Capture) : Assn := fun h =>
  cellsOf mode cs h ∧ ∀ c ∈ cs, c.excludes mode h

theorem grant_nil {h : Heap} : grant mode [] h ↔ h = Heap.empty := by
  simp [grant, cellsOf, Assn.emp]

/-- A copied value adds no obligation. -/
theorem grant_value {cs : List Capture} {h : Heap} :
    grant mode (.value :: cs) h ↔ grant mode cs h := by
  simp only [grant, cellsOf, List.foldr_cons, List.forall_mem_cons, excludes, true_and]
  constructor
  · rintro ⟨hs, he⟩; exact ⟨sep_emp.mp (sep_comm hs), he⟩
  · rintro ⟨hs, he⟩; exact ⟨sep_comm (sep_emp.mpr hs), he⟩

theorem cellsOf_nil : cellsOf mode [] Heap.empty := rfl

/-- A field that hands over `h₁`, before the fields that hand over `h₂`. -/
theorem cellsOf_cons {c : Capture} {cs : List Capture} {h₁ h₂ : Heap} (hd : Heap.Disjoint h₁ h₂)
    (hc : c.cells mode h₁) (hs : cellsOf mode cs h₂) : cellsOf mode (c :: cs) (h₁ ∪ h₂) :=
  ⟨h₁, h₂, hd, rfl, hc, hs⟩

/-- A field that hands over no cells: a copied value or a shared pointer. -/
theorem cellsOf_cons_empty {c : Capture} {cs : List Capture} {h : Heap}
    (hc : c.cells mode Heap.empty) (hs : cellsOf mode cs h) : cellsOf mode (c :: cs) h := by
  simpa using cellsOf_cons (Heap.disjoint_empty h).symm hc hs

/-- A copied value hands over no cells. -/
theorem cellsOf_value {cs : List Capture} {h : Heap} (hs : cellsOf mode cs h) :
    cellsOf mode (.value :: cs) h :=
  cellsOf_cons_empty rfl hs

/-- Every field's cells are part of a heap that satisfies the obligation. -/
theorem grant_cells {cs : List Capture} {h : Heap} (hg : grant mode cs h) {c : Capture}
    (hc : c ∈ cs) : ∃ h₁, c.cells mode h₁ ∧ h₁.Sub h := by
  obtain ⟨hs, -⟩ := hg
  induction cs generalizing h with
  | nil => cases hc
  | cons d ds ih =>
    obtain ⟨h₁, h₂, hd, rfl, h1, h2⟩ := hs
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨h₁, h1, Heap.sub_union_left⟩
    · obtain ⟨h₃, h3, hsub⟩ := ih hc h2
      exact ⟨h₃, h3, hsub.trans (Heap.sub_union_right hd)⟩

/-- A field whose pointer identities are not decomposed cannot be granted. -/
theorem not_grant_other {cs : List Capture} {h : Heap} (hc : Capture.other ∈ cs) :
    ¬ grant mode cs h := fun hg => by
  obtain ⟨_, h1, -⟩ := grant_cells hg hc
  exact h1

/-- A parent cannot hand over a captured region with a cell outside its own part. -/
theorem not_grant_of_unowned {mine : Heap} {cs : List Capture} {c : Capture} (hc : c ∈ cs)
    (hun : ∀ h, c.cells mode h → ∃ l, h l ≠ none ∧ mine l = none) :
    ¬ ∃ keep child, mine = keep ∪ child ∧ grant mode cs child := by
  rintro ⟨keep, child, rfl, hg⟩
  obtain ⟨h₁, h1, hsub⟩ := grant_cells hg hc
  obtain ⟨l, hl, hmine⟩ := hun h₁ h1
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hl
  rw [Heap.union_apply, hsub l x hx] at hmine
  cases keep l <;> simp at hmine

/-- Spawn: the parent `t` hands `child`, which satisfies the obligation, to the new thread. -/
theorem fork_grant {own : ThreadId → Heap} {m m' : Mem} {t c : ThreadId} {keep child : Heap}
    {cs : List Capture} (ho : Owned own m) (ht : t < m.threads.size)
    (hsplit : own t = keep ∪ child) (hd : Heap.Disjoint keep child) (hg : grant mode cs child)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    Owned (upd (upd own t keep) c child) m' ∧ grant mode cs (upd (upd own t keep) c child c) :=
  ⟨Owned.fork ho ht hsplit hd hf, by rw [upd_self]; exact hg⟩

/-- Join: the parent `t` regains every cell that the joined thread `u` holds. -/
theorem join_regain {own : ThreadId → Heap} {m m' : Mem} {t u : ThreadId}
    (ho : Owned own m) (ht : t < m.threads.size) (hut : u ≠ t)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m'))) :
    Owned (upd (upd own t (own t ∪ own u)) u Heap.empty) m' ∧
      (own u).Sub (upd (upd own t (own t ∪ own u)) u Heap.empty t) := by
  refine ⟨Owned.join ho ht hut hj, ?_⟩
  rw [upd_ne _ _ (Ne.symm hut), upd_self]
  exact Heap.sub_union_right (ho.disj t u (Ne.symm hut))

end Capture

end Zig.Conc
