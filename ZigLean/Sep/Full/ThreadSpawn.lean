import ZigLean.Sep.Full.ThreadOwned
import ZigLean.Conc.SpawnLemmas

/-!
# Captures and failed spawns over the threads' parts

The full-state forms of the spawn-ownership lemmas (`ZigLean/Conc/Transfer.lean`,
`ZigLean/Conc/SpawnLemmas.lean`), for proofs that keep `FOwned` (`Full/ThreadOwned.lean`) in their
protocol invariant:

- `FTransfer`, `FCapture.grant mode cs`: how a spawn hands the region of each captured field
  (the generated `Tgt.captures`) to the child, as a full-state assertion on the child's part: the
  separating conjunction of every field's cells (a copied value contributes `emp`), disjoint from
  every shared part. A field classified `other` cannot be granted (`FCapture.not_grant_other`),
  nor a region outside the parent's part (`FCapture.not_grant_of_unowned`).
- `FCapture.fork_grant` hands the grant to the new thread (`FOwned.fork`);
  `FCapture.join_regain` returns the child's whole part to the parent (`FOwned.join`).
- `WP.spawnFailureRetains_fowned`: a failed assignment keeps the caller's split, the grant, the
  ghost state and the memory: no thread is created and no captured region moves.
-/

namespace Zig
namespace Full

open FAssn Conc Proto

/-- How a spawn hands the region of one captured pointer to the child. -/
inductive FTransfer where
  /-- The child receives exactly the resource of `R` until it is joined. -/
  | owned (R : FAssn)
  /-- The pointee lies in `part`, outside every thread part; the child receives none of it. -/
  | shared (part : FHeap)

namespace FTransfer

/-- The resource the child receives. -/
def cells : FTransfer → FAssn
  | .owned R => R
  | .shared _ => emp

/-- The constraint on the child's whole part. -/
def excludes : FTransfer → Res → Prop
  | .owned _, _ => True
  | .shared part, r => FHeap.Disjoint r.heap part

end FTransfer

namespace FCapture

variable {mode : Ptr → FTransfer} {cs : List Capture} {c : Capture} {r r₁ r₂ : Res}

/-- The resource the child receives for one captured field. -/
def cells (mode : Ptr → FTransfer) : Capture → FAssn
  | .value => emp
  | .ptr p => (mode p).cells
  | .slice s => (mode s.ptr).cells
  | .other => fun _ => False

theorem cells_ptr {p : Ptr} {t : FTransfer} (hp : mode p = t) :
    cells mode (.ptr p) = t.cells := by
  simp [cells, hp]

/-- The constraint one captured field puts on the child's whole part. -/
def excludes (mode : Ptr → FTransfer) : Capture → Res → Prop
  | .ptr p, r => (mode p).excludes r
  | .slice s, r => (mode s.ptr).excludes r
  | _, _ => True

theorem excludes_ptr {p : Ptr} {t : FTransfer} (hp : mode p = t) :
    excludes mode (.ptr p) r = t.excludes r := by
  simp [excludes, hp]

/-- The separating conjunction of the cells of every field. -/
def cellsOf (mode : Ptr → FTransfer) (cs : List Capture) : FAssn :=
  cs.foldr (fun c A => cells mode c ⋆ A) emp

/-- The ownership obligation of a spawn with captured fields `cs` (module doc). -/
def grant (mode : Ptr → FTransfer) (cs : List Capture) : FAssn := fun r =>
  cellsOf mode cs r ∧ ∀ c ∈ cs, excludes mode c r

theorem grant_nil : grant mode [] r ↔ emp r := by
  simp [grant, cellsOf]

theorem cellsOf_nil : cellsOf mode [] rnil := ⟨rfl, rfl, rfl⟩

/-- A field that hands over `r₁`, before the fields that hand over `r₂`. -/
theorem cellsOf_cons (hd : FHeap.Disjoint r₁.heap r₂.heap) (hc : cells mode c r₁)
    (hs : cellsOf mode cs r₂) : cellsOf mode (c :: cs) (rsum r₁ r₂) :=
  ⟨r₁, r₂, hd, rfl, hc, hs⟩

/-- A field that hands over nothing: a copied value or a shared pointer. -/
theorem cellsOf_cons_empty (hc : cells mode c rnil) (hs : cellsOf mode cs r) :
    cellsOf mode (c :: cs) r := by
  have := cellsOf_cons (FHeap.disjoint_empty r.heap).symm hc hs
  rwa [rnil_rsum] at this

/-- A copied value hands over nothing. -/
theorem cellsOf_value (hs : cellsOf mode cs r) : cellsOf mode (.value :: cs) r :=
  cellsOf_cons_empty ⟨rfl, rfl, rfl⟩ hs

/-- A copied value adds no obligation. -/
theorem grant_value : grant mode (.value :: cs) r ↔ grant mode cs r := by
  simp only [grant, cellsOf, List.foldr_cons, List.forall_mem_cons, excludes, true_and]
  constructor
  · rintro ⟨hs, he⟩; exact ⟨sep_emp.mp (sep_comm hs), he⟩
  · rintro ⟨hs, he⟩; exact ⟨sep_comm (sep_emp.mpr hs), he⟩

/-- Every field's cells are part of a resource that satisfies the obligation. -/
theorem grant_cells (hg : grant mode cs r) (hc : c ∈ cs) :
    ∃ r₁, cells mode c r₁ ∧ ∀ l, r₁.heap l ≠ none → r.heap l ≠ none := by
  obtain ⟨hs, -⟩ := hg
  induction cs generalizing r with
  | nil => cases hc
  | cons d ds ih =>
    obtain ⟨r₁, r₂, -, rfl, h1, h2⟩ := hs
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨r₁, h1, fun l hl => by simp only [FHeap.union_apply]; cases e : r₁.heap l <;> simp_all⟩
    · obtain ⟨r₃, h3, hsub⟩ := ih hc h2
      exact ⟨r₃, h3, fun l hl => by
        have := hsub l hl
        simp only [FHeap.union_apply]; cases e : r₁.heap l <;> simp_all⟩

/-- A field whose pointer identities are not decomposed cannot be granted. -/
theorem not_grant_other (hc : Capture.other ∈ cs) : ¬ grant mode cs r := fun hg => by
  obtain ⟨_, h1, -⟩ := grant_cells hg hc
  exact h1

/-- A parent cannot hand over a captured region with a byte outside its own part. -/
theorem not_grant_of_unowned {mine : Res} (hc : c ∈ cs)
    (hun : ∀ r, cells mode c r → ∃ l, r.heap l ≠ none ∧ mine.heap l = none) :
    ¬ ∃ keep child, mine = rsum keep child ∧ grant mode cs child := by
  rintro ⟨keep, child, rfl, hg⟩
  obtain ⟨r₁, h1, hsub⟩ := grant_cells hg hc
  obtain ⟨l, hl, hmine⟩ := hun r₁ h1
  have := hsub l hl
  simp only [FHeap.union_apply] at hmine
  cases e : keep.heap l <;> simp_all

variable {own : ThreadId → Res} {rO : Res} {m m' : Mem} {t u ch : ThreadId}

/-- **Spawn**: the parent `t` hands `child`, which satisfies the obligation, to the new thread. -/
theorem fork_grant {keep child : Res} {gt : Bool} (ho : FOwned own rO m) (ht : t < m.threads.size)
    (hsplit : own t = rsum keep child) (hd : FHeap.Disjoint keep.heap child.heap)
    (hg : grant mode cs child)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (ch, m'))) :
    FOwned (upd (upd own t keep) ch child) rO m' ∧ grant mode cs (upd (upd own t keep) ch child ch) :=
  ⟨FOwned.fork ho ht hsplit hd hf, by rw [upd_self]; exact hg⟩

/-- **Join**: the parent `t` regains every byte that the joined thread `u` holds. -/
theorem join_regain (ho : FOwned own rO m) (ht : t < m.threads.size) (hut : u ≠ t)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m'))) :
    FOwned (upd (upd own u rnil) t (rsum (own t) (own u))) rO m' ∧
      ∀ l fc, (own u).heap l = some fc →
        (upd (upd own u rnil) t (rsum (own t) (own u)) t).heap l = some fc := by
  refine ⟨FOwned.join ho ht hut hj, fun l fc hl => ?_⟩
  rw [upd_self]
  have hd : FHeap.Disjoint (own t).heap (own u).heap := by
    by_cases hu : u < m.threads.size
    · exact ho.disj ht hu (Ne.symm hut)
    · intro l; exact .inr (by rw [(ho.outside u (Nat.le_of_not_lt hu)).1]; rfl)
  simp only [FHeap.union_apply]
  rcases hd l with e | e
  · rw [e, hl]; rfl
  · rw [e] at hl; cases hl

end FCapture

end Full

namespace Conc
namespace Proto

open Full

variable {Tgt γ σ : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ} {m : Mem} {n : Nat}

/-- **A failed assignment leaves ownership with the caller.** Suppose the caller split its part
into `keep` and the `child` resource of the grant it prepared for the captured fields
(`FCapture.grant`). On a failed assignment the split, the grant, the ghost state and the memory
at the resumed choice are all unchanged: no thread is created and no captured region moves.
Contrast `FCapture.fork_grant`, which hands `child` to the new thread. -/
theorem WP.spawnFailureRetains_fowned {target : Tgt} {c : Nat} (hc : c ≠ 0) {s : σ}
    {own : ThreadId → Res} {rO keep child : Res} {mode : Ptr → FTransfer} {cs : List Capture}
    (ho : FOwned own rO m) (hsplit : own t = rsum keep child) (hg : FCapture.grant mode cs child) :
    P.WP t ((spawnOutcomeC c target : CM Tgt σ _).run s)
      (fun r G' m' _ => r = (.error (spawnErrorAt (c - 1)), s) ∧ G' = G ∧ m' = m ∧
        FOwned own rO m' ∧ own t = rsum keep child ∧ FCapture.grant mode cs child) G m n :=
  WP.spawnFailureFrame hc (frame := fun G' m' => G' = G ∧ m' = m ∧ FOwned own rO m' ∧
    own t = rsum keep child ∧ FCapture.grant mode cs child) ⟨rfl, rfl, ho, hsplit, hg⟩

end Proto
end Conc

end Zig
