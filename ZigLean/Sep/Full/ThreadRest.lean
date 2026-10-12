import ZigLean.Sep.Full.ThreadOwned

/-!
# The protocol's rest: shared words, and resources that move between it and a part

`FOwned own rO m` (`ZigLean/Sep/Full/ThreadOwned.lean`) keeps the resources that no thread holds
in the protocol's rest `rO`. Three kinds of steps change the rest (`docs/sep-threads.md` §The
threads' parts):

- **A step at shared bytes** (`RestStep W m m'`, `FOwned.restStep`): a sync object's atomic
  word, which no thread owns, is written by the object's code (a lock's `cmpxchg`, a shared
  counter's RMW). Its bytes `W` are in the rest as the memory's cells (`cellsAt W m`), without a
  tag constraint; a step that changes only them, records accesses only to them and adds at most
  locations over them keeps every part and the rest of the rest. The step lemma of each sync object
  (a lock's `LockWord.Step`, `ZigLean/Sep/Full/Lock.lean`) shows that it is such a step.
- **A resource moves** between the rest and a thread's part: `FOwned.take` (a lock's acquire: the
  thread's clock owns the resource's bytes) and `FOwned.give` (a release).
- **A recorded access of the current thread to bytes that no part has** (`FOwned.recordRest`: a
  read of a read-shared buffer, a futex wait's compare at a shared word).
-/

namespace Zig
namespace Full

open FAssn Conc Proto

/-- The memory's cells at the bytes `W`, without tag constraints, as a resource of the rest. -/
def cellsAt (W : Loc → Prop) [DecidablePred W] (m : Mem) : Res :=
  ⟨fun l => if W l then (m.heap l).map fun c => ⟨c, none⟩ else none, Know.none, Ghost.unit⟩

theorem cellsAt_none {W : Loc → Prop} [DecidablePred W] {m : Mem} {l : Loc} (h : ¬ W l) :
    (cellsAt W m).heap l = none := by
  simp [cellsAt, h]

theorem cellsAt_of {W : Loc → Prop} [DecidablePred W] {m : Mem} {l : Loc} (h : W l) :
    (cellsAt W m).heap l = (m.heap l).map fun c => ⟨c, none⟩ := by
  simp [cellsAt, h]

theorem cellsAt_some {W : Loc → Prop} [DecidablePred W] {m : Mem} {l : Loc} (h : W l)
    (hl : m.heap l ≠ none) : (cellsAt W m).heap l ≠ none := by
  rw [cellsAt_of h]
  cases e : m.heap l with
  | none => exact absurd e hl
  | some c => simp

/-- A step that changes only the bytes `W`, which stay live, and records accesses only to them
(module doc). -/
structure RestStep (W : Loc → Prop) (m m' : Mem) : Prop where
  threads : m'.threads = m.threads
  csize : m'.clocks.size = m.clocks.size
  clocks : ∀ u : Nat, VClock.le (m.clocks[u]!) (m'.clocks[u]!) = true
  bsize : m'.blocks.size = m.blocks.size
  heap : ∀ l, ¬ W l → m'.heap l = m.heap l
  live : ∀ l, W l → m'.heap l ≠ none
  kn : KMono m m'
  ext : KeepsExt m m'
  layout : m.LiveLayout → m'.LiveLayout
  tag : ∀ b x, ¬ W (b, x) → tagOf (shapes m') b x = tagOf (shapes m) b x
  wf : ShapesWF (shapes m) → ShapesWF (shapes m')
  fp : ∀ e ∈ m'.footprint, e ∈ m.footprint ∨
    ((∀ x, e.off ≤ x → (x < e.off + e.len ∨ x = e.off) → W (e.block, x)) ∧ e.block < m.blocks.size)

namespace FOwned

variable {own : ThreadId → Res} {rO Y : Res} {m m' : Mem} {t : ThreadId}

/-- A part has no byte of the rest. -/
theorem part_off (ho : FOwned own rO m) {u : ThreadId} (hu : u < m.threads.size) {l : Loc}
    (hl : rO.heap l ≠ none) : (own u).heap l = none := by
  obtain ⟨rR, -, -, hh⟩ := ho.part hu
  rcases hh.disj l with e | e
  · exact e
  · simp only [FHeap.union_apply, Option.or_eq_none_iff] at e; exact absurd e.2 hl

/-- The threads' parts together have no byte of the rest. -/
theorem parts_off {rT : Res} (hh : Holds m rT rO) {l : Loc} (hl : rO.heap l ≠ none) :
    rT.heap l = none :=
  (hh.disj l).resolve_right hl

/-- **A step at the shared bytes `W`** keeps the parts and the rest `Y`, which has no byte of
`W`; the rest's cells at `W` are the new memory's. -/
theorem restStep {W : Loc → Prop} [DecidablePred W] (ho : FOwned own (rsum (cellsAt W m) Y) m)
    (hs : RestStep W m m') (hW : ∀ l, W l → m.heap l ≠ none) (hY : ∀ l, W l → Y.heap l = none) :
    FOwned own (rsum (cellsAt W m') Y) m' := by
  obtain ⟨rT, hsep, hh⟩ := ho.holds
  -- the parts have no byte of `W`
  have hTW : ∀ l, W l → rT.heap l = none := fun l hl =>
    parts_off hh (by simp only [FHeap.union_apply]; rw [cellsAt_of hl]
                     cases e : m.heap l with
                     | none => exact absurd e (hW l hl)
                     | some c => simp)
  have hunion : ∀ l, ¬ W l → (rT.heap ∪ (cellsAt W m').heap ∪ Y.heap) l =
      (rT.heap ∪ (cellsAt W m).heap ∪ Y.heap) l := fun l hl => by
    simp [cellsAt_none hl]
  have hshapes := hs.tag
  refine ⟨⟨rT, by rw [hs.threads]; exact hsep, ⟨fun l => ?_, ⟨fun l => ?_, fun l fc hfc => ?_⟩,
    hh.know.trans hs.kn, ?_, ?_⟩⟩, fun u hu e he htc => ?_, fun u hu => ho.outside u (hs.threads ▸ hu),
    by rw [hs.csize, hs.threads]; exact ho.csize, hs.wf ho.conc.1, hs.layout ho.conc.2⟩
  · -- disjointness
    by_cases hl : W l
    · exact .inl (hTW l hl)
    · rcases hh.disj l with e | e
      · exact .inl e
      · right; simp only [FHeap.union_apply, Option.or_eq_none_iff] at e ⊢
        exact ⟨cellsAt_none hl, e.2⟩
  · -- the cells
    by_cases hl : W l
    · rw [← FHeap.union_assoc]
      simp only [FHeap.union_apply, hTW l hl, hY l hl, cellsAt_of hl, Option.none_or, Option.or_none]
      cases m'.heap l <;> rfl
    · rw [hs.heap l hl, ← FHeap.union_assoc, hunion l hl, FHeap.union_assoc]; exact hh.heap.1 l
  · -- the tags
    obtain ⟨b, x⟩ := l
    by_cases hl : W (b, x)
    · rw [← FHeap.union_assoc] at hfc
      simp only [FHeap.union_apply, hTW _ hl, hY _ hl, cellsAt_of hl, Option.none_or,
        Option.or_none, Option.map_eq_some_iff] at hfc
      obtain ⟨c, -, rfl⟩ := hfc
      trivial
    · rw [← FHeap.union_assoc, hunion _ hl, FHeap.union_assoc] at hfc
      have := hh.heap.2 _ fc hfc
      unfold TagSat at this ⊢; rw [hshapes b x hl]; exact this
  · -- the rest's knowledge
    exact (Know.Sub.union (Know.sub_none _) hh.knowF.right).trans hs.kn
  · exact hh.ghost.keep hs.ext (Nat.le_of_eq hs.bsize.symm)
  · -- the clocks of the parts
    rw [hs.threads] at hu
    rcases hs.fp e he with h | ⟨hw, hb⟩
    · exact VClock.le_trans (ho.owns u hu e h (htc.imp id fun h' => by rw [← hs.bsize]; exact h'))
        (hs.clocks u)
    · rcases htc with ⟨x, h1, h2, h3⟩ | hbe
      · exfalso; apply h3
        have hl := hw x h1 h2
        have := ho.part_off hu (l := (e.block, x)) (by
          simp only [FHeap.union_apply]; rw [cellsAt_of hl]
          cases e' : m.heap (e.block, x) with
          | none => exact absurd e' (hW _ hl)
          | some c => simp)
        simp [FHeap.erase, this]
      · rw [hs.bsize] at hbe; exact absurd hb (Nat.not_lt.mpr hbe)

/-- **Take**: thread `t` takes the resource `rA` of the rest `rsum rA Y`; its clock owns `rA`'s
bytes (a lock's acquire). -/
theorem take {rA : Res} (ho : FOwned own (rsum rA Y) m) (ht : t < m.threads.size)
    (hdA : FHeap.Disjoint rA.heap Y.heap) (hown : m.Owns t rA.heap.erase) :
    FOwned (upd own t (rsum (own t) rA)) Y m := by
  obtain ⟨rR, hR, hRO, hh⟩ := ho.part ht
  have hd := FHeap.disjoint_union_right.mp hh.disj
  have hRA : FHeap.Disjoint rR.heap rA.heap := (FHeap.disjoint_union_right.mp hRO).1
  have hRY : FHeap.Disjoint rR.heap Y.heap := (FHeap.disjoint_union_right.mp hRO).2
  have htA : FHeap.Disjoint (own t).heap rA.heap :=
    (FHeap.disjoint_union_right.mp hd.2).1
  have htAR : FHeap.Disjoint (rsum (own t) rA).heap rR.heap :=
    FHeap.disjoint_union_left.mpr ⟨hd.1, hRA.symm⟩
  refine ⟨?_, fun u hu => ?_, fun u hu => ?_, ho.csize, ho.conc⟩
  · refine ⟨_, parts_put ht hR htAR, ?_⟩
    -- regroup `own t ⋆ (rR ⋆ (rA ⋆ Y))` as `(own t ⋆ rA ⋆ rR) ⋆ Y`
    have h1 : Holds m (own t) (rsum rR (rsum rA Y)) := hh
    have h2 : Holds m (rsum (own t) rR) (rsum rA Y) := Holds.join hd.1 hRO h1
    have h3 : Holds m (rsum (rsum (own t) rR) rA) Y :=
      Holds.join (FHeap.disjoint_union_left.mpr ⟨htA, hRA⟩) hdA h2
    have e : rsum (rsum (own t) rR) rA = rsum (rsum (own t) rA) rR := by
      rw [rsum_assoc, rsum_comm hRA, ← rsum_assoc]
    rw [e] at h3; exact h3
  · by_cases hut : u = t
    · subst hut; rw [upd_self]
      simp only [rsum, FHeap.erase_union]
      exact Mem.OwnsC.union (ho.owns u hu) hown
    · rw [upd_ne _ _ hut]; exact ho.owns u hu
  · rw [upd_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le ht hu))]; exact ho.outside u hu

/-- **Give**: thread `t` gives the resource `rA` of its part `rsum a rA` to the rest (a lock's
release). -/
theorem give {a rA : Res} (ho : FOwned own Y m) (ht : t < m.threads.size)
    (hsplit : own t = rsum a rA) (hd : FHeap.Disjoint a.heap rA.heap) :
    FOwned (upd own t a) (rsum rA Y) m := by
  obtain ⟨rR, hR, hRO, hh⟩ := ho.part ht
  rw [hsplit] at hh
  have hdR := FHeap.disjoint_union_right.mp hh.disj
  have haR : FHeap.Disjoint a.heap rR.heap :=
    (FHeap.disjoint_union_left.mp hdR.1).1
  have hAR : FHeap.Disjoint rA.heap rR.heap := (FHeap.disjoint_union_left.mp hdR.1).2
  have hAY : FHeap.Disjoint rA.heap Y.heap := (FHeap.disjoint_union_left.mp hdR.2).2
  refine ⟨?_, fun u hu => ?_, fun u hu => ?_, ho.csize, ho.conc⟩
  · refine ⟨_, parts_put ht hR haR, ?_⟩
    -- regroup `(a ⋆ rA) ⋆ (rR ⋆ Y)` as `(a ⋆ rR) ⋆ (rA ⋆ Y)`
    have h1 : Holds m (rsum (rsum a rA) rR) Y := Holds.join hdR.1 hRO hh
    have e : rsum (rsum a rA) rR = rsum (rsum a rR) rA := by
      rw [rsum_assoc, rsum_comm hAR, ← rsum_assoc]
    rw [e] at h1
    exact Holds.split (FHeap.disjoint_union_left.mpr ⟨hd, hAR.symm⟩) h1
  · by_cases hut : u = t
    · subst hut; rw [upd_self]
      have := ho.owns u hu; rw [hsplit] at this
      simp only [rsum, FHeap.erase_union] at this
      exact this.left
    · rw [upd_ne _ _ hut]; exact ho.owns u hu
  · rw [upd_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le ht hu))]; exact ho.outside u hu

/-- **A recorded access of the current thread `t` to bytes that no part has** keeps the parts
and the rest. -/
theorem recordRest {b : BlockId} {off len : Nat} {kind : AccessKind} (ho : FOwned own rO m)
    (hc : m.current = t) (ht : t < m.threads.size) (hb : b < m.blocks.size)
    (hno : ∀ u < m.threads.size, ∀ x, off ≤ x → (x < off + len ∨ x = off) → (own u).heap (b, x) = none) :
    FOwned own rO (m.recordAt b off len kind) := by
  have hcs : m.current < m.clocks.size := by rw [hc, ho.csize]; exact ht
  refine ⟨?_, fun u hu e he htc => ?_, ho.outside, by simp [Mem.recordAt]; exact ho.csize,
    ⟨by simpa [shapes, Mem.recordAt] using ho.conc.1, ?_⟩⟩
  · obtain ⟨rT, h1, h2⟩ := ho.holds; exact ⟨rT, h1, Holds.congrMem (m := m) rfl rfl h2⟩
  · have hle : VClock.le (m.clocks[u]!) ((m.recordAt b off len kind).clocks[u]!) = true := by
      simp only [Mem.recordAt]; rw [getElem!_set!_ite]
      split
      · rename_i h; rw [h.1]; exact VClock.le_bump _ _
      · exact VClock.le_refl _
    simp only [Mem.recordAt, Array.mem_push] at he
    rcases he with he | rfl
    · exact VClock.le_trans (ho.owns u hu e he htc) hle
    · exfalso
      rcases htc with ⟨x, h1, h2, h3⟩ | hbe
      · simp only at h1 h2 h3
        exact h3 (by simp [FHeap.erase, hno u hu x h1 h2])
      · simp only [Mem.recordAt] at hbe; exact absurd hb (Nat.not_lt.mpr hbe)
  · obtain ⟨hd, hbd⟩ := ho.conc.2
    exact ⟨fun b b' blk blk' hne h1 h2 => hd b b' blk blk' hne h1 h2, fun b blk h1 => hbd b blk h1⟩

end FOwned

end Full
end Zig
