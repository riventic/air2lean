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
    ((∀ x, e.off ≤ x → x < e.off + e.len → W (e.block, x)) ∧ e.block < m.blocks.size)
  /-- The counter cell's authority stays (`MemAuth.Keep`: no stack push, no step). -/
  auth : MemAuth.Keep m m'

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
  · exact hh.ghost.keep hs.ext (Nat.le_of_eq hs.bsize.symm) hs.auth
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
    (hno : ∀ u < m.threads.size, ∀ x, off ≤ x → x < off + len → (own u).heap (b, x) = none) :
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

/-- A rest that is the same up to `Cell.norm` (with the same tags, knowledge and ghost state). -/
theorem congrRest {rO' : Res} (ho : FOwned own rO m) (hs : FHeap.Sim rO'.heap rO.heap)
    (hk : rO'.know = rO.know) (hg : rO'.gh = rO.gh) : FOwned own rO' m :=
  ⟨let ⟨rT, h1, h2⟩ := ho.holds; ⟨rT, h1, h2.congrF hs hk hg⟩, ho.owns, ho.outside, ho.csize, ho.conc⟩

/-- A rest with the same bytes up to `Cell.norm`, whose tag constraints are the old ones or
none (a constraint can always be dropped), with the same knowledge and ghost state. -/
theorem congrRestU {rO' : Res} (ho : FOwned own rO m)
    (hn : ∀ l, (rO'.heap l).map (fun fc => fc.cell.norm) = (rO.heap l).map (fun fc => fc.cell.norm))
    (ha : ∀ l fc', rO'.heap l = some fc' → fc'.atom = none ∨ ∃ fc, rO.heap l = some fc ∧ fc.atom = fc'.atom)
    (hk : rO'.know = rO.know) (hg : rO'.gh = rO.gh) : FOwned own rO' m := by
  obtain ⟨rT, hs, hh⟩ := ho.holds
  have hnone : ∀ l, rO'.heap l = none ↔ rO.heap l = none := fun l => by
    have := hn l
    constructor
    · intro e; rw [e] at this; cases e' : rO.heap l <;> simp_all
    · intro e; rw [e] at this; cases e' : rO'.heap l <;> simp_all
  refine ⟨⟨rT, hs, fun l => ?_, ⟨fun l => ?_, fun l fc hl => ?_⟩, hh.know, hk ▸ hh.knowF,
    hg ▸ hh.ghost⟩, ho.owns, ho.outside, ho.csize, ho.conc⟩
  · rcases hh.disj l with e | e
    · exact .inl e
    · exact .inr ((hnone l).mpr e)
  · rw [hh.heap.1 l]
    simp only [FHeap.union_apply]
    cases e : rT.heap l with
    | some _ => rfl
    | none => simp only [Option.none_or]; exact (hn l).symm
  · simp only [FHeap.union_apply] at hl
    cases e : rT.heap l with
    | some fc0 =>
      rw [e] at hl; cases hl
      exact hh.heap.2 l fc (by simp [e])
    | none =>
      rw [e, Option.none_or] at hl
      rcases ha l fc hl with h0 | ⟨fc', h', hat⟩
      · unfold TagSat; rw [h0]; trivial
      · rw [← hat]; exact hh.heap.2 l fc' (by simp [e, h'])

/-- A byte of the rest is a live byte of the memory, up to `Cell.norm`. -/
theorem rest_cell (ho : FOwned own rO m) {l : Loc} {fc : FCell} (hl : rO.heap l = some fc) :
    (m.heap l).map Cell.norm = some fc.cell.norm := by
  obtain ⟨rT, -, hh⟩ := ho.holds
  have hT : rT.heap l = none := parts_off hh (by rw [hl]; simp)
  have := hh.heap.1 l
  simp only [FHeap.union_apply, hT, hl, Option.none_or, Option.map_some] at this
  exact this

end FOwned

end Full

/-! ## In a thread: the step's frame -/

namespace Conc
namespace Proto

open Full

variable {Tgt γ α : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ} {m : Mem}
  {n : Nat} {own : ThreadId → Res} {rO : Res}

/-- `WP.liftMem_fownedS` whose step keeps the rest's bytes (`FStepIn` of the rest). -/
theorem WP.liftMem_fownedR {x : MemM α} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' →
      Qa a r' → FStepIn rO.heap.erase m m' → Q a G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n := by
  obtain ⟨rR, hR, hRO, hh⟩ := ho.part htl
  have hcs : m.FConc := ⟨by rw [hc, ho.csize]; exact htl, ho.conc⟩
  have hx := ht m (own t) _ hh hp hcs (hc ▸ ho.owns t htl)
  refine WP.liftMem' (fun e he => ?_) (fun a m' hr => ?_) fun hn => hret.resolve_right fun hr => ?_
  · rw [he] at hx; exact .inr hx
  · rw [hr] at hx
    obtain ⟨r', hh', hq, hc', ho', hs⟩ := hx
    refine ⟨by rw [hs.threads], h a m' r' hr (ho.step hc htl hR hRO hh' hc' ho' hs) hq
      (hs.weaken fun l hl => ?_)⟩
    simp only [FHeap.erase, FHeap.erase_union, Heap.union_apply, Option.map_eq_none_iff] at hl ⊢
    cases e : rR.heap l <;> simp_all
  · obtain ⟨v, m', e⟩ := hr m (own t) _ hh hp hcs (hc ▸ ho.owns t htl)
    rw [e] at hn; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at hn

end Proto
end Conc

end Zig
