import ZigLean.Sep.Full.Extent
import ZigLean.Conc.Own

/-!
# Thread triples over full-state resources

`FTTriple P c Q` is `FTriple` for a `MemM` step of one thread inside a concurrent run
(`docs/sep-threads.md`): the same resources (`Res`), the same `Holds` and the same assertions, with
ownership by the thread's clock (`Mem.Owns`, of the erased bytes) in place of `Mem.Seq`, and the
step's race freedom (`StepIn` of the frame's bytes) in the post. It replaces the legacy `TTriple`
(`ZigLean/Conc/Own.lean`).

- **Memory invariant** (`Mem.FConc`): the current thread exists, the atomic layout is well formed
  and live blocks lie apart (`FSeq` without `Seq`).
- **One logic.** `FTTriple.toFTriple`: a thread triple is a sequential one, since a sequential
  memory is a concurrent one whose current thread owns everything. The updates of the full-state
  library (`EUpd`, `Upd`, `know_intro`) apply in a thread unchanged (`FTTriple.eupd`, `upd`,
  `know_intro`): they are read in the memory without its recorded accesses (`Mem.noFp`), which
  holds the same resources.
- **The bridge** (`FTTriple.ofTTriple`, `ofTTriple_up`): a legacy thread triple of a `Tame` program
  lifts with the side conditions of `FTriple.ofTriple`. The step is read from `m.noFp` as a
  sequential program (`soloAt`), so the legacy bridge does the full-state part, and the legacy
  thread triple on the exact cells gives ownership and `StepIn`.
-/

namespace Zig
namespace Full

open FAssn Conc

/-- The memory invariant of a thread triple (module doc). -/
def _root_.Zig.Mem.FConc (m : Mem) : Prop :=
  m.current < m.clocks.size ∧ ShapesWF (shapes m) ∧ m.LiveLayout

/-- `m` without its recorded accesses: the same blocks, atomic layout and threads. -/
def _root_.Zig.Mem.noFp (m : Mem) : Mem := { m with footprint := #[] }

theorem _root_.Zig.Mem.FSeq.fconc {m : Mem} (h : m.FSeq) : m.FConc := ⟨h.1.single.1, h.2.1, h.2.2⟩

theorem _root_.Zig.Mem.FConc.noFp {m : Mem} (h : m.FConc) : m.noFp.FSeq :=
  ⟨⟨singleThread_empty rfl h.1⟩, h.2.1, h.2.2⟩

/-- In a one-thread memory the current thread owns every heap. -/
theorem _root_.Zig.Mem.SingleThread.owns {m : Mem} (h : m.SingleThread) (hp : Heap) :
    m.Owns m.current hp :=
  fun e he _ => (h.2 e he).2

/-- A step of the current thread keeps a one-thread memory one-thread. -/
theorem _root_.Zig.Mem.SingleThread.stepIn {m m' : Mem} {hF : Heap} (h : m.SingleThread)
    (hs : StepIn hF m m') : m'.SingleThread := by
  refine ⟨by rw [hs.current, hs.size]; exact h.1, fun e he => ⟨?_, ?_⟩⟩
  · rcases hs.fp e he with he' | ⟨ht, -⟩
    · rw [hs.current]; exact (h.2 e he').1
    · rw [hs.current]; exact ht
  · rw [hs.current]
    rcases hs.fpc e he with he' | hle
    · exact VClock.le_trans (h.2 e he').2 hs.mine
    · exact hle

namespace Holds

variable {m : Mem} {r r' rF : Res}

theorem toNoFp (hh : Holds m r rF) : Holds m.noFp r rF :=
  ⟨hh.disj, hh.heap, hh.know, hh.knowF, hh.ghost⟩

theorem ofNoFp (hh : Holds m.noFp r rF) : Holds m r rF :=
  ⟨hh.disj, hh.heap, hh.know, hh.knowF, hh.ghost⟩

/-- The bytes of a resource that `m` holds next to `rF` are part of any split `h ∪ hF` of `m`'s
bytes whose `hF` lies within `rF`'s bytes. -/
theorem erase_sub {h hF : Heap} (hh : Holds m r rF) (hm : m.heap = h ∪ hF)
    (hFs : ∀ l, hF l ≠ none → rF.heap l ≠ none) (l : Loc) (hl : r.heap.erase l ≠ none) :
    h l ≠ none := by
  obtain ⟨fc, hfc⟩ : ∃ fc, r.heap l = some fc := by
    cases e : r.heap l with
    | none => simp [FHeap.erase, e] at hl
    | some fc => exact ⟨fc, rfl⟩
  have hrF : rF.heap l = none := (hh.disj l).resolve_left (by simp [hfc])
  obtain ⟨c, hc, -⟩ := hh.heap.cell (l := l) (fc := fc) (by simp [hfc])
  rw [hm, Heap.union_apply] at hc
  intro hn
  rw [hn, Option.none_or] at hc
  exact hFs l (by rw [hc]; simp) hrF

/-- Two resources that `m` holds next to the same frame have the same bytes. -/
theorem erase_sub_of (hh : Holds m r rF) (hh' : Holds m r' rF) (l : Loc)
    (hl : r'.heap.erase l ≠ none) : r.heap.erase l ≠ none := by
  obtain ⟨fc, hfc⟩ : ∃ fc, r'.heap l = some fc := by
    cases e : r'.heap l with
    | none => simp [FHeap.erase, e] at hl
    | some fc => exact ⟨fc, rfl⟩
  have hrF : rF.heap l = none := (hh'.disj l).resolve_left (by simp [hfc])
  obtain ⟨c, hc, -⟩ := hh'.heap.cell (l := l) (fc := fc) (by simp [hfc])
  intro hn
  have hr : r.heap l = none := by simpa [FHeap.erase] using hn
  have := hh.heap.none (l := l) (by simp [hr, hrF])
  rw [hc] at this; cases this

end Holds

theorem FHeap.erase_fix_ne {m : Mem} {h : FHeap} {l : Loc} :
    (h.fix m).erase l ≠ none ↔ h.erase l ≠ none := by
  simp [FHeap.erase, FHeap.fix]

/-! ## Thread triples -/

/-- `FTriple` for a step of one thread inside a concurrent run (module doc). -/
def FTTriple {α : Type} (P : FAssn) (c : MemM α) (Q : α → FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → m.FConc → m.Owns m.current r.heap.erase →
    match (c.run m).run with
    | none => True
    | some (.error e) => e = .stackOverflow
    | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
        m'.Owns m'.current r'.heap.erase ∧ StepIn rF.heap.erase m m'

namespace FTTriple

variable {α β : Type} {P P' R : FAssn} {Q Q' : α → FAssn} {c : MemM α}

theorem of_run
    (h : ∀ m r rF, Holds m r rF → P r → m.FConc → m.Owns m.current r.heap.erase →
      ∃ v m' r', c.run m = pure (v, m') ∧ Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
        m'.Owns m'.current r'.heap.erase ∧ StepIn rF.heap.erase m m') :
    FTTriple P c Q := by
  intro m r rF hh hp hc ho
  obtain ⟨v, m', r', hr, h'⟩ := h m r rF hh hp hc ho
  rw [hr]; exact ⟨r', h'⟩

theorem conseq (ht : FTTriple P c Q) (hp : ∀ r, P' r → P r) (hq : ∀ v r, Q v r → Q' v r) :
    FTTriple P' c Q' := by
  intro m r rF hh hp' hc ho
  have := ht m r rF hh (hp _ hp') hc ho
  split at this
  · trivial
  · exact this
  · obtain ⟨r', a, b, d⟩ := this; exact ⟨r', a, hq _ _ b, d⟩

theorem pre (ht : FTTriple P c Q) (hp : ∀ r, P' r → P r) : FTTriple P' c Q :=
  conseq ht hp fun _ _ h => h

theorem post (ht : FTTriple P c Q) (hq : ∀ v r, Q v r → Q' v r) : FTTriple P c Q' :=
  conseq ht (fun _ h => h) hq

/-- **One logic**: a thread triple is a sequential triple (module doc). -/
theorem toFTriple (ht : FTTriple P c Q) : FTriple P c Q := by
  intro m r rF hh hp hs
  have := ht m r rF hh hp hs.fconc (hs.1.single.owns _)
  revert this
  cases (c.run m).run with
  | none => intro; trivial
  | some x =>
    cases x with
    | error e => intro h; exact h
    | ok x =>
      rintro ⟨r', hh', hq, hc', -, hst⟩
      exact ⟨r', hh', hq, ⟨hs.1.single.stepIn hst⟩, hc'.2⟩

/-- **The frame rule.** The frame's bytes, tags, knowledge and ghost state stay, and the thread
keeps owning the frame's bytes. -/
theorem frame (ht : FTTriple P c Q) : FTTriple (P ⋆ R) c (fun v => Q v ⋆ R) := by
  intro m r rF hh hpr hc ho
  obtain ⟨rP, rR, hd, rfl, hp, hr⟩ := hpr
  have hRF := (FHeap.disjoint_union_left.mp hh.disj).2
  have ho2 : m.Owns m.current (rP.heap.erase ∪ rR.heap.erase) := by simpa using ho
  have hoR : m.Owns m.current rR.heap.erase := Mem.OwnsC.right ho2
  have := ht m rP _ (Holds.split hd hh) hp hc (Mem.OwnsC.left ho2)
  split at this
  · trivial
  · exact this
  · obtain ⟨r', hh', hq, hc', ho', hst⟩ := this
    have hQR := (FHeap.disjoint_union_right.mp hh'.disj).1
    have hsubR : ∀ l, rR.heap.erase l ≠ none → (rR.heap ∪ rF.heap).erase l ≠ none := fun l hl => by
      simp only [FHeap.erase_union, Heap.union_apply]; cases e : rR.heap.erase l <;> simp_all
    refine ⟨_, Holds.join hQR hRF hh', ⟨r', rR, hQR, rfl, hq, hr⟩, hc', ?_,
      hst.weaken fun l hl => ?_⟩
    · show Mem.OwnsC _ _ _
      rw [FHeap.erase_union]; exact Mem.OwnsC.union ho' (Mem.Owns.frameSelf hst hoR hsubR)
    · simp only [FHeap.erase_union, Heap.union_apply]; cases e : rR.heap.erase l <;> simp_all

theorem frameL (ht : FTTriple P c Q) : FTTriple (R ⋆ P) c (fun v => R ⋆ Q v) :=
  conseq (frame (R := R) ht) (fun _ h => sep_comm h) (fun _ _ h => sep_comm h)

theorem ret (v : α) : FTTriple (Q v) (pure v : MemM α) Q :=
  of_run fun m r _ hh hq hc ho => ⟨v, m, r, rfl, hh, hq, hc, ho, StepIn.refl m _⟩

theorem ret' (v : α) (hq : ∀ r, P r → Q v r) : FTTriple P (pure v : MemM α) Q :=
  pre (ret v) hq

theorem bind {S : β → FAssn} {f : α → MemM β} (hc : FTTriple P c Q)
    (hf : ∀ v, FTTriple (Q v) (f v) S) : FTTriple P (c >>= f) S := by
  intro m r rF hh hp hcm ho
  have h1 := hc m r rF hh hp hcm ho
  simp only [StateT.run_bind, ExceptT.run_bind]
  revert h1
  cases (c.run m).run with
  | none => intro; trivial
  | some x =>
    cases x with
    | error e => intro h1; exact h1
    | ok x =>
      obtain ⟨v, m'⟩ := x
      rintro ⟨r', hh', hq, hc', ho', hst⟩
      have h2 := hf v m' r' rF hh' hq hc' ho'
      dsimp only [Bind.bind, Option.bind]
      split at h2
      · trivial
      · exact h2
      · obtain ⟨r'', a, b, d, e, hst'⟩ := h2
        exact ⟨r'', a, b, d, e, hst.trans hst'⟩

theorem ex {γ : Type} {P : γ → FAssn} (h : ∀ x, FTTriple (P x) c Q) : FTTriple (FAssn.ex P) c Q :=
  fun m r rF hh ⟨x, hp⟩ hc ho => h x m r rF hh hp hc ho

theorem lift {φ : Prop} (h : φ → FTTriple P c Q) : FTTriple (⟪φ⟫ ⋆ P) c Q := by
  intro m r rF hh hp hc ho
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact h hφ m r rF hh hp hc ho

/-- **An update of the precondition** (`EUpd`, read in `m.noFp`). -/
theorem eupd (hu : EUpd P P') (ht : FTTriple P' c Q) : FTTriple P c Q := by
  intro m r rF hh hp hc ho
  obtain ⟨r', hh', hp'⟩ := hu m.noFp r rF hh.toNoFp hp hc.noFp
  exact ht m r' rF hh'.ofNoFp hp' hc (ho.sub (hh.erase_sub_of hh'.ofNoFp))

/-- An update of the postcondition. -/
theorem eupd_post (ht : FTTriple P c Q) (hu : ∀ v, EUpd (Q v) (Q' v)) : FTTriple P c Q' := by
  intro m r rF hh hp hc ho
  have := ht m r rF hh hp hc ho
  split at this
  · trivial
  · exact this
  · obtain ⟨r', hh', hq, hc', ho', hst⟩ := this
    obtain ⟨r'', hh'', hq'⟩ := hu _ _ r' rF hh'.toNoFp hq hc'.noFp
    exact ⟨r'', hh''.ofNoFp, hq', hc', ho'.sub (hh'.erase_sub_of hh''.ofNoFp), hst⟩

/-- A ghost update of the precondition. -/
theorem upd (hu : Upd P P') (ht : FTTriple P' c Q) : FTTriple P c Q := eupd (EUpd.of_upd hu) ht

/-- A ghost update of the postcondition. -/
theorem upd_post (ht : FTTriple P c Q) (hu : ∀ v, Upd (Q v) (Q' v)) : FTTriple P c Q' :=
  eupd_post ht fun v => EUpd.of_upd (hu v)

/-- **Knowledge from ownership** (`FTriple.know_intro`). -/
theorem know_intro {b : BlockId} {A : Nat}
    (hc : ∀ r, P r → ∃ x fc, r.heap (b, x) = some fc ∧ fc.cell.addr = A)
    (ht : FTTriple (P ⋆ known b A) c Q) : FTTriple P c Q := by
  intro m r rF hh hp hcm ho
  obtain ⟨x, fc, hx, hA⟩ := hc r hp
  have hkn : m.kn (.addr b A) := by
    obtain ⟨blk, hblk, -, -, -, ha, -⟩ := hh.block hx
    exact ⟨blk, hblk, by rw [← hA, ha]⟩
  have hres : (P ⋆ known b A) ⟨r.heap, r.know.union (Know.single (.addr b A)), r.gh⟩ :=
    ⟨r, ⟨FHeap.empty, Know.single (.addr b A), Ghost.unit⟩, FHeap.disjoint_empty _,
      by rw [FHeap.union_empty, Ghost.add_unit], hp, rfl, rfl, rfl⟩
  exact ht m _ rF (hh.addKnow (Know.sub_single hkn)) hres hcm ho

end FTTriple

/-! ## Total thread triples

The termination side of a thread's step, as `FTotalTriple` is of a sequential one: the step
returns a value (no error, and a result: not "no result"). A concurrent run's termination is
counted in scheduler turns (`Stops`, `Proto.returnsWithin`, `codex/roadmap-batch-j`), whose
`liftMem` step needs the step to have a result; `FTTotalTriple.halts` gives it in every memory
where the thread owns the precondition. So a thread's `MemM` step enters both halves of the one
concurrent logic (`WP` for safety, `Stops` for turns) from one total thread triple. -/

/-- From every memory where the thread owns `P`, `c` returns a value. -/
def FTTReturns {α : Type} (P : FAssn) (c : MemM α) : Prop :=
  ∀ m r rF, Holds m r rF → P r → m.FConc → m.Owns m.current r.heap.erase →
    ∃ v m', c.run m = pure (v, m')

/-- Total correctness of a thread's step. -/
def FTTotalTriple {α : Type} (P : FAssn) (c : MemM α) (Q : α → FAssn) : Prop :=
  FTTriple P c Q ∧ FTTReturns P c

namespace FTTotalTriple

variable {α β : Type} {P P' R : FAssn} {Q Q' : α → FAssn} {c : MemM α}

theorem toPartial (ht : FTTotalTriple P c Q) : FTTriple P c Q := ht.1

/-- The step has a result (the premise of a turn budget's `liftMem` step). -/
theorem halts (ht : FTTotalTriple P c Q) {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r)
    (hc : m.FConc) (ho : m.Owns m.current r.heap.erase) : (c.run m).run ≠ none := by
  obtain ⟨v, m', e⟩ := ht.2 m r rF hh hp hc ho
  rw [e]; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run]

/-- **One logic**: a total thread triple is a total sequential triple. -/
theorem toFTotalTriple (ht : FTTotalTriple P c Q) : FTotalTriple P c Q :=
  ⟨ht.1.toFTriple, fun m r rF hh hp hs => ht.2 m r rF hh hp hs.fconc (hs.1.single.owns _)⟩

theorem conseq (ht : FTTotalTriple P c Q) (hp : ∀ r, P' r → P r) (hq : ∀ v r, Q v r → Q' v r) :
    FTTotalTriple P' c Q' :=
  ⟨ht.1.conseq hp hq, fun m r rF hh h' hc ho => ht.2 m r rF hh (hp _ h') hc ho⟩

theorem frame (ht : FTTotalTriple P c Q) : FTTotalTriple (P ⋆ R) c (fun v => Q v ⋆ R) := by
  refine ⟨ht.1.frame, fun m r rF hh hpr hc ho => ?_⟩
  obtain ⟨rP, rR, hd, rfl, hp, -⟩ := hpr
  have ho2 : m.Owns m.current (rP.heap.erase ∪ rR.heap.erase) := by simpa using ho
  exact ht.2 m rP _ (Holds.split hd hh) hp hc (Mem.OwnsC.left ho2)

theorem ret (v : α) : FTTotalTriple (Q v) (pure v : MemM α) Q :=
  ⟨FTTriple.ret v, fun m _ _ _ _ _ _ => ⟨v, m, rfl⟩⟩

theorem bind {S : β → FAssn} {f : α → MemM β} (hc : FTTotalTriple P c Q)
    (hf : ∀ v, FTTotalTriple (Q v) (f v) S) : FTTotalTriple P (c >>= f) S := by
  refine ⟨hc.1.bind fun v => (hf v).1, fun m r rF hh hp hcm ho => ?_⟩
  obtain ⟨v, m', e⟩ := hc.2 m r rF hh hp hcm ho
  have h1 := hc.1 m r rF hh hp hcm ho
  rw [e] at h1
  obtain ⟨r', hh', hq, hc', ho', -⟩ := h1
  obtain ⟨w, m'', e'⟩ := (hf v).2 m' r' rF hh' hq hc' ho'
  exact ⟨w, m'', by rw [StateT.run_bind, e]; exact e'⟩

theorem ex {γ : Type} {P : γ → FAssn} (h : ∀ x, FTTotalTriple (P x) c Q) :
    FTTotalTriple (FAssn.ex P) c Q :=
  ⟨FTTriple.ex fun x => (h x).1, fun m r rF hh ⟨x, hp⟩ hc ho => (h x).2 m r rF hh hp hc ho⟩

theorem lift {φ : Prop} (h : φ → FTTotalTriple P c Q) : FTTotalTriple (⟪φ⟫ ⋆ P) c Q :=
  ⟨FTTriple.lift fun hφ => (h hφ).1, fun m r rF hh hp hc ho => by
    obtain ⟨hφ, hp⟩ := sep_lift.mp hp
    exact (h hφ).2 m r rF hh hp hc ho⟩

end FTTotalTriple

/-! ## The bridge from legacy thread triples -/

open Classical in
/-- The run of `c` in `m`, as a program of `m.noFp` (with the final memory's accesses forgotten);
no result in any other memory. -/
noncomputable def soloAt {α : Type} (c : MemM α) (m : Mem) : MemM α := fun m₀ =>
  ExceptT.mk (if m₀ = m.noFp then (c.run m).run.map (Except.map fun p => (p.1, p.2.noFp)) else none)

section SoloAt

variable {α : Type} {c : MemM α} {m : Mem}

theorem soloAt_run_self :
    ((soloAt c m).run m.noFp).run = (c.run m).run.map (Except.map fun p => (p.1, p.2.noFp)) := by
  simp [soloAt, StateT.run, ExceptT.run, ExceptT.mk]

theorem soloAt_run_ne {m₀ : Mem} (h : m₀ ≠ m.noFp) : ((soloAt c m).run m₀).run = none := by
  simp [soloAt, StateT.run, ExceptT.run, ExceptT.mk, h]

/-- A successful run of `soloAt c m` is a run of `c` from `m`. -/
theorem soloAt_ok {m₀ m₁ : Mem} {v : α} (h : ((soloAt c m).run m₀).run = some (.ok (v, m₁))) :
    m₀ = m.noFp ∧ ∃ m', (c.run m).run = some (.ok (v, m')) ∧ m₁ = m'.noFp := by
  by_cases e : m₀ = m.noFp
  · subst e
    rw [soloAt_run_self] at h
    refine ⟨rfl, ?_⟩
    cases hr : (c.run m).run with
    | none => rw [hr] at h; cases h
    | some x =>
      rw [hr] at h
      cases x with
      | error => cases h
      | ok p =>
        simp only [Option.map_some, Except.map, Option.some.injEq, Except.ok.injEq] at h
        obtain ⟨v', m'⟩ := p
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨m', rfl, rfl⟩
  · rw [soloAt_run_ne e] at h; cases h

theorem Tame.soloAt (hc : Tame c) (m : Mem) : Tame (soloAt c m) := fun m₀ v m₁ h => by
  obtain ⟨rfl, m', hr, rfl⟩ := soloAt_ok h
  exact hc m v m' hr

theorem Keeps.soloAt {D : BlockId → Prop} (hc : Keeps D c) (m : Mem) : Keeps D (soloAt c m) :=
  fun m₀ v m₁ h => by
    obtain ⟨rfl, m', hr, rfl⟩ := soloAt_ok h
    exact hc m v m' hr

/-- A legacy thread triple of `c` gives a legacy triple of `soloAt c m` for the heaps that the
current thread of `m` owns. -/
theorem soloAt_triple {P : Assn} {Q : α → Assn} (ht : TTriple P c Q)
    (hc : m.current < m.clocks.size) :
    Triple (fun h => P h ∧ m.Owns m.current h) (soloAt c m) Q := by
  intro m₀ hP hF hd hm ⟨hp, ho⟩ _
  by_cases e : m₀ = m.noFp
  · subst e
    rw [soloAt_run_self]
    have := ht m hP hF hd hm hp hc ho
    revert this
    cases (c.run m).run with
    | none => intro; trivial
    | some x =>
      cases x with
      | error e => intro h; exact h
      | ok p =>
        obtain ⟨v, m'⟩ := p
        rintro ⟨hQ, hdQ, hmQ, hq, -, hst⟩
        have hc' : m'.current < m'.clocks.size := by rw [hst.current, hst.size]; exact hc
        exact ⟨hQ, hdQ, hmQ, hq, ⟨singleThread_empty rfl hc'⟩⟩
  · rw [soloAt_run_ne e]; trivial

end SoloAt

theorem SizeFree.owns {E : BlockId → Option (Nat × BlockKind)} {P : Assn} (hsf : SizeFree E P)
    (m : Mem) (t : ThreadId) : SizeFree E (fun h => P h ∧ m.Owns t h) :=
  fun h h' ⟨hp, ho⟩ hn h2 h3 => ⟨hsf h h' hp hn h2 h3, ho.sub fun l hl => by
    have := hn l
    cases e : h l <;> cases e' : h' l <;> simp_all⟩

namespace FTTriple

variable {α : Type} {P : Assn} {c : MemM α} {Q : α → Assn} {Pf : FAssn} {Qf : α → FAssn}

/-- **The bridge's core**: a legacy thread triple of `c` (for the precondition's exact cells) and,
in every memory, a full-state sequential triple of `soloAt c m` from the resources the thread owns,
give a thread triple. -/
theorem ofNoFp (ht : TTriple P c Q) (hP : ∀ m r rF, Holds m r rF → Pf r → P (r.fix m).heap.erase)
    (hF : ∀ m, m.current < m.clocks.size →
      FTriple (fun r => Pf r ∧ m.Owns m.current r.heap.erase) (soloAt c m) Qf) :
    FTTriple Pf c Qf := by
  intro m r rF hh hp hc ho
  have hs := hF m hc.1 m.noFp r rF hh.toNoFp ⟨hp, ho⟩ hc.noFp
  rw [soloAt_run_self] at hs
  have hFs : ∀ l, (rF.fix m).heap.erase l ≠ none → rF.heap.erase l ≠ none :=
    fun l h => FHeap.erase_fix_ne.mp h
  have hT := ht m _ _ (FHeap.erase_disjoint (FHeap.fix_disjoint hh.disj))
    (hh.fix.heap_exact hh.fix_exact hh.fix_exactF) (hP m r rF hh hp) hc.1
    (ho.sub fun l h => FHeap.erase_fix_ne.mp h)
  revert hs hT
  cases (c.run m).run with
  | none => intros; trivial
  | some x =>
    cases x with
    | error e => intro _ hT; exact hT
    | ok p =>
      obtain ⟨v, m'⟩ := p
      rintro ⟨r', hh', hq, hs'⟩ ⟨hQ, -, hmQ, -, hoQ, hst⟩
      refine ⟨r', hh'.ofNoFp, hq, ⟨by rw [hst.current, hst.size]; exact hc.1, hs'.2⟩, ?_,
        hst.weaken fun l h => FHeap.erase_fix_ne.mpr h⟩
      exact hoQ.sub (hh'.ofNoFp.erase_sub hmQ fun l h => by simpa [FHeap.erase] using hFs l h)

/-- **Lifting a legacy thread triple** with the side conditions of `FTriple.ofTriple`. -/
theorem ofTTriple {E : BlockId → Option (Nat × BlockKind)} {B : BlockId → Prop}
    (ht : TTriple P c Q) (hc : Tame c)
    (hB : ∀ h, P h → ∀ l c, h l = some c → B l.1)
    (hpin : ∀ h, P h → ∀ l c S K, h l = some c → E l.1 = some (S, K) → c.size = S ∧ c.kind = K)
    (hsf : SizeFree E P)
    (hk : (∀ b, B b → (E b).isSome) ∨ Keeps (fun b => (E b).isSome) c) :
    FTTriple (upE P E) c (fun v => upPost (Q v) B E) :=
  ofNoFp ht (fun _ _ _ hh hp => upE_fix hsf hpin hh hp) fun m hm =>
    (FTriple.ofTriple (soloAt_triple ht hm) (hc.soloAt m) (fun h hp => hB h hp.1)
      (fun h hp => hpin h hp.1) (hsf.owns m m.current) (hk.imp id (·.soloAt m))).pre
      fun _ ⟨hp, ho⟩ => ⟨⟨hp.1, ho⟩, hp.2⟩

/-- **Lifting a size-free legacy thread triple** of a program that keeps every live block. -/
theorem ofTTriple_up (ht : TTriple P c Q) (hc : Tame c) (hsf : SizeFree (fun _ => none) P)
    (hk : Keeps (fun _ => False) c) : FTTriple (up P) c (fun v => up (Q v)) :=
  ofNoFp ht (fun _ _ _ hh hp => upE_fix hsf (fun _ _ _ _ _ _ _ h => by cases h) hh (upE_none.mpr hp))
    fun m hm => (FTriple.ofTriple_up (soloAt_triple ht hm) (hc.soloAt m) (hsf.owns m m.current)
      (hk.soloAt m)).pre fun _ ⟨⟨hp, hk, hg⟩, ho⟩ => ⟨⟨hp, ho⟩, hk, hg⟩

end FTTriple

end Full
end Zig
