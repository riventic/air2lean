import ZigLean.Sep.Full.Extent
import ZigLean.Conc.Clock

/-!
# Thread triples over full-state resources

`FTTriple P c Q` is `FTriple` for a `MemM` step of one thread inside a concurrent run
(`docs/sep-threads.md`): the same resources (`Res`), the same `Holds` and the same assertions, with
ownership by the thread's clock (`Mem.Owns`, of the erased bytes) in place of `Mem.Seq`, and the
step's race freedom (`FStepIn` of the frame's bytes: the frame, the other threads and the atomic
locations over the frame stay) in the post. It replaces the legacy `TTriple`
(`ZigLean/Conc/Own.lean`).

- **Memory invariant** (`Mem.FConc`): the current thread exists, the atomic layout is well formed
  and live blocks lie apart (`FSeq` without `Seq`).
- **One logic.** `FTTriple.toFTriple`: a thread triple is a sequential one, since a sequential
  memory is a concurrent one whose current thread owns everything. The updates of the full-state
  library (`EUpd`, `Upd`, `know_intro`) apply in a thread unchanged (`FTTriple.eupd`, `upd`,
  `know_intro`): they are read in the memory without its recorded accesses (`Mem.noFp`), which
  holds the same resources.
- **Ownership and race freedom** come from `ZigLean/Conc/Clock.lean` (`Mem.Owns`, `FStepIn`);
  this module does not import the legacy layer, and no legacy thread triple is lifted. The thread
  rules of the memory primitives are built on `ZigLean/Sep/Full/ThreadStep.lean`.
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

/-- A step of the current thread keeps a one-thread memory one-thread (`FStepIn`). -/
theorem _root_.Zig.Mem.SingleThread.fstep {m m' : Mem} {hF : Heap} (h : m.SingleThread)
    (hs : FStepIn hF m m') : m'.SingleThread := by
  refine ⟨by rw [hs.current, hs.size]; exact h.1, fun e he => ⟨?_, ?_⟩⟩
  · rcases hs.fp e he with ⟨e₀, he₀, hn⟩ | ⟨ht, -⟩
    · rw [hs.current, hn.1]; exact (h.2 e₀ he₀).1
    · rw [hs.current]; exact ht
  · rw [hs.current]
    rcases hs.fpc e he with ⟨e₀, he₀, hn⟩ | hle
    · exact VClock.le_trans hn.clock (VClock.le_trans (h.2 e₀ he₀).2 hs.mine)
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
        m'.Owns m'.current r'.heap.erase ∧ FStepIn rF.heap.erase m m'

namespace FTTriple

variable {α β : Type} {P P' R : FAssn} {Q Q' : α → FAssn} {c : MemM α}

theorem of_run
    (h : ∀ m r rF, Holds m r rF → P r → m.FConc → m.Owns m.current r.heap.erase →
      ∃ v m' r', c.run m = pure (v, m') ∧ Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
        m'.Owns m'.current r'.heap.erase ∧ FStepIn rF.heap.erase m m') :
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
      exact ⟨r', hh', hq, ⟨hs.1.single.fstep hst⟩, hc'.2⟩

/-- `of_fix` (below) in the memories with a property `Φ`, a fact about the memory that a
precondition cannot state (`Mem.MsgCov` at an oracle pick's resumption): the body of the thread
triple in each of them. -/
theorem of_fix_on (Φ : Mem → Prop) (hP : ∀ m r rF, Holds m r rF → P r → P (r.fix m))
    (h : ∀ m r rF, Φ m → Holds m r rF → Exact m r → Exact m rF → P r → m.FConc →
      m.Owns m.current r.heap.erase →
      match (c.run m).run with
      | none => True
      | some (.error e) => e = .stackOverflow
      | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
          m'.Owns m'.current r'.heap.erase ∧ FStepIn rF.heap.erase m m') :
    ∀ m r rF, Φ m → Holds m r rF → P r → m.FConc → m.Owns m.current r.heap.erase →
      match (c.run m).run with
      | none => True
      | some (.error e) => e = .stackOverflow
      | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
          m'.Owns m'.current r'.heap.erase ∧ FStepIn rF.heap.erase m m' := by
  intro m r rF hΦ hh hp hc ho
  have := h m (r.fix m) (rF.fix m) hΦ hh.fix hh.fix_exact hh.fix_exactF (hP m r rF hh hp) hc
    (ho.sub fun l hl => FHeap.erase_fix_ne.mp hl)
  split at this
  · trivial
  · exact this
  · obtain ⟨r', hh', hq, hc', ho', hst⟩ := this
    exact ⟨r', hh'.congrF hh.fix_sim.symm rfl rfl, hq, hc', ho',
      hst.weaken fun l hl => FHeap.erase_fix_ne.mpr hl⟩

/-- **Thread rules from exact cells** (`FTriple.of_fix`): it is enough to prove a thread triple
for resources whose cells are the memory's exact cells, if the precondition survives reading
the actual sizes. The thread owns the same bytes, and the frame has the same bytes. -/
theorem of_fix (hP : ∀ m r rF, Holds m r rF → P r → P (r.fix m))
    (h : ∀ m r rF, Holds m r rF → Exact m r → Exact m rF → P r → m.FConc →
      m.Owns m.current r.heap.erase →
      match (c.run m).run with
      | none => True
      | some (.error e) => e = .stackOverflow
      | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
          m'.Owns m'.current r'.heap.erase ∧ FStepIn rF.heap.erase m m') :
    FTTriple P c Q :=
  fun m r rF hh hp hc ho =>
    of_fix_on (fun _ => True) hP (fun m r rF _ => h m r rF) m r rF trivial hh hp hc ho

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
      rw [FHeap.erase_union]; exact Mem.OwnsC.union ho' (Mem.Owns.fstepSelf hst hoR hsubR)
    · simp only [FHeap.erase_union, Heap.union_apply]; cases e : rR.heap.erase l <;> simp_all

theorem frameL (ht : FTTriple P c Q) : FTTriple (R ⋆ P) c (fun v => R ⋆ Q v) :=
  conseq (frame (R := R) ht) (fun _ h => sep_comm h) (fun _ _ h => sep_comm h)

theorem ret (v : α) : FTTriple (Q v) (pure v : MemM α) Q :=
  of_run fun m r _ hh hq hc ho => ⟨v, m, r, rfl, hh, hq, hc, ho, FStepIn.refl m _⟩

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

/-- Knowledge and ghost state (anything that owns no bytes) can be forgotten (`FTriple.drop`). -/
theorem drop {K : α → FAssn} (ht : FTTriple P c (fun v => Q v ⋆ K v))
    (hK : ∀ v r, K v r → r.heap = FHeap.empty) : FTTriple P c Q := by
  intro m r rF hh hp hcm ho
  have := ht m r rF hh hp hcm ho
  split at this
  · trivial
  · exact this
  · obtain ⟨r', ⟨hd, hm, hk, hkF, hg⟩, ⟨r₁, r₂, -, rfl, hq, hk2⟩, hc', ho', hs'⟩ := this
    have e := hK _ _ hk2
    simp only [e, FHeap.union_empty] at hd hm ho'
    exact ⟨r₁, ⟨hd, hm, hk.left, hkF, GOk.mono hg⟩, hq, hc', ho', hs'⟩

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

end Full
end Zig
