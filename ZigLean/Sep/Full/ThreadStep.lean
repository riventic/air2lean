import ZigLean.Sep.Full.Thread

/-!
# Thread rules of the memory primitives (`docs/sep-threads.md`, S2)

A memory primitive (a load, a store, `alloc`, `free`, the page mappings) reads the recorded
accesses of a memory (its footprint) only for its race check. Where the current thread owns what
the step touches, no check fails, so the step runs in a concurrent memory `m` as in `m.noFp` (the
same memory without the record, a sequential one), with `m`'s record in front. That is
**`ThreadLocal P c`**: from every memory where the thread owns `P`,

* the run of `c` from `m` is its run from `m.noFp` up to the record of accesses (the results
  agree after `Mem.noFp`);
* a result of the run from `m` is a step of the current thread outside the frame (`FStepIn` of
  the frame's bytes: no other thread's state, no atomic location over the frame, no byte of the
  frame accessed, no `const` global written, old entries kept or narrowed), and a byte of a block
  of `m` that comes alive has no recorded access but ones before the thread's clock
  (`Mem.RevivesOwned`: a growth in place forgets the history of the grown offsets; a step that
  makes no old byte alive, `Mem.NoRevive`, has it).

**The kernel** (`FTTriple.ofSeq`, `FTTotalTriple.ofSeq`): a sequential triple of a `ThreadLocal`
step is a thread triple. The resources, the postcondition and the memory invariant come from the
sequential triple read in `m.noFp` (`Holds` reads only the blocks and the atomic layout); race
freedom comes from `ThreadLocal`, and ownership of the post's bytes from both (a byte of the post
is a byte of the pre, in a new block, or revived without history: `owns_step`). So a primitive
has one proof, its sequential triple plus
its locality, and its `@[fsym]` sequential rule is the thread rule read sequentially
(`FTTotalTriple.toFTotalTriple`).

`ThreadLocal` frames (`ThreadLocal.frame`), and a step that leaves the memory as it is has a thread
rule without the kernel (`FTTotalTriple.of_read`). The building blocks of the primitives' locality
are below: runs with a record in front (`RunFp`, which gives `ThreadLocal` by `ThreadLocal.intro`
for a step that revives nothing), and accesses to bytes that `P` owns
(`OwnsPtr`, `ThreadLocal.loadBytes`/`load`/`storeBytes`/`store`), `alloc` and `free`. Local steps
compose (`ThreadLocal.bind`, `pure`, `throw`, `ite`, `readBind`), which gives `@memset`,
`@memmove` and `@memcpy` over owned bytes.
-/

namespace Zig
namespace Full

open FAssn Conc

/-! ## Memories with a record in front -/

theorem _root_.Zig.Mem.noFp_withFp (m : Mem) : m.noFp.withFp m.footprint = m := by
  cases m; simp [Mem.noFp, Mem.withFp]

/-- No byte of a block of `m` comes alive in `m'`: the live bytes of `m'` in `m`'s blocks were
live in `m`. -/
def _root_.Zig.Mem.NoRevive (m m' : Mem) : Prop :=
  ∀ b x, b < m.blocks.size → m'.heap (b, x) ≠ none → m.heap (b, x) ≠ none

theorem _root_.Zig.Mem.NoRevive.refl (m : Mem) : m.NoRevive m := fun _ _ _ h => h

/-- A step of the current thread in `m.noFp` is one in `m`, with `m`'s record in front. -/
theorem Holds.withFp {m₀ : Mem} {r rF : Res} (hh : Holds m₀ r rF) (F : Array FootprintEntry) :
    Holds (m₀.withFp F) r rF :=
  ⟨hh.disj, hh.heap, hh.know, hh.knowF, hh.ghost.of_blocks rfl rfl rfl rfl⟩

theorem _root_.Zig.FStepIn.withFp {hF : Heap} {m m₀ : Mem} (hs : FStepIn hF m.noFp m₀) :
    FStepIn hF m (m₀.withFp m.footprint) where
  current := hs.current
  threads := hs.threads
  waiters := hs.waiters
  woken := hs.woken
  groups := hs.groups
  size := hs.size
  others := hs.others
  mine := hs.mine
  blocks := hs.blocks
  nextMsg := hs.nextMsg
  atomics := let ⟨σ, ha⟩ := hs.atomics; ⟨σ, ha.mono, ha.kept, ha.frame, ha.new, ha.seen, ha.own⟩
  fp e he := by
    rcases Array.mem_append.mp he with he | he
    · exact .inl ⟨e, he, .refl e⟩
    · rcases hs.fp e he with ⟨_, he', -⟩ | h
      · simp [Mem.noFp] at he'
      · exact .inr h
  fpc e he := by
    rcases Array.mem_append.mp he with he | he
    · exact .inl ⟨e, he, .refl e⟩
    · rcases hs.fpc e he with ⟨_, he', -⟩ | h
      · simp [Mem.noFp] at he'
      · exact .inr h
  const := hs.const
  cov F h := by
    have e1 : m.noFp.withFp (F ++ m.footprint) = m.withFp F := by simp [Mem.noFp, Mem.withFp]
    have e2 : (m₀.withFp m.footprint).withFp F = m₀.withFp (F ++ m.footprint) := by
      simp [Mem.withFp, Array.append_assoc]
    rw [e2]; exact hs.cov _ (e1 ▸ h)

/-- **A byte that comes alive is the thread's**: a byte of a block of `m` that is live in `m'`
but not in `m` has only recorded accesses that happened before the thread's clock in `m'`. A
revival that forgets the byte's history (`Mem.forgetFrom`, a growth in place) gives it; so does
every step that makes no byte of an old block alive (`Mem.NoRevive.revivesOwned`). -/
def _root_.Zig.Mem.RevivesOwned (m m' : Mem) : Prop :=
  ∀ b x, b < m.blocks.size → m'.heap (b, x) ≠ none → m.heap (b, x) = none →
    ∀ e ∈ m'.footprint, e.block = b → e.off ≤ x → x < e.off + e.len →
      VClock.le e.clock (m'.clocks[m'.current]!) = true

theorem _root_.Zig.Mem.NoRevive.revivesOwned {m m' : Mem} (h : m.NoRevive m') : m.RevivesOwned m' :=
  fun b x hb h' hn => absurd hn (h b x hb h')

/-- Two steps of the thread that revive only bytes it owns revive only bytes it owns. -/
theorem _root_.Zig.Mem.RevivesOwned.trans {m m₁ m₂ : Mem} {hF hF' : Heap} (h₁ : m.RevivesOwned m₁)
    (hs₁ : FStepIn hF m m₁) (h₂ : m₁.RevivesOwned m₂) (hs₂ : FStepIn hF' m₁ m₂) :
    m.RevivesOwned m₂ := by
  intro b x hb hl hd e he heb h1 h2
  by_cases hl₁ : m₁.heap (b, x) = none
  · exact h₂ b x (Nat.lt_of_lt_of_le hb hs₁.blocks) hl hl₁ e he heb h1 h2
  · have hcur : m₂.current = m₁.current := hs₂.current
    rcases hs₂.fpc e he with ⟨e₀, he₀, hn⟩ | hle
    · obtain ⟨-, hb₀, -, ho₀, hl₀, hc₀⟩ := hn
      have := h₁ b x hb hl₁ hd e₀ he₀ (hb₀ ▸ heb) (by omega) (by omega)
      rw [hcur]
      exact VClock.le_trans hc₀ (VClock.le_trans this hs₂.mine)
    · rw [hcur]; exact hle

/-- **A revival that forgets the history** (`Mem.forgetFrom b S`): a step whose record is a record
with the accesses to block `b` from offset `S` on forgotten, and which brings to life only bytes of
`b` from `S` on, revives only bytes the thread owns. -/
theorem _root_.Zig.Mem.RevivesOwned.of_forgetFrom {m m₁ m' : Mem} {b : BlockId} {S : Nat}
    (hfp : m'.footprint = (m₁.forgetFrom b S).footprint)
    (hgrow : ∀ b' x, b' < m.blocks.size → m'.heap (b', x) ≠ none → m.heap (b', x) = none →
      b' = b ∧ S ≤ x) :
    m.RevivesOwned m' := by
  intro b' x hb' hl hd e he heb h1 h2
  obtain ⟨rfl, hS⟩ := hgrow b' x hb' hl hd
  rw [hfp] at he
  rcases Mem.forgetFrom_entry he heb with hc | ⟨-, hend⟩
  · rw [hc]; exact VClock.le_default _
  · omega

/-- **Ownership after a step**: the thread owns the bytes of a resource that the memory after the
step holds next to the frame. A byte of it was a byte of the resource before (the frame keeps its
own), or is in a new block, or came alive with no access but the thread's (`RevivesOwned`). -/
theorem owns_step {m m' : Mem} {r r' rF : Res} (hh : Holds m r rF)
    (ho : m.Owns m.current r.heap.erase) (hs : FStepIn rF.heap.erase m m')
    (hrev : m.RevivesOwned m') (hh' : Holds m' r' rF) :
    m'.Owns m'.current r'.heap.erase := by
  intro e he ht
  have hcur : m'.current = m.current := hs.current
  show VClock.le e.clock (m'.clocks[m'.current]!) = true
  rw [hcur]
  -- a byte of `r'` is live in `m'`
  have hlive : ∀ x, r'.heap.erase (e.block, x) ≠ none → m'.heap (e.block, x) ≠ none := by
    intro x h3
    obtain ⟨fc, hfc⟩ : ∃ fc, r'.heap (e.block, x) = some fc := by
      cases e' : r'.heap (e.block, x) with
      | none => simp [FHeap.erase, e'] at h3
      | some fc => exact ⟨fc, rfl⟩
    obtain ⟨c, hc, -⟩ := hh'.heap.cell (l := (e.block, x)) (fc := fc) (by simp [hfc])
    rw [hc]; simp
  rcases hs.fpc e he with ⟨e₀, he₀, hn⟩ | hle
  · obtain ⟨-, hb₀, -, ho₀, hl₀, hc₀⟩ := hn
    by_cases hrv : ∃ x, e.off ≤ x ∧ x < e.off + e.len ∧ r'.heap.erase (e.block, x) ≠ none ∧
        e.block < m.blocks.size ∧ m.heap (e.block, x) = none
    · -- a byte that came alive: the thread owns it
      obtain ⟨x, h1, h2, h3, hb, hm⟩ := hrv
      rw [← hcur]
      exact hrev _ x hb (hlive x h3) hm e he rfl h1 h2
    refine VClock.le_trans hc₀ (VClock.le_trans (ho e₀ he₀ ?_) hs.mine)
    rcases ht with ⟨x, h1, h2, h3⟩ | hb
    · by_cases hb : e.block < m.blocks.size
      · have hm : m.heap (e.block, x) ≠ none := fun hm => hrv ⟨x, h1, h2, h3, hb, hm⟩
        left
        refine ⟨x, by omega, by omega, ?_⟩
        rw [← hb₀]
        obtain ⟨fc, hfc⟩ : ∃ fc, r'.heap (e.block, x) = some fc := by
          cases e' : r'.heap (e.block, x) with
          | none => simp [FHeap.erase, e'] at h3
          | some fc => exact ⟨fc, rfl⟩
        have hrF : rF.heap (e.block, x) = none := (hh'.disj _).resolve_left (by simp [hfc])
        intro hn
        have hr : r.heap (e.block, x) = none := by simpa [FHeap.erase] using hn
        exact hm (hh.heap.none (by simp [hr, hrF]))
      · exact .inr (by rw [← hb₀]; exact Nat.le_of_not_lt hb)
    · exact .inr (by rw [← hb₀]; exact Nat.le_trans hs.blocks hb)
  · exact hle

/-! ## Local steps and the kernel -/

/-- **A step local to the thread that owns `P`** (module doc): its run from `m` is its run from
`m.noFp` up to the record of accesses, and a result of it is a step of the thread outside the
frame that revives only bytes the thread owns. -/
def ThreadLocal {α : Type} (P : FAssn) (c : MemM α) : Prop :=
  ∀ m r rF, Holds m r rF → P r → m.FConc → m.Owns m.current r.heap.erase →
    (c.run m).run.map (Except.map fun p => (p.1, p.2.noFp)) =
      ((c.run m.noFp).run).map (Except.map fun p => (p.1, p.2.noFp)) ∧
    ∀ v m', c.run m = pure (v, m') → FStepIn rF.heap.erase m m' ∧ m.RevivesOwned m'

/-- The run from `m` agrees with the run from `m.noFp` up to the record: a result of one is a
result of the other with the same value and the same memory up to the record. -/
theorem run_noFp_ok {α : Type} {x : MemM α} {m m' : Mem} {v : α}
    (h : (x.run m).run.map (Except.map fun p => (p.1, p.2.noFp)) =
      ((x.run m.noFp).run).map (Except.map fun p => (p.1, p.2.noFp)))
    (e : x.run m = pure (v, m')) : ∃ m₀, x.run m.noFp = pure (v, m₀) ∧ m₀.noFp = m'.noFp := by
  have e' : (x.run m).run = some (.ok (v, m')) := e
  rw [e'] at h
  match e3 : (x.run m.noFp).run, h with
  | none, h => simp at h
  | some (.error _), h => simp [Except.map] at h
  | some (.ok (w, m₀)), h =>
    simp only [Option.map_some, Except.map, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    exact ⟨m₀, e3, h.symm⟩

/-- The converse of `run_noFp_ok`. -/
theorem run_noFp_ok' {α : Type} {x : MemM α} {m m₀ : Mem} {v : α}
    (h : (x.run m).run.map (Except.map fun p => (p.1, p.2.noFp)) =
      ((x.run m.noFp).run).map (Except.map fun p => (p.1, p.2.noFp)))
    (e : x.run m.noFp = pure (v, m₀)) : ∃ m', x.run m = pure (v, m') ∧ m₀.noFp = m'.noFp := by
  have e' : (x.run m.noFp).run = some (.ok (v, m₀)) := e
  rw [e'] at h
  cases e3 : (x.run m).run with
  | none => rw [e3] at h; simp at h
  | some y =>
    cases y with
    | error _ => rw [e3] at h; simp [Except.map] at h
    | ok p =>
      obtain ⟨w, m'⟩ := p
      rw [e3] at h
      simp only [Option.map_some, Except.map, Option.some.injEq, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨m', e3, h.symm⟩

theorem _root_.Zig.Mem.FConc.of_noFp {m m' : Mem} (h : m.FConc) (e : m.noFp = m'.noFp) :
    m'.FConc := by
  have : m'.noFp.FConc := e ▸ (h : m.noFp.FConc)
  exact this

theorem Holds.of_noFp_eq {m m' : Mem} {r rF : Res} (hh : Holds m r rF) (e : m.noFp = m'.noFp) :
    Holds m' r rF := Holds.ofNoFp (e ▸ hh.toNoFp)

namespace ThreadLocal

variable {α : Type} {P P' R : FAssn} {c : MemM α}

theorem pre (hl : ThreadLocal P c) (hp : ∀ r, P' r → P r) : ThreadLocal P' c :=
  fun m r rF hh h hc ho => hl m r rF hh (hp r h) hc ho

/-- **Locality frames**: a frame of the thread's own is a part of the step's frame. -/
theorem frame (hl : ThreadLocal P c) : ThreadLocal (P ⋆ R) c := by
  intro m r rF hh hpr hc ho
  obtain ⟨rP, rR, hd, rfl, hp, -⟩ := hpr
  have ho2 : m.Owns m.current (rP.heap.erase ∪ rR.heap.erase) := by simpa using ho
  obtain ⟨h1, h2⟩ := hl m rP _ (Holds.split hd hh) hp hc (Mem.OwnsC.left ho2)
  refine ⟨h1, fun v m₀ e => ?_⟩
  obtain ⟨hst, hrev⟩ := h2 v m₀ e
  refine ⟨hst.weaken fun l hl => ?_, hrev⟩
  simp only [FHeap.erase_union, Heap.union_apply]; cases e : rR.heap.erase l <;> simp_all

theorem frameL (hl : ThreadLocal P c) : ThreadLocal (R ⋆ P) c :=
  hl.frame.pre fun _ h => sep_comm h

theorem ex {γ : Type} {P : γ → FAssn} (h : ∀ x, ThreadLocal (P x) c) :
    ThreadLocal (FAssn.ex P) c :=
  fun m r rF hh ⟨x, hp⟩ hc ho => h x m r rF hh hp hc ho

theorem lift {φ : Prop} (h : φ → ThreadLocal P c) : ThreadLocal (⟪φ⟫ ⋆ P) c := by
  intro m r rF hh hp hc ho
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact h hφ m r rF hh hp hc ho

end ThreadLocal

namespace FTTriple

variable {α : Type} {P : FAssn} {Q : α → FAssn} {c : MemM α}

/-- **The kernel** (module doc): a sequential triple of a local step is a thread triple. -/
theorem ofSeq (ht : FTriple P c Q) (hl : ThreadLocal P c) : FTTriple P c Q := by
  intro m r rF hh hp hc ho
  obtain ⟨hrun, hloc⟩ := hl m r rF hh hp hc ho
  have hs := ht m.noFp r rF hh.toNoFp hp hc.noFp
  match e : (c.run m).run with
  | none => trivial
  | some (.error err) =>
    rw [e] at hrun
    match e₀ : (c.run m.noFp).run, hrun with
    | none, h => simp at h
    | some (.ok _), h => simp [Except.map] at h
    | some (.error err₀), h =>
      simp only [Option.map_some, Except.map, Option.some.injEq, Except.error.injEq] at h
      subst h; rw [e₀] at hs; exact hs
  | some (.ok (v, m')) =>
    obtain ⟨m₀, e₀, hm⟩ := run_noFp_ok hrun e
    have e₀' : (c.run m.noFp).run = some (.ok (v, m₀)) := e₀
    rw [e₀'] at hs
    obtain ⟨r', hh', hq, hs'⟩ := hs
    obtain ⟨hst, hrev⟩ := hloc v m' e
    have hh'' := hh'.of_noFp_eq hm
    exact ⟨r', hh'', hq, hs'.fconc.of_noFp hm, owns_step hh ho hst hrev hh'', hst⟩

end FTTriple

namespace FTTReturns

/-- A sequential step that returns, local to the thread, returns in the thread. -/
theorem ofSeq {α : Type} {P : FAssn} {c : MemM α} (hr : FReturns P c) (hl : ThreadLocal P c) :
    FTTReturns P c := by
  intro m r rF hh hp hc ho
  obtain ⟨hrun, -⟩ := hl m r rF hh hp hc ho
  obtain ⟨v, m₀, e⟩ := hr m.noFp r rF hh.toNoFp hp hc.noFp
  obtain ⟨m', e', -⟩ := run_noFp_ok' hrun e
  exact ⟨v, m', e'⟩

end FTTReturns

namespace FTTotalTriple

variable {α : Type} {P : FAssn} {Q : α → FAssn} {c : MemM α}

/-- **The kernel, total** (module doc). -/
theorem ofSeq (ht : FTotalTriple P c Q) (hl : ThreadLocal P c) : FTTotalTriple P c Q :=
  ⟨FTTriple.ofSeq ht.1 hl, FTTReturns.ofSeq ht.2 hl⟩

/-- A step that returns `v` and leaves the memory as it is. -/
theorem of_read {v : α}
    (h : ∀ m r rF, Holds m r rF → P r → m.FConc → c.run m = pure (v, m)) :
    FTTotalTriple P c (fun x => ⟪x = v⟫ ⋆ P) := by
  refine ⟨fun m r rF hh hp hc ho => ?_, fun m r rF hh hp hc _ => ⟨v, m, h m r rF hh hp hc⟩⟩
  have e : (c.run m).run = some (.ok (v, m)) := h m r rF hh hp hc
  rw [e]
  exact ⟨r, hh, sep_lift.mpr ⟨rfl, hp⟩, hc, ho, FStepIn.refl m _⟩

end FTTotalTriple

/-! ## Runs with a record in front

`RunFp F m₀ c`: the run of `c` from `m₀` with the record `F` in front is its run from `m₀`, with
`F` in front of the final memory. It composes (`RunFp.bind`); a recorded access that does not
race (`RunFp.recordAccess`) and a step that reads only the blocks (`RunFp.getLift`) have it. -/

/-- The run of `c` from `m₀.withFp F` is its run from `m₀` with `F` in front. -/
def RunFp {α : Type} (F : Array FootprintEntry) (m₀ : Mem) (c : MemM α) : Prop :=
  (c.run (m₀.withFp F)).run = ((c.run m₀).run).map (Except.map fun p => (p.1, p.2.withFp F))

namespace RunFp

variable {α β : Type} {F : Array FootprintEntry} {m₀ : Mem}

theorem pure (v : α) : RunFp F m₀ (pure v : MemM α) := rfl

theorem bind {c : MemM α} {f : α → MemM β} (hc : RunFp F m₀ c)
    (hf : ∀ v m₁, c.run m₀ = Pure.pure (v, m₁) → RunFp F m₁ (f v)) : RunFp F m₀ (c >>= f) := by
  unfold RunFp at *
  rw [StateT.run_bind, ExceptT.run_bind, hc, StateT.run_bind, ExceptT.run_bind]
  match e : (c.run m₀).run with
  | none => rfl
  | some (.error _) => rfl
  | some (.ok (v, m₁)) =>
    simp only [Option.map_some, Except.map]
    exact hf v m₁ e

/-- A `Result` step. -/
theorem lift (g : Result α) : RunFp F m₀ (StateT.lift g : MemM α) := by
  unfold RunFp
  simp only [StateT.run_lift]
  rw [ExceptT.run_bind, ExceptT.run_bind]
  cases g.run with
  | none => rfl
  | some x => cases x <;> rfl

/-- A step that reads the memory where the record does not matter (`he`: the continuation is the
same for the memory with the record in front, as one that reads only the blocks). -/
theorem get_bind {f : Mem → MemM α} (he : f (m₀.withFp F) = f m₀) (hf : RunFp F m₀ (f m₀)) :
    RunFp F m₀ (get >>= f) := by
  unfold RunFp at *
  simp only [StateT.run_bind, StateT.run_get, pure_bind, he]
  exact hf

/-- A change of the memory that keeps the record in front (`hg`, as a change of the blocks). -/
theorem modify {g : Mem → Mem} (hg : g (m₀.withFp F) = (g m₀).withFp F) :
    RunFp F m₀ (do let m ← get; set (g m) : MemM PUnit) := by
  unfold RunFp
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_set, hg]
  rfl

theorem _root_.Zig.Mem.recordAt_withFp (m₀ : Mem) (F : Array FootprintEntry) (b o n : Nat)
    (k : AccessKind) : (m₀.withFp F).recordAt b o n k = (m₀.recordAt b o n k).withFp F := by
  simp only [Mem.recordAt, Mem.withFp]
  rw [Array.push_eq_append, Array.push_eq_append, Array.append_assoc]

/-- A recorded access that races in neither memory. -/
theorem recordAccess {b o n : Nat} {k : AccessKind} (h₀ : NoRace m₀ b o n k)
    (h : NoRace (m₀.withFp F) b o n k) : RunFp F m₀ (Zig.recordAccess b o n k) := by
  unfold RunFp
  rw [recordAccess_run h, recordAccess_run h₀]
  exact congrArg (fun x => some (Except.ok ((), x))) (Mem.recordAt_withFp m₀ F b o n k)

/-- `recordAccessIn` (nothing for a read of a `const` global), when the access races in neither
memory. -/
theorem recordAccessIn {b o n : Nat} {blk : Block} {k : AccessKind} (h₀ : NoRace m₀ b o n k)
    (h : NoRace (m₀.withFp F) b o n k) : RunFp F m₀ (Zig.recordAccessIn b blk o n k) := by
  unfold Zig.recordAccessIn
  split
  · split
    · rfl
    · exact pure _
  · exact recordAccess h₀ h

variable {p : Ptr} {n a : Nat} {k : AccessKind}

/-- `loadBytes`, when its access races in neither memory. -/
theorem loadBytes
    (hnr : ∀ b blk o, m₀.access p n a = Pure.pure (b, blk, o) →
      NoRace m₀ b o n k ∧ NoRace (m₀.withFp F) b o n k) :
    RunFp F m₀ (Zig.loadBytes p n a k) := by
  unfold Zig.loadBytes
  refine get_bind rfl (bind (lift _) fun x m₁ h => ?_)
  obtain ⟨b, blk, o⟩ := x
  obtain ⟨ha, rfl⟩ := Proto.MemM.lift_ok h
  obtain ⟨h1, h2⟩ := hnr b blk o (Proto.access_pure ha)
  exact bind (recordAccessIn h1 h2) fun _ _ _ => pure _

/-- `storeBytes`, when its access races in neither memory. -/
theorem storeBytes {bs : Array Byte}
    (hnr : ∀ b blk o, m₀.access p bs.size a = Pure.pure (b, blk, o) →
      NoRace m₀ b o bs.size k ∧ NoRace (m₀.withFp F) b o bs.size k) :
    RunFp F m₀ (Zig.storeBytes p a bs k) := by
  unfold Zig.storeBytes
  refine get_bind rfl (bind (lift _) fun x m₁ h => ?_)
  obtain ⟨b, blk, o⟩ := x
  obtain ⟨ha, rfl⟩ := Proto.MemM.lift_ok h
  obtain ⟨h1, h2⟩ := hnr b blk o (Proto.accessW_pure ha).1
  exact bind (recordAccess h1 h2) fun _ _ _ => modify rfl

/-- `load`, when its access races in neither memory. -/
theorem load {T : Type} [Enc T]
    (hnr : ∀ b blk o, m₀.access p (Enc.size T) a = Pure.pure (b, blk, o) →
      NoRace m₀ b o (Enc.size T) .read ∧ NoRace (m₀.withFp F) b o (Enc.size T) .read) :
    RunFp F m₀ (Zig.load T a p) := by
  unfold Zig.load
  exact bind (loadBytes hnr) fun _ _ _ => get_bind rfl (lift _)

/-- `alloc` reads no record. -/
theorem alloc (kind : BlockKind) (size align : Nat) : RunFp F m₀ (Zig.alloc kind size align) := by
  unfold RunFp
  cases hroom : m₀.allocOk kind size align
  · rw [alloc_run_noRoom _ (by exact hroom), alloc_run_noRoom _ hroom]; rfl
  · rw [alloc_run_eq _ (by exact hroom), alloc_run_eq _ hroom]; rfl

/-- `free`, when the end of the block races in neither memory or in both. -/
theorem free {b : BlockId} (hpb : p.block = some b)
    (hfr : ∀ blk, m₀.blocks[b]? = some blk →
      (m₀.withFp F).freeRaces b blk.bytes.size = m₀.freeRaces b blk.bytes.size) :
    RunFp F m₀ (Zig.free p) := by
  unfold RunFp Zig.free
  have e1 : (m₀.withFp F).blocks = m₀.blocks := rfl
  simp only [StateT.run_bind, StateT.run_get, pure_bind, hpb, e1]
  cases hb : m₀.blocks[b]? with
  | none => rfl
  | some blk =>
    simp only
    split
    · rw [hfr blk hb]
      split
      · rfl
      · rfl
    · rfl

theorem throw (e : Error) : RunFp F m₀ (MonadExcept.throw e : MemM α) := rfl

/-- `modify` by a change that keeps the record in front. -/
theorem modify' {g : Mem → Mem} (hg : g (m₀.withFp F) = (g m₀).withFp F) :
    RunFp F m₀ (_root_.modify g : MemM PUnit) := by
  unfold RunFp
  simp [_root_.modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run, hg]
  rfl

/-- A read of the memory, a change of it that keeps the record in front, then a step that reads
the old memory only where the record does not matter. -/
theorem get_set_bind {g : Mem → Mem} {k : Mem → MemM α}
    (hg : g (m₀.withFp F) = (g m₀).withFp F) (hk : k (m₀.withFp F) = k m₀)
    (hr : RunFp F (g m₀) (k m₀)) :
    RunFp F m₀ (get >>= fun m => set (g m) >>= fun _ => k m) := by
  unfold RunFp at *
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_set, hg, hk]
  exact hr

/-- The run part of `ThreadLocal`: the run from `m` is the run from `m.noFp` with `m`'s record in
front. -/
theorem noFp {m : Mem} {c : MemM α} (h : RunFp m.footprint m.noFp c) :
    (c.run m).run = ((c.run m.noFp).run).map (Except.map fun p => (p.1, p.2.withFp m.footprint)) := by
  unfold RunFp at h
  rwa [Mem.noFp_withFp] at h

end RunFp

theorem _root_.Zig.Mem.withFp_noFp (m : Mem) (F : Array FootprintEntry) : (m.withFp F).noFp = m.noFp := by
  cases m; rfl

theorem _root_.Zig.Result.pure_inj {β : Type} {x y : β} (h : (Pure.pure x : Result β) = Pure.pure y) :
    x = y := by
  have := congrArg ExceptT.run h
  simpa [Pure.pure, ExceptT.pure, ExceptT.mk, ExceptT.run] using this

theorem RunFp.of_noFp {α : Type} {m : Mem} {c : MemM α}
    (h : (c.run m).run = ((c.run m.noFp).run).map (Except.map fun p => (p.1, p.2.withFp m.footprint))) :
    RunFp m.footprint m.noFp c := by
  unfold RunFp; rwa [Mem.noFp_withFp]

/-- A result of a run that is the run from `m.noFp` with `F` in front is one from `m.noFp`. -/
theorem run_withFp_ok {α : Type} {x : MemM α} {m m₂ : Mem} {w : α} {F : Array FootprintEntry}
    (h : (x.run m).run = ((x.run m.noFp).run).map (Except.map fun p => (p.1, p.2.withFp F)))
    (e : x.run m = pure (w, m₂)) : ∃ m₃, x.run m.noFp = pure (w, m₃) ∧ m₂ = m₃.withFp F := by
  have e' : (x.run m).run = some (.ok (w, m₂)) := e
  rw [e'] at h
  match e3 : (x.run m.noFp).run, h with
  | none, h => simp at h
  | some (.error _), h => simp [Except.map] at h
  | some (.ok (w', m₃)), h =>
    simp only [Option.map_some, Except.map, Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨m₃, e3, rfl⟩

/-- **A step local in the record's sense**: its run from `m` is its run from `m.noFp` with `m`'s
record in front (`RunFp`), and a result of the run from `m.noFp` is a step outside the frame that
makes no byte of an old block alive. The memory primitives are local this way. -/
theorem ThreadLocal.intro {α : Type} {P : FAssn} {c : MemM α}
    (h : ∀ m r rF, Holds m r rF → P r → m.FConc → m.Owns m.current r.heap.erase →
      RunFp m.footprint m.noFp c ∧
      ∀ v m₀, c.run m.noFp = pure (v, m₀) → FStepIn rF.heap.erase m.noFp m₀ ∧ m.NoRevive m₀) :
    ThreadLocal P c := by
  intro m r rF hh hp hc ho
  obtain ⟨hr, hl⟩ := h m r rF hh hp hc ho
  have hrun := hr.noFp
  refine ⟨?_, fun v m' e => ?_⟩
  · rw [hrun, Option.map_map]
    congr 1; funext x
    cases x <;> simp [Except.map, Mem.withFp_noFp]
  · obtain ⟨m₀, e₀, rfl⟩ := run_withFp_ok hrun e
    obtain ⟨hst, hrev⟩ := hl v m₀ e₀
    exact ⟨hst.withFp, fun b x hb h' hn => absurd hn (hrev b x hb h')⟩

/-! ## New and ended blocks -/

theorem _root_.Zig.StepIn.afterAlloc (m : Mem) (hF : Heap) (kind : BlockKind) (size align : Nat) :
    StepIn hF m (m.afterAlloc kind size align) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, VClock.le_refl _,
    by simp [Mem.afterAlloc], fun _ he => .inl he, fun _ he => .inl he⟩

/-- A new block at the end leaves the old ones as they are. -/
theorem _root_.Zig.FStepIn.afterAlloc (m : Mem) (hF : Heap) (kind : BlockKind) (size align : Nat) :
    FStepIn hF m (m.afterAlloc kind size align) :=
  .of_stepIn (StepIn.afterAlloc m hF kind size align)
    (fun b hb ⟨blk, h1, h2⟩ => ⟨blk, by
      rw [Mem.afterAlloc, Array.getElem?_push_lt hb] at h1; rwa [Array.getElem?_eq_getElem hb], h2⟩)
    (fun _ he hn => absurd he hn)
    (Mem.MsgCov.keepFp (fun _ hl _ => hl) (fun _ _ _ hin => hin.push _ rfl) fun _ he => he)

theorem _root_.Zig.Mem.NoRevive.afterAlloc (m : Mem) (kind : BlockKind) (size align : Nat) :
    m.NoRevive (m.afterAlloc kind size align) := fun b x hb h => by
  have e0 : (m.afterAlloc kind size align).blocks[b]? = m.blocks[b]? := by
    rw [Array.getElem?_eq_getElem hb]; exact Array.getElem?_push_lt hb
  have e : (m.afterAlloc kind size align).heap (b, x) = m.heap (b, x) := by
    dsimp only [Mem.heap]; rw [e0]
  rwa [e] at h

/-- The memory after `free` of block `b`. -/
theorem _root_.Zig.FStepIn.kill {m : Mem} {hF : Heap} {b : BlockId} {blk : Block}
    (hb : m.blocks[b]? = some blk) :
    FStepIn hF m { m with blocks := m.blocks.set! b { blk with live := false } } :=
  FStepIn.setBlock (fun h => ⟨blk, hb, h⟩) fun l _ e _ ⟨blk', h1, h2⟩ => by
    rw [e, hb] at h1; cases h1; exact h2

theorem _root_.Zig.Mem.NoRevive.kill (m : Mem) (b : BlockId) (blk : Block) :
    m.NoRevive { m with blocks := m.blocks.set! b { blk with live := false } } :=
  fun b' x hb' h => by
    by_cases hb : b' = b
    · subst hb
      exfalso; apply h
      have e0 : ({ m with blocks := m.blocks.set! b' { blk with live := false } } : Mem).blocks[b']? =
          some { blk with live := false } := by
        rw [Array.set!_eq_setIfInBounds]; exact Array.getElem?_setIfInBounds_self_of_lt hb'
      dsimp only [Mem.heap]; rw [e0]; simp
    · have e : ({ m with blocks := m.blocks.set! b { blk with live := false } } : Mem).heap (b', x) =
          m.heap (b', x) := by
        unfold Mem.heap
        simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
        simp [Ne.symm hb]
      rwa [e] at h

/-- Block `b` becomes `nb`, live at no offset where it was not (no more liveness, no more bytes,
a live start no lower). -/
theorem _root_.Zig.Mem.NoRevive.setBlock {m m' : Mem} {b : BlockId} {blk nb : Block}
    (hb : m.blocks[b]? = some blk) (hbs : m'.blocks = m.blocks.set! b nb)
    (hlive : nb.live = true → blk.live = true) (hsz : nb.bytes.size ≤ blk.bytes.size)
    (hlo : blk.kind.mappedLo ≤ nb.kind.mappedLo) : m.NoRevive m' := fun b' x hb' h => by
  have hget : ∀ j, m'.blocks[j]? = if j = b then some nb else m.blocks[j]? := fun j => by
    rw [hbs, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases e : b = j
    · subst e; simp [Array.getElem?_eq_some_iff.mp hb |>.1]
    · simp [e, Ne.symm e]
  by_cases e : b' = b
  · subst e
    have e0 : m'.blocks[b']? = some nb := by rw [hget]; simp
    rw [Mem.heap_of e0] at h
    rw [Mem.heap_of hb]
    split at h
    · rename_i hc
      rw [dif_pos ⟨hlive hc.1, by omega, by omega⟩]; simp
    · exact absurd rfl h
  · have e1 : m'.heap (b', x) = m.heap (b', x) := by
      unfold Mem.heap; dsimp only; rw [hget, if_neg e]
    rwa [e1] at h

/-- A new block at the end. -/
theorem _root_.Zig.Mem.NoRevive.push {m m' : Mem} {x : Block} (hbs : m'.blocks = m.blocks.push x) :
    m.NoRevive m' := fun b o hb h => by
  have e : m'.heap (b, o) = m.heap (b, o) := by
    have e0 : m'.blocks[b]? = m.blocks[b]? := by
      rw [hbs, Array.getElem?_push_lt hb, Array.getElem?_eq_getElem hb]
    unfold Mem.heap; dsimp only; rw [e0]
  rwa [e] at h

namespace ThreadLocal

variable {P : FAssn}

/-- **`alloc` is local** for every precondition: it reads no record and touches no byte. -/
theorem alloc (kind : BlockKind) (size align : Nat) : ThreadLocal P (Zig.alloc kind size align) := by
  refine intro fun m r rF hh hp hc ho => ⟨?_, fun v m₀ e => ?_⟩
  · exact RunFp.alloc kind size align
  · obtain ⟨-, rfl⟩ := Proto.alloc_ok (m := m.noFp) e
    exact ⟨FStepIn.afterAlloc _ _ _ _ _, Mem.NoRevive.afterAlloc _ _ _ _⟩

/-- **`free` of a block that `P` owns whole** is local: no access to it races with its end. -/
theorem free {p : Ptr} {b : BlockId} (hpb : p.block = some b)
    (hown : ∀ m r rF, Holds m r rF → P r → ∀ blk, m.blocks[b]? = some blk →
      ∀ x, x < blk.bytes.size → r.heap.erase (b, x) ≠ none) :
    ThreadLocal P (Zig.free p) := by
  refine intro fun m r rF hh hp hc ho => ⟨?_, fun v m₀ e => ?_⟩
  · refine RunFp.free hpb fun blk hb => ?_
    rw [Mem.noFp_withFp, freeRaces_of_singleThread hc.noFp.1.single]
    refine freeRaces_of_clock fun e he heb hl hoff => ho e he (.inl ⟨e.off, Nat.le_refl _, by omega, ?_⟩)
    rw [heb]; exact hown m r rF hh hp blk hb e.off hoff
  · obtain ⟨b', blk, -, hb, rfl⟩ := Proto.free_ok (m := m.noFp) e
    exact ⟨FStepIn.kill hb, Mem.NoRevive.kill _ _ _⟩

end ThreadLocal

/-! ## Owned accesses -/

/-- An access at `p` that succeeds is at `p`'s block and offset, in a block of the memory. -/
theorem access_at {m : Mem} {p : Ptr} {n a : Nat} {b : BlockId} {blk : Block} {o : Nat}
    (h : m.access p n a = pure (b, blk, o)) :
    p.block = some b ∧ o = p.off.toNat ∧ m.blocks[b]? = some blk ∧ b < m.blocks.size := by
  obtain ⟨hpb, hblk, -, -, -, -, rfl⟩ := access_eq h
  exact ⟨hpb, rfl, hblk, (Array.getElem?_eq_some_iff.mp hblk).1⟩

/-- The bytes `[o, o + n)` of block `b` are bytes of every resource of `P`. -/
def OwnsAt (P : FAssn) (b : BlockId) (o n : Nat) : Prop :=
  ∀ r, P r → ∀ x, o ≤ x → x < o + n → r.heap.erase (b, x) ≠ none

/-- The `n` bytes at `p` are bytes of every resource of `P` (`OwnsAt` at `p`'s block, if any). -/
def OwnsPtr (P : FAssn) (p : Ptr) (n : Nat) : Prop :=
  ∀ b, p.block = some b → OwnsAt P b p.off.toNat n

/-- The bytes of `bytesAt` at `p` are in its heap. -/
theorem bytesAt_has {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} {h : Heap}
    {b : BlockId} (hb : Zig.bytesAt p A S K bs h) (hpb : p.block = some b) :
    ∀ x, p.off.toNat ≤ x → x < p.off.toNat + bs.size → h (b, x) ≠ none := by
  obtain ⟨b', hb', -, hl⟩ := hb
  rw [hpb] at hb'; cases hb'
  intro x hx hx'
  rw [hl (b, x), if_pos ⟨rfl, hx, hx'⟩]; simp

namespace OwnsAt

variable {P R : FAssn} {b : BlockId} {o n : Nat}

theorem sepL (h : OwnsAt P b o n) : OwnsAt (P ⋆ R) b o n := by
  rintro _ ⟨r₁, r₂, -, rfl, h1, -⟩ x hx hx'
  have := h r₁ h1 x hx hx'
  simp only [FHeap.erase_union, Heap.union_apply]
  cases e : r₁.heap.erase (b, x) <;> simp_all

theorem sepR (h : OwnsAt P b o n) : OwnsAt (R ⋆ P) b o n := fun r hr =>
  h.sepL r (sep_comm hr)

theorem of_imp {P' : FAssn} (h : OwnsAt P b o n) (hp : ∀ r, P' r → P r) : OwnsAt P' b o n :=
  fun r hr => h r (hp r hr)

/-- The bytes of `bytesAt` at `p`. -/
theorem bytesAt {p : Ptr} {A S : Nat} {K : BlockKind} {bs : Array Byte} (hpb : p.block = some b) :
    OwnsAt (up (Zig.bytesAt p A S K bs)) b p.off.toNat bs.size := by
  rintro r ⟨hb, -, -⟩
  exact bytesAt_has hb hpb

end OwnsAt

namespace OwnsPtr

variable {P R : FAssn} {p : Ptr} {n : Nat}

theorem sepL (h : OwnsPtr P p n) : OwnsPtr (P ⋆ R) p n := fun b hb => (h b hb).sepL

theorem sepR (h : OwnsPtr P p n) : OwnsPtr (R ⋆ P) p n := fun b hb => (h b hb).sepR

theorem of_imp {P' : FAssn} (h : OwnsPtr P p n) (hp : ∀ r, P' r → P r) : OwnsPtr P' p n :=
  fun b hb => (h b hb).of_imp hp

/-- The bytes of `bytesAt` at `p`. -/
theorem bytesAt {A S : Nat} {K : BlockKind} {bs : Array Byte} :
    OwnsPtr (up (Zig.bytesAt p A S K bs)) p bs.size := fun _ hpb => OwnsAt.bytesAt hpb

end OwnsPtr

namespace ThreadLocal

variable {P : FAssn} {p : Ptr} {n a : Nat} {k : AccessKind} {b : BlockId}

/-- The race checks of an owned access pass in `m` (ownership) and in `m.noFp` (one thread). -/
theorem noRace_owned {m : Mem} {r : Res} {o : Nat} (hc : m.FConc)
    (ho : m.Owns m.current r.heap.erase)
    (hin : ∀ x, o ≤ x → x < o + n → r.heap.erase (b, x) ≠ none) :
    NoRace m.noFp b o n k ∧ NoRace (m.noFp.withFp m.footprint) b o n k := by
  refine ⟨noRace_of_singleThread hc.noFp.1.single _ _ _ _, ?_⟩
  rw [Mem.noFp_withFp]; exact ho.noRace hin

/-- **An owned read of bytes** (`loadBytes`) is local. Its access is a read (`hk`): `loadBytes`
checks no `const` global, so a recorded write kind would be a write to one. -/
theorem loadBytes (hown : OwnsPtr P p n) (hk : k.isWrite = false := by decide) :
    ThreadLocal P (Zig.loadBytes p n a k) := by
  refine intro fun m r rF hh hp hc ho => ⟨?_, fun v m₀ e => ?_⟩
  · refine RunFp.loadBytes fun b blk o h => ?_
    obtain ⟨hpb, rfl, -⟩ := access_at h
    exact noRace_owned hc ho (hown b hpb r hp)
  · obtain ⟨b, blk, o, h, -, -, rfl⟩ := Proto.loadBytes_ok (m := m.noFp) e
    obtain ⟨hpb, rfl, -, hb⟩ := access_at h
    exact ⟨FStepIn.readAt hc.1 (FHeap.erase_disjoint hh.disj) (hown b hpb r hp) hb
        (fun hw => absurd hw (by simp [hk])),
      fun _ _ _ h => by rwa [Mem.heap_readAt] at h⟩

/-- **An owned typed load** is local. -/
theorem load {T : Type} [Enc T] (hown : OwnsPtr P p (Enc.size T)) :
    ThreadLocal P (Zig.load T a p) := by
  refine intro fun m r rF hh hp hc ho => ⟨?_, fun v m₀ e => ?_⟩
  · refine RunFp.load (T := T) fun b blk o h => ?_
    obtain ⟨hpb, rfl, -⟩ := access_at h
    exact noRace_owned hc ho (hown b hpb r hp)
  · obtain ⟨b, blk, o, h, -, -, rfl⟩ := Proto.load_ok (m := m.noFp) e
    obtain ⟨hpb, rfl, -, hb⟩ := access_at h
    exact ⟨FStepIn.readAt hc.1 (FHeap.erase_disjoint hh.disj) (hown b hpb r hp) hb
        (fun hw => absurd hw (by decide)),
      fun _ _ _ h => by rwa [Mem.heap_readAt] at h⟩

/-- **An owned write of bytes** (`storeBytes`) is local. -/
theorem storeBytes {bs : Array Byte} (hown : OwnsPtr P p bs.size) :
    ThreadLocal P (Zig.storeBytes p a bs k) := by
  refine intro fun m r rF hh hp hc ho => ⟨?_, fun v m₀ e => ?_⟩
  · refine RunFp.storeBytes fun b blk o h => ?_
    obtain ⟨hpb, rfl, -⟩ := access_at h
    exact noRace_owned hc ho (hown b hpb r hp)
  · obtain ⟨b, blk, o, h, hK, -, rfl⟩ := Proto.storeBytes_ok (m := m.noFp) e
    have hsz := (access_eq h).2.2.2.2.1
    have h0 := (access_eq h).2.2.2.1
    obtain ⟨hpb, ho', hblk, hb⟩ := access_at h
    subst o
    refine ⟨(FStepIn.recordAt (m := m.noFp) hc.1 (FHeap.erase_disjoint hh.disj)
      (hown b hpb r hp) hb fun _ ⟨blk', h1, h2⟩ => ?_).trans
        (FStepIn.write (m := m.noFp.recordAt b p.off.toNat bs.size k) hblk _ _),
      fun b' x _ h => ?_⟩
    · rw [hblk] at h1; cases h1; exact hK h2
    cases e' : ((m.noFp.recordAt b p.off.toNat bs.size k).write b blk p.off.toNat bs).heap (b', x)
      with
    | none => exact absurd e' h
    | some c =>
      obtain ⟨c', hc', -⟩ := Mem.heap_write_cell (m := m.noFp.recordAt b p.off.toNat bs.size k)
        hblk (by omega) e'
      rw [Mem.heap_recordAt] at hc'
      have hc'' : m.heap (b', x) = some c' := hc'
      simp [hc'']

/-- **An owned typed store** is local. -/
theorem store {T : Type} [Enc T] {v : T} (hown : OwnsPtr P p (Enc.encode v).size) :
    ThreadLocal P (Zig.store a p v) :=
  storeBytes hown

end ThreadLocal

/-! ## Composing local steps

`ThreadLocal.bind`: a local step whose successful sequential runs keep `Q`, then a step local for
`Q`. With `pure`, `throw`, `ite` and `readBind` (a read of the blocks, as `Mem.access`), the byte
operations `@memset`, `@memmove` and `@memcpy` are local from the ownership of their bytes. -/

theorem _root_.Zig.Mem.withFp_withFp (m : Mem) (F G : Array FootprintEntry) :
    (m.withFp G).withFp F = m.withFp (F ++ G) := by
  cases m; simp [Mem.withFp, Array.append_assoc]

theorem _root_.Zig.Mem.NoRevive.trans {m m₁ m₂ : Mem} (h₁ : m.NoRevive m₁)
    (hb : m.blocks.size ≤ m₁.blocks.size) (h₂ : m₁.NoRevive m₂) : m.NoRevive m₂ :=
  fun b x hb' h => h₁ b x hb' (h₂ b x (Nat.lt_of_lt_of_le hb' hb) h)

namespace ThreadLocal

variable {α β γ : Type} {P : FAssn}

theorem pure (v : α) : ThreadLocal P (Pure.pure v : MemM α) :=
  intro fun m _ _ _ _ _ _ => ⟨RunFp.pure v, fun w m₀ e => by
    obtain ⟨-, rfl⟩ := Proto.MemM.pure_ok (m := m.noFp) e
    exact ⟨FStepIn.refl _ _, fun _ _ _ h => h⟩⟩

theorem throw (err : Error) : ThreadLocal P (throw err : MemM α) :=
  intro fun m _ _ _ _ _ _ => ⟨RunFp.throw err, fun _ _ e => (Proto.MemM.throw_ok (m := m.noFp) e).elim⟩

theorem ite {c : Prop} [Decidable c] {a b : MemM α} (ha : c → ThreadLocal P a)
    (hb : ¬ c → ThreadLocal P b) : ThreadLocal P (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

/-- **Sequencing**: a local step whose successful sequential runs end in `Q`, then a step local
for `Q`. -/
theorem bind {Q : α → FAssn} {c : MemM α} {f : α → MemM β} (hc : ThreadLocal P c)
    (hq : ∀ m r rF, Holds m r rF → P r → m.FSeq → ∀ v m₁, c.run m = Pure.pure (v, m₁) →
      ∃ r', Holds m₁ r' rF ∧ Q v r' ∧ m₁.FSeq)
    (hf : ∀ v, ThreadLocal (Q v) (f v)) : ThreadLocal P (c >>= f) := by
  intro m r rF hh hp hcm ho
  obtain ⟨hrun, hloc⟩ := hc m r rF hh hp hcm ho
  -- after a result of `c`, `f` is local both there and at the matching sequential result
  have step : ∀ v m₁', c.run m = Pure.pure (v, m₁') → ∃ m₁, c.run m.noFp = Pure.pure (v, m₁) ∧
      ((f v).run m₁').run.map (Except.map fun p => (p.1, p.2.noFp)) =
        ((f v).run m₁).run.map (Except.map fun p => (p.1, p.2.noFp)) ∧
      ∀ w m₂', (f v).run m₁' = Pure.pure (w, m₂') →
        FStepIn rF.heap.erase m₁' m₂' ∧ m₁'.RevivesOwned m₂' := by
    intro v m₁' e
    obtain ⟨m₁, e₁, hm⟩ := run_noFp_ok hrun e
    obtain ⟨r₀, hh₀, hq₀, hs₀⟩ := hq m.noFp r rF hh.toNoFp hp hcm.noFp v m₁ e₁
    obtain ⟨hst, hrev⟩ := hloc v m₁' e
    have hh₀' := hh₀.of_noFp_eq hm
    obtain ⟨h1, h1'⟩ := hf v m₁' r₀ rF hh₀' hq₀ (hs₀.fconc.of_noFp hm) (owns_step hh ho hst hrev hh₀')
    obtain ⟨h0, -⟩ := hf v m₁ r₀ rF hh₀ hq₀ hs₀.fconc (hs₀.1.single.owns _)
    exact ⟨m₁, e₁, by rw [h1, h0, hm], h1'⟩
  refine ⟨?_, fun w m₂' e => ?_⟩
  · rw [StateT.run_bind, ExceptT.run_bind, StateT.run_bind, ExceptT.run_bind]
    have hr := hrun
    cases hx : (c.run m).run with
    | none =>
      rw [hx] at hr
      cases hx0 : (c.run m.noFp).run with
      | none => rfl
      | some y => rw [hx0] at hr; simp at hr
    | some x =>
      cases x with
      | error err =>
        rw [hx] at hr
        cases hx0 : (c.run m.noFp).run with
        | none => rw [hx0] at hr; simp at hr
        | some y =>
          cases y with
          | error err' =>
            rw [hx0] at hr
            simp only [Option.map_some, Except.map, Option.some.injEq, Except.error.injEq] at hr
            subst hr; rfl
          | ok p => rw [hx0] at hr; simp [Except.map] at hr
      | ok p =>
        obtain ⟨v, m₁'⟩ := p
        obtain ⟨m₁, e₁, hfeq, -⟩ := step v m₁' hx
        have e₁' : (c.run m.noFp).run = some (.ok (v, m₁)) := e₁
        rw [e₁']
        exact hfeq
  · obtain ⟨v, m₁', e1, e2⟩ := Proto.MemM.bind_ok e
    obtain ⟨hst, hrev⟩ := hloc v m₁' e1
    obtain ⟨m₁, -, -, h2⟩ := step v m₁' e1
    obtain ⟨hst2, hrev2⟩ := h2 w m₂' e2
    exact ⟨hst.trans hst2, hrev.trans hst hrev2 hst2⟩

/-- **A read of the blocks**, then a local step. -/
theorem readBind {g : Mem → Result γ} {f : γ → MemM α} (hg : ∀ m F, g (m.withFp F) = g m)
    (hf : ∀ v, ThreadLocal P (f v)) :
    ThreadLocal P (get >>= fun m => StateT.lift (g m) >>= f) := by
  have e : (get >>= fun m => StateT.lift (g m) >>= f : MemM α) =
      ((get >>= fun m => StateT.lift (g m)) >>= f) := by simp only [bind_assoc]
  rw [e]
  refine bind (Q := fun _ => P) (intro fun m r rF hh hp hc ho => ⟨RunFp.get_bind (by simp only [hg])
    (RunFp.lift _), fun v m₀ e => ?_⟩) (fun m r rF hh hp hs v m₁ e => ?_) hf
  · obtain ⟨m', m₁, hg', e1⟩ := Proto.MemM.bind_ok e
    obtain ⟨rfl, rfl⟩ := Proto.MemM.get_ok hg'
    obtain ⟨-, rfl⟩ := Proto.MemM.lift_ok e1
    exact ⟨FStepIn.refl _ _, Mem.NoRevive.refl _⟩
  · obtain ⟨m', m₂, hg', e1⟩ := Proto.MemM.bind_ok e
    obtain ⟨rfl, rfl⟩ := Proto.MemM.get_ok hg'
    obtain ⟨-, rfl⟩ := Proto.MemM.lift_ok e1
    exact ⟨r, hh, hp, hs⟩

/-- The memory after a read (`Mem.readAt`: recorded, or nothing for a `const` global) holds what
the memory held. -/
theorem _root_.Zig.Full.Holds.readAt {m : Mem} {r rF : Res} (hh : Holds m r rF) (blk : Block)
    (b : BlockId) (o n : Nat) (kd : AccessKind) : Holds (m.readAt blk b o n kd) r rF :=
  Mem.readAt_cases (P := fun x => Holds x r rF) hh
    ⟨hh.disj, hh.heap, hh.know, hh.knowF, hh.ghost.of_blocks rfl rfl rfl rfl⟩

theorem _root_.Zig.Mem.FSeq.readAt {m : Mem} (hs : m.FSeq) (blk : Block) (b : BlockId)
    (o n : Nat) (kd : AccessKind) : (m.readAt blk b o n kd).FSeq :=
  Mem.readAt_cases (P := Mem.FSeq) hs ⟨hs.1.recordAt _ _ _ _, hs.2.1, hs.2.2⟩

/-- A successful read of `n` bytes keeps the resources and the memory invariant; it reads `n`
bytes. -/
theorem loadBytes_post {p : Ptr} {n a : Nat} {k : AccessKind} :
    ∀ m r rF, Holds m r rF → P r → m.FSeq → ∀ v m₁,
      (Zig.loadBytes p n a k).run m = Pure.pure (v, m₁) →
        ∃ r', Holds m₁ r' rF ∧ (⟪v.size = n⟫ ⋆ P) r' ∧ m₁.FSeq := by
  intro m r rF hh hp hs v m₁ e
  obtain ⟨b, blk, o, ha, -, rfl, rfl⟩ := Proto.loadBytes_ok e
  obtain ⟨-, -, -, h0, hsz, -, rfl⟩ := access_eq ha
  refine ⟨r, hh.readAt _ _ _ _ _, sep_lift.mpr ⟨?_, hp⟩, hs.readAt _ _ _ _ _⟩
  simp only [Array.size_extract]; omega

/-- **`@memmove`** of `n` items of `size` bytes between owned bytes. -/
theorem memmove {size da sa : Nat} {d s : Ptr} {n : BitVec 64}
    (hd : OwnsPtr P d (n.toNat * size)) (hs : OwnsPtr P s (n.toNat * size)) :
    ThreadLocal P (Zig.memmove size da sa d s n) := by
  unfold Zig.memmove
  refine ite (fun _ => pure _) fun _ => readBind (fun _ _ => rfl) fun _ =>
    bind (loadBytes hs) loadBytes_post fun bs => lift fun hbs => storeBytes (by rw [hbs]; exact hd)

/-- **`@memcpy`** of `n` items of `size` bytes between owned bytes. -/
theorem memcpy {size da sa : Nat} {d s : Ptr} {n n' : BitVec 64}
    (hd : OwnsPtr P d (n.toNat * size)) (hs : OwnsPtr P s (n.toNat * size)) :
    ThreadLocal P (Zig.memcpy size da sa d s n n') := by
  unfold Zig.memcpy
  exact ite (fun _ => throw _) fun _ => memmove hd hs

/-- **`@memset`** of `n` items over owned bytes. -/
theorem memset {δ : Type} [Enc δ] {al : Nat} {p : Ptr} {n : BitVec 64} {v : Option δ}
    (hv : ∀ x, v = some x → (Enc.encode x).size = Enc.size δ)
    (hown : OwnsPtr P p (n.toNat * Enc.size δ)) : ThreadLocal P (Zig.memset al p n v) := by
  unfold Zig.memset
  refine ite (fun _ => pure _) fun _ => readBind (fun _ _ => rfl) fun _ => ?_
  cases v with
  | none =>
    exact storeBytes (by simpa [Array.size_flatten_replicate] using hown)
  | some x =>
    exact storeBytes (by simpa [Array.size_flatten_replicate, hv x rfl] using hown)

end ThreadLocal

/-! ## Owned bytes of byte ranges, regions and arrays -/

namespace OwnsPtr

variable {p : Ptr} {A S : Nat} {K : BlockKind} {a : Nat} {bs : Array Byte}

/-- The bytes `[k, k + n)` of `bytesAt` at `p`, at `p.add k`. -/
theorem bytesAt_add {k n : Nat} (hk : k + n ≤ bs.size) :
    OwnsPtr (up (Zig.bytesAt p A S K bs)) (p.add k) n := by
  intro b hb r hr x hx hx'
  obtain ⟨⟨b', hb', h0, hl⟩, -, -⟩ := hr
  have hpb : p.block = some b := hb
  rw [hpb] at hb'; cases hb'
  have hoff : (p.add k).off.toNat = p.off.toNat + k := by simp [Ptr.add]; omega
  rw [hoff] at hx hx'
  rw [hl (b, x), if_pos ⟨rfl, by omega, by omega⟩]; simp

/-- The bytes of item `i` of an array. -/
theorem arr_elem {T : Type} [Enc T] {vs : List T} {i : BitVec 64} (hi : i.toNat < vs.length) :
    OwnsPtr (up (Zig.arr p vs)) (p.elem (Enc.size T) i) (Enc.size T) := by
  rintro b hb r ⟨⟨_, _, _, bs, -, hsz, -, hbt, -⟩, hk, hg⟩
  rw [Ptr.elem_eq] at hb ⊢
  refine bytesAt_add ?_ b hb r ⟨hbt, hk, hg⟩
  rw [hsz]
  simpa only [Nat.mul_succ] using Nat.mul_le_mul_left (Enc.size T) (Nat.succ_le_of_lt hi)

end OwnsPtr

end Full
end Zig
