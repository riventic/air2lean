import ZigLean.Sep.Full.Extent
import ZigLean.Conc.Base.Heap
import ZigLean.Conc.Clock

/-!
# Thread triples over full-state resources

`FTTriple P c Q` is `FTriple` for a `MemM` step of one thread inside a concurrent run
(`docs/sep-threads.md`): the same resources (`Res`), the same `Holds` and the same assertions, with
ownership by the thread's clock in place of `Mem.Seq`, and the step's race freedom in the post.
It replaces the legacy `TTriple` (`ZigLean/Conc/Own.lean`).

- **Ownership, option R** (`Mem.OwnsRes`, `docs/sep-full-state.md` §Read shares): the thread owns
  the resource's exclusive bytes (cells and whole shares, `Res.excl`: every recorded access before
  its clock, `Mem.Owns`) and reads its partial shares (`Res.shared`: every recorded write before its
  clock, `Mem.OwnsR`), so concurrent readers each own their share. `Mem.OwnsRes.of_owns` gives it
  from ownership of all the bytes (`Res.owned`), as for any share-free resource.
- **Race freedom** (`FStepIn rF.owned m m' (rF.shared.inter r.shared)`): the frame, the other
  threads and the atomic locations over the frame stay; a new access touches no frame byte except
  a read of a partial share of the frame that the resource `r` shares too (`Heap.inter`). A real
  load needs a positive fraction of every byte it reads (`Mem.BytesRead`), and next to a byte the
  resource holds the frame holds at most a partial share (`Holds.frame_shared`), so a load of the
  resource's bytes is local (`ThreadLocal.loadOwned`; the locality provider `ThreadLocal.sload` in
  `Share.lean`). A frame that admitted a read of any of its shares would let a thread that holds no
  share of a byte record a read of it, unordered with the writer who later takes the byte whole
  (maintainer decision 2026-11-09, option (A); `docs/sep-full-state.md` §Read shares).
- Which bytes a resource holds is fixed by the memory and the frame (`Holds.owned_sub`), so an
  update in a thread gains no byte. Gathering partial shares of different owners into a whole share
  fails closed (engine ledger `share-gather`).

- **Memory invariant** (`Mem.FConc`): the current thread exists, the atomic layout is well formed
  and live blocks lie apart (`FSeq` without `Seq`).
- **One logic.** `FTTriple.toFTriple`: a thread triple is a sequential one, since a sequential
  memory is a concurrent one whose current thread owns everything. The updates of the full-state
  library (`EUpd`, `Upd`, `know_intro`) apply in a thread unchanged (`FTTriple.eupd`, `upd`,
  `know_intro`): they are read in the memory without its recorded accesses (`Mem.noFp`), which
  holds the same resources.
- **Ownership and race freedom** come from `ZigLean/Conc/Clock.lean` (`Mem.Owns`, `Mem.OwnsR`, `FStepIn`);
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
theorem _root_.Zig.Mem.SingleThread.fstep {m m' : Mem} {hF hR : Heap} (h : m.SingleThread)
    (hs : FStepIn hF m m' hR) : m'.SingleThread := by
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
  ⟨hh.disj, hh.heap, hh.know, hh.knowF, hh.ghost.of_blocks rfl rfl rfl rfl⟩

theorem ofNoFp (hh : Holds m.noFp r rF) : Holds m r rF :=
  ⟨hh.disj, hh.heap, hh.know, hh.knowF, hh.ghost.of_blocks rfl rfl rfl rfl⟩

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

end Holds

theorem FHeap.erase_fix_ne {m : Mem} {h : FHeap} {l : Loc} :
    (h.fix m).erase l ≠ none ↔ h.erase l ≠ none := by
  simp [FHeap.erase, FHeap.fix]

theorem Res.excl_fix {m : Mem} {r : Res} {l : Loc} : (r.fix m).excl l ≠ none ↔ r.excl l ≠ none := by
  simp only [Res.excl_ne, Res.fix, ne_eq, FHeap.fix_none]

theorem Res.shared_fix {m : Mem} {r : Res} {l : Loc} :
    (r.fix m).shared l ≠ none ↔ r.shared l ≠ none := by
  simp only [Res.shared_ne, Res.fix, FHeap.fix_none]

/-! ## Thread ownership of a resource (option R) -/

/-- **Thread `t` owns the resource `r`** (`docs/sep-full-state.md` §Read shares, option R): every
recorded access to its exclusive bytes (cells, whole shares: `Res.excl`) and every recorded write
to its shared bytes (partial shares: `Res.shared`) happened before `t`'s clock. -/
def _root_.Zig.Mem.OwnsRes (m : Mem) (t : ThreadId) (r : Res) : Prop :=
  m.Owns t r.excl ∧ m.OwnsR t r.shared

section OwnsRes

variable {m m' : Mem} {t : ThreadId} {r r' r₁ r₂ : Res}

/-- Ownership of all of a resource's bytes is thread ownership of it. -/
theorem _root_.Zig.Mem.OwnsRes.of_owns (ho : m.Owns t r.owned) : m.OwnsRes t r :=
  ⟨ho.sub fun _ => Res.owned_of_excl, Mem.Owns.toR (ho.sub fun _ => Res.owned_of_shared)⟩

/-- A thread may read every byte of a resource it owns. -/
theorem _root_.Zig.Mem.OwnsRes.ownsR (ho : m.OwnsRes t r) : m.OwnsR t r.owned :=
  (Mem.OwnsRC.union (Mem.OwnsC.toR ho.1) ho.2).sub fun _ hl hn => by
    simp only [Heap.union_apply, Option.or_eq_none_iff] at hn
    rcases Res.excl_or_shared hl with h | h
    · exact h hn.1
    · exact h hn.2

/-- An access to a byte a resource holds touches its exclusive or its shared bytes
(`Res.excl_or_shared`). -/
theorem _root_.Zig.FootprintEntry.Touches.excl_or_shared {e : FootprintEntry} {r : Res}
    (h : e.Touches r.owned) : e.Touches r.excl ∨ e.Touches r.shared :=
  let ⟨x, h1, h2, h3⟩ := h
  (Res.excl_or_shared h3).imp (fun h => ⟨x, h1, h2, h⟩) (fun h => ⟨x, h1, h2, h⟩)

/-- A thread owns every access to its cells. -/
theorem _root_.Zig.Mem.OwnsRes.cells (ho : m.OwnsRes t r) : m.Owns t r.heap.erase :=
  ho.1.sub fun _ hl => Res.excl_of_heap fun e => hl (by simp [FHeap.erase, e])

theorem _root_.Zig.Mem.OwnsRes.sub (ho : m.OwnsRes t r)
    (hx : ∀ l, r'.excl l ≠ none → r.excl l ≠ none)
    (hs : ∀ l, r'.shared l ≠ none → r.owned l ≠ none) : m.OwnsRes t r' :=
  ⟨ho.1.sub hx, ho.ownsR.sub hs⟩

/-- A thread owns each part of a resource it owns. -/
theorem _root_.Zig.Mem.OwnsRes.sepL (ho : m.OwnsRes t r) (hh : r.heap = r₁.heap ∪ r₂.heap)
    (hg : r.gh = r₁.gh.add r₂.gh) : m.OwnsRes t r₁ :=
  ho.sub (fun _ hl => Res.excl_sep hh hg (.inl hl))
    fun _ hl => (Res.owned_sep hh hg).mpr (.inl (Res.owned_of_shared hl))

theorem _root_.Zig.Mem.OwnsRes.sepR (ho : m.OwnsRes t r) (hh : r.heap = r₁.heap ∪ r₂.heap)
    (hg : r.gh = r₁.gh.add r₂.gh) : m.OwnsRes t r₂ :=
  ho.sub (fun _ hl => Res.excl_sep hh hg (.inr hl))
    fun _ hl => (Res.owned_sep hh hg).mpr (.inr (Res.owned_of_shared hl))

/-- The current thread keeps owning a resource over any of its steps (`Mem.Owns.fstepCur`). -/
theorem _root_.Zig.Mem.OwnsRes.fstepCur {hF hR : Heap} (ho : m.OwnsRes m.current r)
    (hs : FStepIn hF m m' hR) : m'.OwnsRes m'.current r :=
  ⟨ho.1.fstepCur hs, ho.2.fstepCur hs⟩

/-- **An update keeps thread ownership**: next to the same frame in the same memory, every
exclusive byte of the new resource is an exclusive byte of the old one (`Holds.excl_sub'`: a
whole share is exclusive), and every byte of it a byte of the old one (`Holds.owned_sub`). -/
theorem _root_.Zig.Mem.OwnsRes.upd {rF : Res} (ho : m.OwnsRes t r) (hh : Holds m r rF)
    (hh' : Holds m r' rF) : m.OwnsRes t r' :=
  ho.sub (fun _ hl => hh.excl_sub' hh' (hh'.live_of_owned (Res.owned_of_excl hl)).1 hl)
    fun _ hl => hh.owned_sub hh' (Res.owned_of_shared hl)

/-- An exclusive byte of `r₁ ⋆ r₂` that `r₂` does not own at all is exclusive in `r₁`. -/
theorem _root_.Zig.Full.Res.excl_of_sep_none {r₁ r₂ : Res} {l : Loc}
    (h₂ : r₂.owned l = none)
    (hl : Res.excl ⟨r₁.heap ∪ r₂.heap, r₁.know.union r₂.know, r₁.gh.add r₂.gh⟩ l ≠ none) :
    r₁.excl l ≠ none := by
  have h0 : r₂.heap l = none ∧ ¬ (r₂.gh.share l).Pos := by
    have : ¬ r₂.owned l ≠ none := fun h => h h₂
    rw [Res.owned_ne] at this; grind
  refine Res.excl_ne.mpr ?_
  rcases Res.excl_ne.mp hl with e | e
  · left; simpa [FHeap.union_apply, h0.1] using e
  · right
    rw [Ghost.add_share, (SCell.not_pos_iff.mp h0.2).eq, SCell.add_zero] at e
    exact e

/-- **The frame rule's ownership**: after a step of the thread on the part `rP` of `rP ⋆ rR`
that ends with `rP'`, the thread owns `rP' ⋆ rR`. An exclusive byte of the sum is one of `rP'`,
or a byte of `rR`, which the sum held exclusively before (`Holds.excl_sub'`: the frame `rF` is
the same). -/
theorem _root_.Zig.Mem.OwnsRes.frame {hF hR : Heap} {rF rP rP' rR : Res}
    (hh : Holds m ⟨rP.heap ∪ rR.heap, rP.know.union rR.know, rP.gh.add rR.gh⟩ rF)
    (hh' : Holds m' ⟨rP'.heap ∪ rR.heap, rP'.know.union rR.know, rP'.gh.add rR.gh⟩ rF)
    (ho : m.OwnsRes m.current ⟨rP.heap ∪ rR.heap, rP.know.union rR.know, rP.gh.add rR.gh⟩)
    (ho' : m'.OwnsRes m'.current rP') (hs : FStepIn hF m m' hR) :
    m'.OwnsRes m'.current ⟨rP'.heap ∪ rR.heap, rP'.know.union rR.know, rP'.gh.add rR.gh⟩ := by
  have ho₁ := ho.fstepCur hs
  refine ⟨(Mem.OwnsC.union ho'.1 ho₁.1).sub fun l hl hn => ?_,
    (Mem.OwnsRC.union ho'.ownsR ho₁.ownsR).sub fun l hl hn => ?_⟩
  · simp only [Heap.union_apply, Option.or_eq_none_iff] at hn
    by_cases hR' : rR.owned l ≠ none
    · have hl₀ : Res.owned ⟨rP.heap ∪ rR.heap, rP.know.union rR.know, rP.gh.add rR.gh⟩ l ≠ none :=
        (Res.owned_sep rfl rfl).mpr (.inr hR')
      exact (hh.excl_sub' hh' (hh.live_of_owned hl₀).1 hl) hn.2
    · exact Res.excl_of_sep_none (Classical.not_not.mp hR') hl hn.1
  · simp only [Heap.union_apply, Option.or_eq_none_iff] at hn
    rcases (Res.owned_sep rfl rfl).mp (Res.owned_of_shared hl) with e | e
    · exact e hn.1
    · exact ((Res.owned_sep rfl rfl).mpr (.inr e)) hn.2

/-- Thread ownership ignores ghost state without shares. -/
theorem _root_.Zig.Mem.OwnsRes.addGh_iff {h : FHeap} {k : Know} {a g : Ghost}
    (hb : g.share = fun _ => SCell.zero := by rfl) :
    m.OwnsRes t ⟨h, k, a.add g⟩ ↔ m.OwnsRes t ⟨h, k, a⟩ := by
  unfold Mem.OwnsRes; rw [Res.excl_addGh hb, Res.shared_addGh hb]

/-- **Another thread keeps owning** a resource of the frame `rF` of a step in `rF.owned` that
may read `rF.shared`: its exclusive bytes are exclusive in `rF` (`Res.excl_sep`), so no step
touches them; its shared bytes are only read. -/
theorem _root_.Zig.Mem.OwnsRes.fstep {hF hR : Heap} {u : ThreadId} {p : Res}
    (ho : m.OwnsRes u p) (hs : FStepIn hF m m' hR) (hu : u ≠ m.current)
    (hx : ∀ l, p.excl l ≠ none → hF l ≠ none ∧ hR l = none)
    (hsh : ∀ l, p.shared l ≠ none → hF l ≠ none) : m'.OwnsRes u p :=
  ⟨Mem.Owns.fstep hs hu ho.1 (fun l hl => (hx l hl).1) fun l hl => (hx l hl).2,
    Mem.OwnsR.fstep hs hu ho.2 hsh⟩

/-- `OwnsRes.fstep` for a step in the frame `rF` itself (`FStepIn rF.owned m m' rF.shared`), of a
resource `p` that is a part of `rF` (`hsub`: its cells and shares add up into `rF`'s). -/
theorem _root_.Zig.Mem.OwnsRes.fstepIn {u : ThreadId} {p rF : Res}
    (ho : m.OwnsRes u p) (hs : FStepIn rF.owned m m' rF.shared) (hu : u ≠ m.current)
    (hsub : ∀ l, p.excl l ≠ none → rF.excl l ≠ none)
    (hown : ∀ l, p.owned l ≠ none → rF.owned l ≠ none) : m'.OwnsRes u p :=
  ho.fstep hs hu (fun l hl => ⟨hown l (Res.owned_of_excl hl), Res.excl_shared_disj (hsub l hl)⟩)
    fun l hl => hown l (Res.owned_of_shared hl)

end OwnsRes

/-- **The frame reads of a step that reads only shares of `hO`** are among the frame's shares. -/
theorem _root_.Zig.FStepIn.interL {hF hR hO : Heap} {m m' : Mem}
    (hs : FStepIn hF m m' (hR.inter hO)) : FStepIn hF m m' hR :=
  hs.weakenR (fun _ h => h) fun _ _ h => (Heap.inter_ne.mp h).1

/-- A step whose frame reads are shares of `hO` reads only shares of `hO'`, if every frame byte
of a frame share that `hO` has, `hO'` has. -/
theorem _root_.Zig.FStepIn.interR {hF hR hO hO' : Heap} {m m' : Mem}
    (hs : FStepIn hF m m' (hR.inter hO))
    (h : ∀ l, hF l ≠ none → hR l ≠ none → hO l ≠ none → hO' l ≠ none) :
    FStepIn hF m m' (hR.inter hO') :=
  hs.weakenR (fun _ h => h) fun l hl hr =>
    let ⟨a, b⟩ := Heap.inter_ne.mp hr; Heap.inter_ne.mpr ⟨a, h l hl a b⟩

/-- **A step in the frame `rF` of `r` that reads only shares of `hO`** reads only `r`'s shares, if
every byte of `rF` that `hO` has, `r` holds (next to a frame byte, only a partial share:
`Holds.frame_shared`). -/
theorem _root_.Zig.FStepIn.toShared {hO : Heap} {m m₁ m₂ : Mem} {r rF : Res} (hh : Holds m r rF)
    (hs : FStepIn rF.owned m₁ m₂ (rF.shared.inter hO))
    (ho : ∀ l, rF.owned l ≠ none → hO l ≠ none → r.owned l ≠ none) :
    FStepIn rF.owned m₁ m₂ (rF.shared.inter r.shared) :=
  hs.interR fun l hl _ hb => hh.swap.frame_shared hl (ho l hl hb)

/-- Two steps next to the frame `rF`, of the part `r₀` and then of the part `r₁` it became: their
frame reads are shares `r₀` shares (`Holds.owned_sub'`: next to the same frame `r₁` holds no frame
byte `r₀` lacked). -/
theorem _root_.Zig.FStepIn.transPart {m₀ m₁ m₂ : Mem} {r₀ r₁ rF : Res} (hh₀ : Holds m₀ r₀ rF)
    (hh₁ : Holds m₁ r₁ rF) (hs : FStepIn rF.owned m₀ m₁ (rF.shared.inter r₀.shared))
    (hs' : FStepIn rF.owned m₁ m₂ (rF.shared.inter r₁.shared)) :
    FStepIn rF.owned m₀ m₂ (rF.shared.inter r₀.shared) :=
  hs.trans (hs'.toShared hh₀ fun _ hl hb =>
    hh₀.owned_sub' hh₁ (hh₀.swap.live_of_owned hl).1 (Res.owned_of_shared hb))

/-- **The frame's bytes and read shares** of a resource's step: a step in the frame `⟨rR ⋆ rF⟩`
is a step in `rF` (the shared bytes of the sum that `rF` holds are `rF`'s shared bytes). -/
theorem _root_.Zig.FStepIn.frameRight {m m' : Mem} {rR rF : Res} {hO : Heap}
    (hs : FStepIn (Res.owned ⟨rR.heap ∪ rF.heap, rR.know.union rF.know, rR.gh.add rF.gh⟩) m m'
      ((Res.shared ⟨rR.heap ∪ rF.heap, rR.know.union rF.know, rR.gh.add rF.gh⟩).inter hO)) :
    FStepIn rF.owned m m' (rF.shared.inter hO) :=
  hs.weakenR (fun _ hl => (Res.owned_sep rfl rfl).mpr (.inr hl))
    fun _ hl hs => let ⟨a, b⟩ := Heap.inter_ne.mp hs
      Heap.inter_ne.mpr ⟨Res.shared_sep' rfl rfl a hl, b⟩

/-- **The frame rule's step**: a step of the part `rP` in the frame `⟨rR ⋆ rF⟩`, reading only
shares of `rP`, is a step of `rP ⋆ rR` in `rF` that reads only its shares (`frameRight`,
`toShared`). -/
theorem _root_.Zig.FStepIn.framePart {m m₁ m₂ : Mem} {rP rR rF : Res}
    (hh : Holds m ⟨rP.heap ∪ rR.heap, rP.know.union rR.know, rP.gh.add rR.gh⟩ rF)
    (hs : FStepIn (Res.owned ⟨rR.heap ∪ rF.heap, rR.know.union rF.know, rR.gh.add rF.gh⟩) m₁ m₂
      ((Res.shared ⟨rR.heap ∪ rF.heap, rR.know.union rF.know, rR.gh.add rF.gh⟩).inter rP.shared)) :
    FStepIn rF.owned m₁ m₂
      (rF.shared.inter (Res.shared ⟨rP.heap ∪ rR.heap, rP.know.union rR.know, rP.gh.add rR.gh⟩)) :=
  hs.frameRight.toShared hh fun _ _ hl => (Res.owned_sep rfl rfl).mpr (.inl (Res.owned_of_shared hl))

/-! ## Thread triples -/

/-- `FTriple` for a step of one thread inside a concurrent run (module doc). The thread owns the
resource (`Mem.OwnsRes`: every access to its exclusive bytes, every write to its shared bytes
before its clock), and the step may read the frame's partial read shares that the resource shares
too (`FStepIn`'s `hR`, `rF.shared.inter r.shared`; module doc). -/
def FTTriple {α : Type} (P : FAssn) (c : MemM α) (Q : α → FAssn) : Prop :=
  ∀ m r rF, Holds m r rF → P r → m.FConc → m.OwnsRes m.current r →
    match (c.run m).run with
    | none => True
    | some (.error e) => e = .stackOverflow
    | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
        m'.OwnsRes m'.current r' ∧ FStepIn rF.owned m m' (rF.shared.inter r.shared)

namespace FTTriple

variable {α β : Type} {P P' R : FAssn} {Q Q' : α → FAssn} {c : MemM α}

theorem of_run
    (h : ∀ m r rF, Holds m r rF → P r → m.FConc → m.OwnsRes m.current r →
      ∃ v m' r', c.run m = pure (v, m') ∧ Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
        m'.OwnsRes m'.current r' ∧ FStepIn rF.owned m m' (rF.shared.inter r.shared)) :
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
  have := ht m r rF hh hp hs.fconc (.of_owns (hs.1.single.owns _))
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
      m.OwnsRes m.current r →
      match (c.run m).run with
      | none => True
      | some (.error e) => e = .stackOverflow
      | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
          m'.OwnsRes m'.current r' ∧ FStepIn rF.owned m m' (rF.shared.inter r.shared)) :
    ∀ m r rF, Φ m → Holds m r rF → P r → m.FConc → m.OwnsRes m.current r →
      match (c.run m).run with
      | none => True
      | some (.error e) => e = .stackOverflow
      | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
          m'.OwnsRes m'.current r' ∧ FStepIn rF.owned m m' (rF.shared.inter r.shared) := by
  intro m r rF hΦ hh hp hc ho
  have := h m (r.fix m) (rF.fix m) hΦ hh.fix hh.fix_exact hh.fix_exactF (hP m r rF hh hp) hc
    (ho.sub (fun _ hl => Res.excl_fix.mp hl) fun _ hl => Res.owned_fix.mp (Res.owned_of_shared hl))
  split at this
  · trivial
  · exact this
  · obtain ⟨r', hh', hq, hc', ho', hst⟩ := this
    exact ⟨r', hh'.congrF hh.fix_sim.symm rfl rfl, hq, hc', ho',
      hst.weakenR (fun _ hl => Res.owned_fix.mpr hl) fun _ _ hl =>
        let ⟨a, b⟩ := Heap.inter_ne.mp hl
        Heap.inter_ne.mpr ⟨Res.shared_fix.mp a, Res.shared_fix.mp b⟩⟩

/-- **Thread rules from exact cells** (`FTriple.of_fix`): it is enough to prove a thread triple
for resources whose cells are the memory's exact cells, if the precondition survives reading
the actual sizes. The thread owns the same bytes, and the frame has the same bytes. -/
theorem of_fix (hP : ∀ m r rF, Holds m r rF → P r → P (r.fix m))
    (h : ∀ m r rF, Holds m r rF → Exact m r → Exact m rF → P r → m.FConc →
      m.OwnsRes m.current r →
      match (c.run m).run with
      | none => True
      | some (.error e) => e = .stackOverflow
      | some (.ok (v, m')) => ∃ r', Holds m' r' rF ∧ Q v r' ∧ m'.FConc ∧
          m'.OwnsRes m'.current r' ∧ FStepIn rF.owned m m' (rF.shared.inter r.shared)) :
    FTTriple P c Q :=
  fun m r rF hh hp hc ho =>
    of_fix_on (fun _ => True) hP (fun m r rF _ => h m r rF) m r rF trivial hh hp hc ho

/-- **The frame rule.** The frame's bytes, tags, knowledge and ghost state stay, and the thread
keeps owning the frame's bytes. -/
theorem frame (ht : FTTriple P c Q) : FTTriple (P ⋆ R) c (fun v => Q v ⋆ R) := by
  intro m r rF hh hpr hc ho
  obtain ⟨rP, rR, hd, rfl, hp, hr⟩ := hpr
  have hRF := (FHeap.disjoint_union_left.mp hh.disj).2
  have := ht m rP _ (Holds.split hd hh) hp hc (ho.sepL rfl rfl)
  split at this
  · trivial
  · exact this
  · obtain ⟨r', hh', hq, hc', ho', hst⟩ := this
    have hQR := (FHeap.disjoint_union_right.mp hh'.disj).1
    have hj := Holds.join hQR hRF hh'
    exact ⟨_, hj, ⟨r', rR, hQR, rfl, hq, hr⟩, hc', Mem.OwnsRes.frame hh hj ho ho' hst,
      hst.framePart hh⟩

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
        exact ⟨r'', a, b, d, e, hst.transPart hh hh' hst'⟩

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
  have := ht m r' rF hh'.ofNoFp hp' hc (ho.upd hh hh'.ofNoFp)
  split at this
  · trivial
  · exact this
  · obtain ⟨r'', a, b, d, e, hst⟩ := this
    exact ⟨r'', a, b, d, e, hst.toShared hh fun _ _ hs =>
      hh.owned_sub hh'.ofNoFp (Res.owned_of_shared hs)⟩

/-- An update of the postcondition. -/
theorem eupd_post (ht : FTTriple P c Q) (hu : ∀ v, EUpd (Q v) (Q' v)) : FTTriple P c Q' := by
  intro m r rF hh hp hc ho
  have := ht m r rF hh hp hc ho
  split at this
  · trivial
  · exact this
  · obtain ⟨r', hh', hq, hc', ho', hst⟩ := this
    obtain ⟨r'', hh'', hq'⟩ := hu _ _ r' rF hh'.toNoFp hq hc'.noFp
    exact ⟨r'', hh''.ofNoFp, hq', hc', ho'.upd hh' hh''.ofNoFp, hst⟩

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
  -- the added knowledge changes no byte: the same shares (`Res.shared` reads heap and ghost)
  exact ht m ⟨r.heap, r.know.union (Know.single (.addr b A)), r.gh⟩ rF
    (hh.addKnow (Know.sub_single hkn)) hres hcm ho

/-- Knowledge and ghost state (anything that owns no bytes and no stack token) can be forgotten
(`FTriple.drop`). -/
theorem drop {K : α → FAssn} (ht : FTTriple P c (fun v => Q v ⋆ K v))
    (hK : ∀ v r, K v r → r.heap = FHeap.empty ∧ r.gh.Affine) : FTTriple P c Q := by
  intro m r rF hh hp hcm ho
  have := ht m r rF hh hp hcm ho
  split at this
  · trivial
  · exact this
  · obtain ⟨r', ⟨hd, hm, hk, hkF, hg⟩, ⟨r₁, r₂, -, rfl, hq, hk2⟩, hc', ho', hs'⟩ := this
    obtain ⟨e, ha⟩ := hK _ _ hk2
    simp only [e, FHeap.union_empty] at hd hm
    rw [ha.share_add] at hm
    exact ⟨r₁, ⟨hd, hm, hk.left, hkF, GOk.mono hg ha⟩, hq, hc', ho'.sepL rfl rfl, hs'⟩

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
  ∀ m r rF, Holds m r rF → P r → m.FConc → m.OwnsRes m.current r →
    ∃ v m', c.run m = pure (v, m')

/-- Total correctness of a thread's step. -/
def FTTotalTriple {α : Type} (P : FAssn) (c : MemM α) (Q : α → FAssn) : Prop :=
  FTTriple P c Q ∧ FTTReturns P c

namespace FTTotalTriple

variable {α β : Type} {P P' R : FAssn} {Q Q' : α → FAssn} {c : MemM α}

theorem toPartial (ht : FTTotalTriple P c Q) : FTTriple P c Q := ht.1

/-- The step has a result (the premise of a turn budget's `liftMem` step). -/
theorem halts (ht : FTTotalTriple P c Q) {m : Mem} {r rF : Res} (hh : Holds m r rF) (hp : P r)
    (hc : m.FConc) (ho : m.OwnsRes m.current r) : (c.run m).run ≠ none := by
  obtain ⟨v, m', e⟩ := ht.2 m r rF hh hp hc ho
  rw [e]; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run]

/-- **One logic**: a total thread triple is a total sequential triple. -/
theorem toFTotalTriple (ht : FTTotalTriple P c Q) : FTotalTriple P c Q :=
  ⟨ht.1.toFTriple, fun m r rF hh hp hs => ht.2 m r rF hh hp hs.fconc (.of_owns (hs.1.single.owns _))⟩

theorem conseq (ht : FTTotalTriple P c Q) (hp : ∀ r, P' r → P r) (hq : ∀ v r, Q v r → Q' v r) :
    FTTotalTriple P' c Q' :=
  ⟨ht.1.conseq hp hq, fun m r rF hh h' hc ho => ht.2 m r rF hh (hp _ h') hc ho⟩

theorem frame (ht : FTTotalTriple P c Q) : FTTotalTriple (P ⋆ R) c (fun v => Q v ⋆ R) := by
  refine ⟨ht.1.frame, fun m r rF hh hpr hc ho => ?_⟩
  obtain ⟨rP, rR, hd, rfl, hp, -⟩ := hpr
  exact ht.2 m rP _ (Holds.split hd hh) hp hc (ho.sepL rfl rfl)

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
