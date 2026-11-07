import ZigLean.Sep.Full.Thread
import ZigLean.Sep.Full.AllocSpec
import ZigLean.Sep.Full.Mmap
import ZigLean.Conc.Base.Heap
import ZigLean.Conc.Base.Threads

/-!
# The threads' parts over full-state resources

`FOwned own rO m` (`docs/sep-threads.md` §The threads' parts): thread `u`'s part is the resource
`own u`; the parts compose (`sepN`) and hold in `m` next to the protocol's rest `rO` (resources no
thread holds: a free lock's resource, shared atomic words, ledgers the protocol keeps); each
thread's clock owns its part's bytes. It replaces the legacy `Owned` (`ZigLean/Conc/Csl.lean`)
for the full-state logic; a proof keeps it in its protocol invariant, as before.

- **Message coverage** (`Mem.MsgCov`, `ZigLean/Conc/Clock.lean`) is part of the memory
  invariant (`FOwned.conc`): every step of a thread keeps it (`FStepIn.cov`), and the scheduler's
  steps (a stop, a spawn, a join, the futex queue) change neither the locations nor the record. A
  call resumed by the scheduler (`WP.call_fowned`) reads it at an atomic op's oracle pick.
- `FOwned.start`: no parts, the whole memory in `rO`, in a memory with no recorded access.
- `FOwned.step`, `WP.liftMem_fownedS` (and its forms `liftMem_fowned`, `liftM_fowned`,
  `callMC_fowned(S)`): a `MemM` step of thread `t` with a thread triple (`FTTriple`) on its part;
  the other parts and `rO` are the frame.
- `FOwned.keep` (a step that changes no block, location, thread, clock or access),
  `FOwned.recordAt` (a recorded access of a thread to its own bytes, e.g. a futex wait's read),
  `FOwned.cover` / `heap_empty` (every live byte belongs to a part or to `rO`).
- `FOwned.fork` (spawn), `FOwned.join`, `FOwned.current` (a stop), `FOwned.setThread` (a detach):
  the parts move directly, using the memory model's heap and access-clock facts
  (`ZigLean/Conc/Base/Threads.lean`).
-/

namespace Zig
namespace Full

open FAssn Conc Proto

/-! ## Parts as an indexed separating conjunction -/

/-- Thread `u`'s part is exactly `own u`. -/
abbrev partOf (own : ThreadId → Res) (u : ThreadId) : FAssn := fun r => r = own u

/-- The parts other than `t`'s. -/
abbrev partsBut (own : ThreadId → Res) (t : ThreadId) (j : Nat) : FAssn :=
  if j = t then emp else partOf own j

/-- A conjunct of `sepN` owns a part of the bytes. -/
theorem sepN_mem {f : Nat → FAssn} : ∀ {n : Nat} {r : Res} {j : Nat}, sepN n f r → j < n →
    ∃ rj, f j rj ∧ ∀ l, rj.heap l ≠ none → r.heap l ≠ none
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, _, j, ⟨r₁, r₂, _, rfl, h1, h2⟩, hj => by
    by_cases hjn : j = n
    · subst hjn
      exact ⟨r₁, h1, fun l hl => by simp only [FHeap.union_apply]; cases e : r₁.heap l <;> simp_all⟩
    · obtain ⟨rj, hf, hs⟩ := sepN_mem (j := j) h2 (by omega)
      exact ⟨rj, hf, fun l hl => by
        have := hs l hl
        simp only [FHeap.union_apply]; cases e : r₁.heap l <;> simp_all⟩

/-- A conjunct of `sepN` owns a part of the owned set (`Res.owned`: bytes and shares). -/
theorem sepN_owned {f : Nat → FAssn} : ∀ {n : Nat} {r : Res} {j : Nat}, sepN n f r → j < n →
    ∃ rj, f j rj ∧ ∀ l, rj.owned l ≠ none → r.owned l ≠ none
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, _, j, ⟨r₁, r₂, _, rfl, h1, h2⟩, hj => by
    by_cases hjn : j = n
    · subst hjn
      exact ⟨r₁, h1, fun _ hl => (Res.owned_sep rfl rfl).mpr (.inl hl)⟩
    · obtain ⟨rj, hf, hs⟩ := sepN_owned (j := j) h2 (by omega)
      exact ⟨rj, hf, fun l hl => (Res.owned_sep rfl rfl).mpr (.inr (hs l hl))⟩

/-- An exclusive byte of a conjunct of `sepN` (`Res.excl`: a cell or a whole share) is exclusive
in the sum. -/
theorem sepN_excl {f : Nat → FAssn} : ∀ {n : Nat} {r : Res} {j : Nat}, sepN n f r → j < n →
    ∃ rj, f j rj ∧ ∀ l, rj.excl l ≠ none → r.excl l ≠ none
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, _, j, ⟨r₁, r₂, _, rfl, h1, h2⟩, hj => by
    by_cases hjn : j = n
    · subst hjn
      exact ⟨r₁, h1, fun _ hl => Res.excl_sep rfl rfl (.inl hl)⟩
    · obtain ⟨rj, hf, hs⟩ := sepN_excl (j := j) h2 (by omega)
      exact ⟨rj, hf, fun l hl => Res.excl_sep rfl rfl (.inr (hs l hl))⟩

/-- An owned location of a `sepN` is owned by one of its conjuncts. -/
theorem sepN_cover_owned {f : Nat → FAssn} : ∀ {n : Nat} {r : Res} {l : Loc}, sepN n f r →
    r.owned l ≠ none → ∃ j < n, ∃ rj, f j rj ∧ rj.owned l ≠ none
  | 0, _, _, ⟨he, _, hg⟩, hl => absurd (by simp [Res.owned, he, hg, FHeap.empty, SCell.cell_zero]) hl
  | n + 1, _, l, ⟨r₁, r₂, _, rfl, h1, h2⟩, hl => by
    rcases (Res.owned_sep rfl rfl).mp hl with e | e
    · exact ⟨n, by omega, r₁, h1, e⟩
    · obtain ⟨j, hj, rj, hf, hr⟩ := sepN_cover_owned h2 e
      exact ⟨j, by omega, rj, hf, hr⟩

/-- A byte of a `sepN` belongs to one of its conjuncts. -/
theorem sepN_cover {f : Nat → FAssn} : ∀ {n : Nat} {r : Res} {l : Loc}, sepN n f r →
    r.heap l ≠ none → ∃ j < n, ∃ rj, f j rj ∧ rj.heap l ≠ none
  | 0, _, _, ⟨he, _, _⟩, hl => absurd (by rw [he]; rfl) hl
  | n + 1, _, l, ⟨r₁, r₂, _, rfl, h1, h2⟩, hl => by
    by_cases e : r₁.heap l = none
    · obtain ⟨j, hj, rj, hf, hr⟩ := sepN_cover h2 (by simpa [FHeap.union_apply, e] using hl)
      exact ⟨j, by omega, rj, hf, hr⟩
    · exact ⟨n, by omega, r₁, h1, e⟩

/-- Pick thread `t`'s part out of the parts. -/
theorem parts_pick {own : ThreadId → Res} {n t : Nat} {rT : Res} (ht : t < n)
    (h : sepN n (partOf own) rT) :
    ∃ rR, sepN n (partsBut own t) rR ∧ FHeap.Disjoint (own t).heap rR.heap ∧
      rT = ⟨(own t).heap ∪ rR.heap, (own t).know.union rR.know, (own t).gh.add rR.gh⟩ := by
  rw [sepN_pick ht] at h
  obtain ⟨r₁, r₂, hd, rfl, rfl, h2⟩ := h
  exact ⟨r₂, h2, hd, rfl⟩

/-- Another thread's part is within the rest. -/
theorem partsBut_sub {own : ThreadId → Res} {n t u : Nat} {rR : Res}
    (h : sepN n (partsBut own t) rR) (hu : u < n) (hut : u ≠ t) (l : Loc)
    (hl : (own u).heap l ≠ none) : rR.heap l ≠ none := by
  obtain ⟨rj, hf, hs⟩ := sepN_mem h hu
  simp only [partsBut, hut, ↓reduceIte, partOf] at hf
  subst hf; exact hs l hl

/-- Another thread's owned set is within the rest's. -/
theorem partsBut_owned {own : ThreadId → Res} {n t u : Nat} {rR : Res}
    (h : sepN n (partsBut own t) rR) (hu : u < n) (hut : u ≠ t) (l : Loc)
    (hl : (own u).owned l ≠ none) : rR.owned l ≠ none := by
  obtain ⟨rj, hf, hs⟩ := sepN_owned h hu
  simp only [partsBut, hut, ↓reduceIte, partOf] at hf
  subst hf; exact hs l hl

/-- Another thread's exclusive bytes are exclusive in the rest. -/
theorem partsBut_excl {own : ThreadId → Res} {n t u : Nat} {rR : Res}
    (h : sepN n (partsBut own t) rR) (hu : u < n) (hut : u ≠ t) (l : Loc)
    (hl : (own u).excl l ≠ none) : rR.excl l ≠ none := by
  obtain ⟨rj, hf, hs⟩ := sepN_excl h hu
  simp only [partsBut, hut, ↓reduceIte, partOf] at hf
  subst hf; exact hs l hl

/-- Put a new part `r` for `t` back. -/
theorem parts_put {own : ThreadId → Res} {n t : Nat} {rR r : Res} (ht : t < n)
    (h : sepN n (partsBut own t) rR) (hd : FHeap.Disjoint r.heap rR.heap) :
    sepN n (partOf (upd own t r)) ⟨r.heap ∪ rR.heap, r.know.union rR.know, r.gh.add rR.gh⟩ := by
  rw [sepN_pick ht]
  refine ⟨r, rR, hd, rfl, by simp [partOf], ?_⟩
  rw [sepN_congr (g := partsBut own t) fun j _ => ?_]
  · exact h
  · by_cases hj : j = t
    · simp [hj]
    · simp only [partsBut, hj, ↓reduceIte]; unfold partOf; rw [upd_ne _ _ hj]

theorem Exact.sub {m : Mem} {r : Res} (hx : Exact m r) : r.heap.erase.Sub m.heap := fun l c hc => by
  simp only [FHeap.erase, Option.map_eq_some_iff] at hc
  obtain ⟨fc, hfc, rfl⟩ := hc
  exact hx l fc hfc

/-- The composition of two resources (the resource of `P ⋆ Q`). -/
abbrev rsum (a b : Res) : Res := ⟨a.heap ∪ b.heap, a.know.union b.know, a.gh.add b.gh⟩

theorem rsum_comm {a b : Res} (hd : FHeap.Disjoint a.heap b.heap) : rsum a b = rsum b a := by
  simp only [rsum, FHeap.union_comm hd, Know.union_comm, Ghost.add_comm]

theorem rsum_assoc {a b c : Res} : rsum (rsum a b) c = rsum a (rsum b c) := by
  simp only [rsum, FHeap.union_assoc, Know.union_assoc, Ghost.add_assoc]

/-- The empty resource: the part of a thread that owns nothing (a joined one). -/
abbrev rnil : Res := ⟨FHeap.empty, Know.none, Ghost.unit⟩

theorem rnil_rsum (r : Res) : rsum rnil r = r := by
  simp [rsum, Know.none_union]

theorem rsum_rnil (r : Res) : rsum r rnil = r := by
  simp [rsum, Know.union_none]

theorem partOf_rnil : (fun r => r = rnil) = (emp : FAssn) := by
  funext r; apply propext
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩; rw [res_eta r, h1, h2, h3]

theorem Res.noCur_rsum {a b : Res} (ha : a.NoCur) (hb : b.NoCur) : (rsum a b).NoCur := fun v => by
  simp [ha v, hb v]

theorem Res.NoCur.left {a b : Res} (h : (rsum a b).NoCur) : a.NoCur := fun v => by
  have := h v; simp at this; omega

theorem Res.NoCur.right {a b : Res} (h : (rsum a b).NoCur) : b.NoCur := fun v => by
  have := h v; simp at this; omega

/-- A `sepN` of resources without `cur` tokens holds none. -/
theorem sepN_noCur {f : Nat → FAssn} (hf : ∀ j r, f j r → r.NoCur) :
    ∀ {n : Nat} {r : Res}, sepN n f r → r.NoCur
  | 0, _, h => fun v => by rw [h.2.2]; rfl
  | n + 1, _, ⟨r₁, r₂, _, rfl, h1, h2⟩ => Res.noCur_rsum (hf n r₁ h1) (sepN_noCur hf h2)

/-- **`m` holds any split with the same sum**: `Holds` reads only the sum of the resource and the
frame (its bytes, knowledge and ghost state), so a resource may move between them. -/
theorem Holds.regroup {m : Mem} {r rF r' rF' : Res} (hh : Holds m r rF)
    (hd : FHeap.Disjoint r'.heap rF'.heap) (he : rsum r' rF' = rsum r rF) : Holds m r' rF' := by
  have eh := congrArg Res.heap he
  have ek := congrArg Res.know he
  have eg := congrArg Res.gh he
  dsimp only at eh ek eg
  have hk : Know.Sub (r'.know.union rF'.know) m.kn := by rw [ek]; exact hh.know.union hh.knowF
  refine ⟨hd, by rw [eh, eg]; exact hh.heap, hk.left, hk.right, ?_⟩
  have hg := hh.ghost
  unfold GOk Ghost.Ok at hg ⊢
  rw [eg]; exact hg

/-! ## Thread ownership across fork and join -/

/-- A step in `hF` that may read `hR` is a step in the bytes of `hF` outside `hR`. -/
theorem _root_.Zig.FStepIn.unread {hF hR : Heap} {m m' : Mem} (hs : FStepIn hF m m' hR) :
    FStepIn (hF.diff hR) m m' :=
  hs.weakenR (fun l hl => by unfold Heap.diff at hl; split at hl <;> simp_all)
    fun l hl hr => by unfold Heap.diff at hl; split at hl <;> simp_all

/-- A step in a resource's bytes that may read its partial shares is a step in its cells, which
are no share. -/
theorem _root_.Zig.FStepIn.cells {r : Res} {m m' : Mem} (hs : FStepIn r.owned m m' r.shared) :
    FStepIn r.heap.erase m m' :=
  hs.unread.weaken fun l hl => by
    have hh : r.heap l ≠ none := fun e => hl (by simp [FHeap.erase, e])
    unfold Heap.diff
    rw [if_pos (Res.excl_shared_disj (Res.excl_of_heap hh))]
    exact Res.owned_of_heap hh

/-- **A step in a frame `a ⋆ b ⋆ c` is a step in `a ⋆ c`**: a byte that the whole frame holds as a
partial share, and `a ⋆ c` holds, is a partial share of `a ⋆ c` (a whole share of `a ⋆ c` would
be whole in the frame). -/
theorem _root_.Zig.FStepIn.dropMid {a b c : Res} {m m' : Mem}
    (hs : FStepIn (rsum a (rsum b c)).owned m m' (rsum a (rsum b c)).shared) :
    FStepIn (rsum a c).owned m m' (rsum a c).shared :=
  hs.weakenR (fun l hl => by
      rcases (Res.owned_sep rfl rfl).mp hl with h | h
      · exact (Res.owned_sep rfl rfl).mpr (.inl h)
      · exact (Res.owned_sep rfl rfl).mpr (.inr ((Res.owned_sep rfl rfl).mpr (.inr h))))
    fun l hl hR => by
      obtain ⟨hn, hw, -⟩ := Res.shared_ne.mp hR
      simp only [FHeap.union_apply, Option.or_eq_none_iff] at hn
      have hn' : (rsum a c).heap l = none := by
        simp only [FHeap.union_apply, Option.or_eq_none_iff]; exact ⟨hn.1, hn.2.2⟩
      refine Res.shared_ne.mpr ⟨hn', fun hw' => hw ?_,
        ((Res.owned_ne.mp hl).resolve_left fun h => h hn')⟩
      simp only [Ghost.add_share] at hw' ⊢
      rw [← SCell.add_assoc, SCell.add_comm (a.gh.share l) (b.gh.share l), SCell.add_assoc]
      exact SCell.Whole.add' _ hw'

theorem _root_.Zig.Mem.OwnsRes.fork {m m' : Mem} {t u c : ThreadId} {gt : Bool} {r : Res}
    (ho : m.OwnsRes u r) (hcs : m.clocks.size = m.threads.size) (hu : u < m.threads.size)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m'))) :
    m'.OwnsRes u r :=
  ⟨ho.1.fork hcs hu hf, ho.2.fork hcs hu hf⟩

theorem _root_.Zig.Mem.OwnsRes.fork_child {m m' : Mem} {t c : ThreadId} {gt : Bool} {r : Res}
    (ho : m.OwnsRes t r) (hcs : m.clocks.size = m.threads.size)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m'))) :
    m'.OwnsRes c r :=
  ⟨ho.1.fork_child hcs hf, ho.2.fork_child hcs hf⟩

theorem _root_.Zig.Mem.OwnsRes.join_other {m m' : Mem} {t u w : ThreadId} {r : Res}
    (ho : m.OwnsRes w r) (hw : w ≠ t)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m'))) :
    m'.OwnsRes w r :=
  ⟨ho.1.join_other hw hj, ho.2.join_other hw hj⟩

/-- **No gathering** (`hg`: at every byte one of `a`, `b` holds no partial share): an exclusive
byte of `a ⋆ b` is exclusive in `a` or in `b`. -/
theorem _root_.Zig.Full.Res.excl_rsum {a b : Res} (hg : ∀ l, a.shared l = none ∨ b.shared l = none)
    (l : Loc) (hl : (rsum a b).excl l ≠ none) : (a.excl ∪ b.excl) l ≠ none := fun hn => by
  simp only [Heap.union_apply, Option.or_eq_none_iff] at hn
  have hnone {r : Res} (hx : r.excl l = none) (hs : r.shared l = none) : r.owned l = none :=
    Classical.byContradiction fun ho => (Res.excl_or_shared ho).elim (· hx) (· hs)
  rcases hg l with e | e
  · have hl' : Res.excl ⟨b.heap ∪ a.heap, b.know.union a.know, b.gh.add a.gh⟩ l ≠ none := by
      have ha := hnone hn.1 e
      rcases Res.excl_ne.mp hl with e' | e'
      · refine Res.excl_ne.mpr (.inl ?_)
        have : a.heap l = none := by
          have h' : ¬ a.owned l ≠ none := fun h => h ha
          rw [Res.owned_ne] at h'; grind
        simpa [FHeap.union_apply, this] using e'
      · exact Res.excl_ne.mpr (.inr (by
          rw [Ghost.add_share, SCell.add_comm, ← Ghost.add_share]; exact e'))
    exact Res.excl_of_sep_none (hnone hn.1 e) hl' hn.2
  · exact Res.excl_of_sep_none (hnone hn.2 e) hl hn.1

/-- A shared byte of `a ⋆ b` is a byte of `a` or of `b`. -/
theorem _root_.Zig.Full.Res.shared_rsum {a b : Res} (l : Loc) (hl : (rsum a b).shared l ≠ none) :
    (a.owned ∪ b.owned) l ≠ none := fun hn => by
  simp only [Heap.union_apply, Option.or_eq_none_iff] at hn
  rcases (Res.owned_sep rfl rfl).mp (Res.owned_of_shared hl) with e | e
  · exact e hn.1
  · exact e hn.2

/-- **Join without gathering a share**: when at every byte one of the two resources holds no
partial share (`hg`), each exclusive byte of the joined resource is exclusive in one of them,
and the parent owns the join. Gathering two partial shares into a whole one would need
`Mem.Owns` of the byte: `OwnsR` does not order their holders' reads (`ShareRaceCX`). -/
theorem _root_.Zig.Mem.OwnsRes.join {m m' : Mem} {t u : ThreadId} {a b : Res}
    (h₁ : m.OwnsRes t a) (h₂ : m.OwnsRes u b) (ht : t < m.clocks.size)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m')))
    (hg : ∀ l, a.shared l = none ∨ b.shared l = none) :
    m'.OwnsRes t (rsum a b) :=
  ⟨(Mem.Owns.join h₁.1 h₂.1 ht hj).sub (Res.excl_rsum hg),
    (Mem.OwnsR.join h₁.ownsR h₂.ownsR ht hj).sub Res.shared_rsum⟩

/-- **Ownership of a sum without gathering a share** (`hg`, as `Mem.OwnsRes.join`). -/
theorem _root_.Zig.Mem.OwnsRes.gather {m : Mem} {t : ThreadId} {a b : Res} (ha : m.OwnsRes t a)
    (hb : m.OwnsRes t b) (hg : ∀ l, a.shared l = none ∨ b.shared l = none) :
    m.OwnsRes t (rsum a b) :=
  ⟨(Mem.OwnsC.union ha.1 hb.1).sub (Res.excl_rsum hg),
    (Mem.OwnsRC.union ha.ownsR hb.ownsR).sub Res.shared_rsum⟩

/-- **Ownership of a sum with an owned resource**: with `Mem.Owns` of every byte of `b`, a whole
share that `a ⋆ b` gathers is owned (a lock's acquire of a resource without partial shares,
`FOwned.take`). -/
theorem _root_.Zig.Mem.OwnsRes.addOwns {m : Mem} {t : ThreadId} {a b : Res} (ha : m.OwnsRes t a)
    (hb : m.Owns t b.owned) : m.OwnsRes t (rsum a b) :=
  ⟨(Mem.OwnsC.union ha.1 hb).sub fun l hl hn => by
      simp only [Heap.union_apply, Option.or_eq_none_iff] at hn
      exact Res.excl_of_sep_none hn.2 hl hn.1,
    (Mem.OwnsRC.union ha.ownsR (Mem.Owns.toR hb)).sub Res.shared_rsum⟩

/-! ## The parts -/

/-- The threads' parts and the protocol's rest in `m` (module doc). -/
structure FOwned (own : ThreadId → Res) (rO : Res) (m : Mem) : Prop where
  holds : ∃ rT, sepN m.threads.size (partOf own) rT ∧ Holds m rT rO
  owns : ∀ u < m.threads.size, m.OwnsRes u (own u)
  outside : ∀ u, m.threads.size ≤ u → emp (own u)
  csize : m.clocks.size = m.threads.size
  conc : ShapesWF (shapes m) ∧ m.LiveLayout ∧ m.MsgCov
  /-- No part and not the rest holds the running thread's token `cur`: a thread holds it only
  inside its own step (`WP.liftMem_fownedCurS`), so a stop keeps the parts (`FOwned.current`). -/
  noCur : (∀ u, (own u).NoCur) ∧ rO.NoCur

namespace FOwned

variable {own : ThreadId → Res} {rO : Res} {m m' : Mem} {t : ThreadId}

/-- Thread `t`'s part holds in `m`, with the other parts and `rO` as its frame. -/
theorem part (ho : FOwned own rO m) (ht : t < m.threads.size) :
    ∃ rR, sepN m.threads.size (partsBut own t) rR ∧ FHeap.Disjoint rR.heap rO.heap ∧
      Holds m (own t) ⟨rR.heap ∪ rO.heap, rR.know.union rO.know, rR.gh.add rO.gh⟩ := by
  obtain ⟨rT, hs, hh⟩ := ho.holds
  obtain ⟨rR, hR, hd, rfl⟩ := parts_pick ht hs
  exact ⟨rR, hR, (FHeap.disjoint_union_left.mp hh.disj).2, Holds.split hd hh⟩

/-- The parts and the rest hold no `cur` token. -/
theorem holds_noCur (ho : FOwned own rO m) {rT : Res} (hs : sepN m.threads.size (partOf own) rT) :
    ∀ v, (rT.gh.add rO.gh).ac.ex .cur v = 0 :=
  Res.noCur_rsum (sepN_noCur (fun j r h => by rw [h]; exact ho.noCur.1 j) hs) ho.noCur.2

/-- The other parts (`partsBut`) hold no `cur` token. -/
theorem partsBut_noCur (ho : FOwned own rO m) {rR : Res}
    (hR : sepN m.threads.size (partsBut own t) rR) : rR.NoCur :=
  sepN_noCur (fun j r h => by
    unfold partsBut at h
    split at h
    · exact fun v => by rw [h.2.2]; rfl
    · rw [h]; exact ho.noCur.1 j) hR

/-- Thread `t`'s part with its frame (`FOwned.part`) holds no `cur` token: a thread rule may add
`cur t` (`Holds.addCurF`, `Holds.addCur`). -/
theorem part_noCur (ho : FOwned own rO m) {rR : Res}
    (hR : sepN m.threads.size (partsBut own t) rR) :
    ∀ v, ((own t).gh.add (rR.gh.add rO.gh)).ac.ex .cur v = 0 :=
  Res.noCur_rsum (ho.noCur.1 t) (Res.noCur_rsum (ho.partsBut_noCur hR) ho.noCur.2)

/-- **Thread `t`'s part and the rest, split anew**: a new part `o'` and rest `rO'` with the same
sum as `t`'s part and the rest (e.g. a resource moves between them: in a two-lock product, the
other lock's held resource, which one lock's view keeps in the rest and the other's in the
part). The new part must be `t`'s (`Mem.OwnsRes`: a share it gathers into a whole one needs
`Mem.Owns` of the byte, engine ledger #share-gather); the other parts stay. -/
theorem move {o' rO' : Res} (ho : FOwned own rO m) (ht : t < m.threads.size)
    (hd : FHeap.Disjoint o'.heap rO'.heap) (he : rsum o' rO' = rsum (own t) rO)
    (hown : m.OwnsRes t o') : FOwned (upd own t o') rO' m := by
  obtain ⟨rT, hs, hh⟩ := ho.holds
  obtain ⟨rR, hR, hdR, rfl⟩ := parts_pick ht hs
  have hRO : FHeap.Disjoint rR.heap rO.heap := (FHeap.disjoint_union_left.mp hh.disj).2
  -- `rR` is apart from the old sum, so from the new one's summands
  have hR' : FHeap.Disjoint rR.heap (o'.heap ∪ rO'.heap) := by
    rw [show o'.heap ∪ rO'.heap = (own t).heap ∪ rO.heap from congrArg Res.heap he]
    exact FHeap.disjoint_union_right.mpr ⟨hdR.symm, hRO⟩
  obtain ⟨hRo, hRr⟩ := FHeap.disjoint_union_right.mp hR'
  have hcur : (rsum o' rO').NoCur := by rw [he]; exact Res.noCur_rsum (ho.noCur.1 t) ho.noCur.2
  refine ⟨⟨_, parts_put ht hR hRo.symm, hh.regroup ?_ ?_⟩, fun u hu => ?_, fun u hu => ?_,
    ho.csize, ho.conc, fun u => ?_, hcur.right⟩
  · exact FHeap.disjoint_union_left.mpr ⟨hd, hRr⟩
  · show rsum (rsum o' rR) rO' = rsum (rsum (own t) rR) rO
    calc rsum (rsum o' rR) rO' = rsum (rsum o' rO') rR := by
          rw [rsum_assoc (a := o'), rsum_comm hRr, ← rsum_assoc]
      _ = rsum (rsum (own t) rO) rR := by rw [he]
      _ = rsum (rsum (own t) rR) rO := by
          rw [rsum_assoc (a := own t), rsum_comm hRO.symm, ← rsum_assoc]
  · by_cases e : u = t
    · subst e; rw [upd_self]; exact hown
    · rw [upd_ne _ _ e]; exact ho.owns u hu
  · rw [upd_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le ht hu))]; exact ho.outside u hu
  · by_cases e : u = t
    · subst e; rw [upd_self]; exact hcur.left
    · rw [upd_ne _ _ e]; exact ho.noCur.1 u

/-- **The start**: no thread owns anything, the whole memory is the protocol's rest (its
messages covered, as in a memory without atomic locations: `Mem.MsgCov.of_atomics`). No thread
has a stack budget (a budget demands its thread's stack token, `StackAuth`). -/
theorem start (hf : m.footprint = #[]) (hc : m.clocks.size = m.threads.size)
    (hw : ShapesWF (shapes m)) (hl : m.LiveLayout) (hmc : m.MsgCov)
    (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) :
    FOwned (fun _ => ⟨FHeap.empty, Know.none, Ghost.unit⟩) ⟨m.fheap, Know.none, Ghost.unit⟩ m where
  holds := by
    refine ⟨⟨FHeap.empty, Know.none, Ghost.unit⟩, ?_, ?_⟩
    · have : ∀ n, sepN n (partOf fun _ => (⟨FHeap.empty, Know.none, Ghost.unit⟩ : Res))
          ⟨FHeap.empty, Know.none, Ghost.unit⟩ := by
        intro n; induction n with
        | zero => exact ⟨rfl, rfl, rfl⟩
        | succ n ih =>
          refine ⟨⟨FHeap.empty, Know.none, Ghost.unit⟩, ⟨FHeap.empty, Know.none, Ghost.unit⟩,
            FHeap.disjoint_empty _, ?_, rfl, ih⟩
          simp [Know.union_none, Ghost.add_unit]
      exact this _
    · exact ⟨fun _ => .inl rfl, SMatch.of_fmatch (by simpa using FMatch.fheap m)
        fun _ => by rw [Ghost.add_unit]; exact SCell.empty_zero, Know.sub_none _, Know.sub_none _,
        by simpa [Ghost.add_unit] using GOk.unit hns⟩
  owns _ _ := ⟨fun e he => by rw [hf] at he; simp at he, fun e he => by rw [hf] at he; simp at he⟩
  outside _ _ := ⟨rfl, rfl, rfl⟩
  csize := hc
  conc := ⟨hw, hl, hmc⟩
  noCur := ⟨fun _ _ => rfl, fun _ => rfl⟩

/-- `main`'s part at a start in the plain mode. -/
def _root_.Zig.Full.plainOwn : ThreadId → Res := upd (fun _ => rnil) 0 ⟨FHeap.empty, Know.none, Ghost.plain⟩

theorem _root_.Zig.Full.plainOwn_zero : plainOwn 0 = ⟨FHeap.empty, Know.none, Ghost.plain⟩ := by
  simp [plainOwn]

theorem _root_.Zig.Full.plainOwn_ne {u : ThreadId} (h : u ≠ 0) : plainOwn u = rnil := by
  simp [plainOwn, upd_ne _ _ h]

/-- **The start in the plain mode** (`Holds.addPlain`): as `FOwned.start`, and `main` (thread 0)
holds the plain mode (`plain`): no thread has a stack budget and no meter runs. -/
theorem start_plain (hf : m.footprint = #[]) (hc : m.clocks.size = m.threads.size)
    (hw : ShapesWF (shapes m)) (hl : m.LiveLayout) (hmc : m.MsgCov) (ht0 : 0 < m.threads.size)
    (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) :
    FOwned plainOwn ⟨m.fheap, Know.none, Ghost.unit⟩ m where
  holds := by
    refine ⟨⟨FHeap.empty, Know.none, Ghost.plain⟩, ?_, ?_⟩
    · have : ∀ n, 0 < n → sepN n (partOf plainOwn) ⟨FHeap.empty, Know.none, Ghost.plain⟩ := by
        intro n hn
        induction n with
        | zero => exact absurd hn (Nat.lt_irrefl 0)
        | succ n ih =>
          rcases Nat.eq_zero_or_pos n with rfl | hpos
          · refine ⟨plainOwn 0, rnil, FHeap.disjoint_empty _, ?_, rfl, ⟨rfl, rfl, rfl⟩⟩
            simp [plainOwn_zero, Know.union_none]
          · refine ⟨rnil, ⟨FHeap.empty, Know.none, Ghost.plain⟩, FHeap.disjoint_empty _, ?_,
              (plainOwn_ne (Nat.pos_iff_ne_zero.mp hpos)).symm, ih hpos⟩
            simp [Know.none_union, Ghost.unit_add]
      exact this _ ht0
    · have hh : Holds m rnil ⟨m.fheap, Know.none, Ghost.unit⟩ :=
        ⟨fun _ => .inl rfl, SMatch.of_fmatch (by simpa using FMatch.fheap m)
        fun _ => by rw [Ghost.add_unit]; exact SCell.empty_zero, Know.sub_none _, Know.sub_none _,
          by simpa [Ghost.add_unit] using GOk.unit hns⟩
      simpa using hh.addPlain hns fun L => by simp
  owns _ _ := ⟨fun e he => by rw [hf] at he; simp at he, fun e he => by rw [hf] at he; simp at he⟩
  outside u hu := by
    rw [plainOwn_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le ht0 hu))]; exact ⟨rfl, rfl, rfl⟩
  csize := hc
  conc := ⟨hw, hl, hmc⟩
  noCur := ⟨fun u v => by
    by_cases e : u = 0
    · subst e; rw [plainOwn_zero]; simp [Ghost.plain]
    · rw [plainOwn_ne e]; rfl, fun _ => rfl⟩

theorem _root_.Zig.Full.sepN_rnil_gh : ∀ {n : Nat} {r : Res}, sepN n (partOf fun _ => rnil) r →
    r.gh = Ghost.unit
  | 0, _, h => h.2.2
  | _ + 1, _, ⟨_, _, _, rfl, rfl, h2⟩ => by simp [sepN_rnil_gh h2]

/-- **The start with the plain mode in the rest**: as `FOwned.start`, and the protocol's rest
holds the plain mode, which any thread can copy into its part (`FOwned.dupPlain`). -/
theorem start_plainRest (hf : m.footprint = #[]) (hc : m.clocks.size = m.threads.size)
    (hw : ShapesWF (shapes m)) (hl : m.LiveLayout) (hmc : m.MsgCov)
    (hns : m.NoStack := by exact Mem.noStack_of_stacks rfl) :
    FOwned (fun _ => rnil) ⟨m.fheap, Know.none, Ghost.plain⟩ m := by
  have ho := start hf hc hw hl hmc hns
  refine ⟨?_, ho.owns, ho.outside, ho.csize, ho.conc, fun _ _ => rfl, fun v => by simp [Ghost.plain]⟩
  obtain ⟨rT, h1, h2⟩ := ho.holds
  have e := sepN_rnil_gh h1
  have := h2.swap.addPlain hns fun L => by rw [Ghost.add_comm]; simp [e]
  exact ⟨rT, h1, by simpa using this.swap⟩

/-- **Thread `t` copies the plain mode out of the rest** (`Holds.dupPlain`). -/
theorem dupPlain (ho : FOwned own rO m) (ht : t < m.threads.size)
    (hF : rO.Plain) :
    FOwned (upd own t ⟨(own t).heap, (own t).know, (own t).gh.add Ghost.plain⟩) rO m := by
  refine ⟨?_, fun u hu => ?_, fun u hu => ?_, ho.csize, ho.conc, ⟨fun u v => ?_, ho.noCur.2⟩⟩
  rotate_right
  · by_cases e : u = t
    · subst e; rw [upd_self]; simpa [Ghost.plain] using ho.noCur.1 u v
    · rw [upd_ne _ _ e]; exact ho.noCur.1 u v
  · obtain ⟨rT, hs, hh⟩ := ho.holds
    obtain ⟨rR, hR, hd, rfl⟩ := parts_pick ht hs
    refine ⟨_, parts_put (r := ⟨(own t).heap, (own t).know, (own t).gh.add Ghost.plain⟩) ht hR hd, ?_⟩
    have := hh.dupPlain hF
    have e : ((own t).gh.add Ghost.plain).add rR.gh = ((own t).gh.add rR.gh).add Ghost.plain := by
      rw [Ghost.add_assoc, Ghost.add_comm Ghost.plain, ← Ghost.add_assoc]
    simpa [e] using this
  · by_cases e : u = t
    · subst e; rw [upd_self]; exact (Mem.OwnsRes.addGh_iff).mpr (ho.owns u hu)
    · rw [upd_ne _ _ e]; exact ho.owns u hu
  · rw [upd_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le ht hu))]; exact ho.outside u hu

/-- **A step of thread `t`** with a thread triple on its part (`FTTriple`'s post). The new part
holds no `cur` token (`Holds.dropCurF`: the thread rules run the step with `cur t` in the frame
or take it back). -/
theorem step {rR r' : Res} (ho : FOwned own rO m) (hc : m.current = t) (ht : t < m.threads.size)
    (hR : sepN m.threads.size (partsBut own t) rR) (hRO : FHeap.Disjoint rR.heap rO.heap)
    (hh : Holds m' r' ⟨rR.heap ∪ rO.heap, rR.know.union rO.know, rR.gh.add rO.gh⟩)
    (hcm : m'.FConc) (how : m'.OwnsRes m'.current r')
    (hs : FStepIn (Res.owned ⟨rR.heap ∪ rO.heap, rR.know.union rO.know, rR.gh.add rO.gh⟩) m m'
      (Res.shared ⟨rR.heap ∪ rO.heap, rR.know.union rO.know, rR.gh.add rO.gh⟩))
    (hnc : r'.NoCur) :
    FOwned (upd own t r') rO m' where
  noCur := ⟨fun u => by
    by_cases e : u = t
    · subst e; rw [upd_self]; exact hnc
    · rw [upd_ne _ _ e]; exact ho.noCur.1 u, ho.noCur.2⟩
  holds := by
    rw [hs.threads]
    exact ⟨_, parts_put ht hR (FHeap.disjoint_union_right.mp hh.disj).1,
      Holds.join (FHeap.disjoint_union_right.mp hh.disj).1 hRO hh⟩
  owns u hu := by
    rw [hs.threads] at hu
    by_cases hut : u = t
    · subst hut; rw [upd_self]; rw [hs.current, hc] at how; exact how
    · rw [upd_ne _ _ hut]
      exact (ho.owns u hu).fstepIn hs (hc ▸ hut)
        (fun l hl => Res.excl_sep rfl rfl (.inl (partsBut_excl hR hu hut l hl)))
        fun l hl => (Res.owned_sep rfl rfl).mpr (.inl (partsBut_owned hR hu hut l hl))
  outside u hu := by
    rw [hs.threads] at hu
    rw [upd_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le ht hu))]; exact ho.outside u hu
  csize := by rw [hs.size, hs.threads]; exact ho.csize
  conc := ⟨hcm.2.1, hcm.2.2, hs.msgCov ho.conc.2.2⟩

/-- A stop: only `current` changes (no part holds `cur`, `Holds.stop`). -/
theorem current (ho : FOwned own rO m) (t : ThreadId) : FOwned own rO { m with current := t } :=
  ⟨by obtain ⟨rT, h1, h2⟩ := ho.holds; exact ⟨rT, h1, h2.stop (ho.holds_noCur h1) t⟩,
    ho.owns, ho.outside, ho.csize, ho.conc, ho.noCur⟩

/-- A change of a thread's record (a detach). -/
theorem setThread (ho : FOwned own rO m) (tid : ThreadId) (rec : ThreadRec) :
    FOwned own rO { m with threads := m.threads.set! tid rec } := by
  have hs : (m.threads.set! tid rec).size = m.threads.size := by simp [Array.set!_eq_setIfInBounds]
  exact ⟨by
      dsimp only; rw [hs]; obtain ⟨rT, h1, h2⟩ := ho.holds
      exact ⟨rT, h1, Holds.congrMem (m := m) rfl rfl h2⟩,
    fun u hu => ho.owns u (by rw [hs] at hu; exact hu), fun u hu => ho.outside u (by rw [hs] at hu; exact hu),
    by rw [hs]; exact ho.csize, ho.conc, ho.noCur⟩

/-- **Spawn**: the parent `t` gives `r₂` of its part `r₁ ⋆ r₂` to the new thread. -/
theorem fork {r₁ r₂ : Res} {c : ThreadId} {gt : Bool} (ho : FOwned own rO m)
    (ht : t < m.threads.size)
    (hsplit : own t = ⟨r₁.heap ∪ r₂.heap, r₁.know.union r₂.know, r₁.gh.add r₂.gh⟩)
    (hd12 : FHeap.Disjoint r₁.heap r₂.heap)
    (hf : ((Thread.forkWith gt).run { m with current := t }).run = some (.ok (c, m'))) :
    FOwned (upd (upd own t r₁) c r₂) rO m' := by
  have hb₁ : m.OwnsRes t r₁ :=
    (ho.owns t ht).sepL (congrArg Res.heap hsplit) (congrArg Res.gh hsplit)
  have hb₂ : m.OwnsRes t r₂ :=
    (ho.owns t ht).sepR (congrArg Res.heap hsplit) (congrArg Res.gh hsplit)
  have h1 : m'.OwnsRes t r₁ := Mem.OwnsRes.fork hb₁ ho.csize ht hf
  have h2 : m'.OwnsRes c r₂ := Mem.OwnsRes.fork_child hb₂ ho.csize hf
  have hother (u : ThreadId) (hu : u < m.threads.size) : m'.OwnsRes u (own u) :=
    (ho.owns u hu).fork ho.csize hu hf
  rw [Proto.forkWith_run] at hf
  simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  obtain ⟨rR, hR, hRO, hh⟩ := ho.part ht
  have hd := FHeap.disjoint_union_right.mp hh.disj
  rw [hsplit] at hd
  have h1R : FHeap.Disjoint r₁.heap rR.heap := fun l => by
    rcases hd.1 l with e | e
    · simp only [FHeap.union_apply, Option.or_eq_none_iff] at e; exact .inl e.1
    · exact .inr e
  have h2R : FHeap.Disjoint r₂.heap rR.heap := fun l => by
    rcases hd.1 l with e | e
    · simp only [FHeap.union_apply, Option.or_eq_none_iff] at e; exact .inl e.2
    · exact .inr e
  have hnt : (rsum r₁ r₂).NoCur := by have := ho.noCur.1 t; rw [hsplit] at this; exact this
  refine ⟨?_, fun u hu => ?_, fun u hu => ?_, by simpa using ho.csize,
    ho.conc, ⟨fun u => ?_, ho.noCur.2⟩⟩
  · have h12R : FHeap.Disjoint (r₁.heap ∪ r₂.heap) rR.heap := hd.1
    have hput := parts_put (r := r₁) ht hR h1R
    rw [sepN_congr (g := partOf (upd (upd own t r₁) m.threads.size r₂)) fun j hj => by
      unfold partOf; rw [upd_ne _ _ (show j ≠ m.threads.size by omega)]] at hput
    rw [hsplit] at hh
    have hj : Holds m (rsum (rsum r₁ r₂) rR) rO := Holds.join h12R hRO hh
    rw [rsum_comm hd12, rsum_assoc] at hj
    have hnc : ∀ v, ((rsum r₂ (rsum r₁ rR)).gh.add rO.gh).ac.ex .cur v = 0 :=
      Res.noCur_rsum (Res.noCur_rsum hnt.right (Res.noCur_rsum hnt.left (ho.partsBut_noCur hR)))
        ho.noCur.2
    refine ⟨rsum r₂ (rsum r₁ rR), ?_, Holds.congrMem (m := { m with current := t }) rfl rfl
      (hj.stop hnc t)⟩
    dsimp only; rw [Array.size_push]
    exact ⟨r₂, rsum r₁ rR, FHeap.disjoint_union_right.mpr ⟨hd12.symm, h2R⟩, rfl,
      by simp [partOf], hput⟩
  · dsimp only at hu; simp only [Array.size_push] at hu
    by_cases huc : u = m.threads.size
    · subst huc; rw [upd_self]; exact h2
    · rw [upd_ne _ _ huc]
      by_cases hut : u = t
      · subst hut; rw [upd_self]; exact h1
      · rw [upd_ne _ _ hut]
        exact hother u (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hu) huc)
  · dsimp only at hu; simp only [Array.size_push] at hu
    have htu : t < u := Nat.lt_of_lt_of_le ht (Nat.le_of_succ_le hu)
    rw [upd_ne _ _ (Nat.ne_of_gt hu), upd_ne _ _ (Nat.ne_of_gt htu)]
    exact ho.outside u (Nat.le_of_succ_le hu)
  · by_cases huc : u = m.threads.size
    · subst huc; rw [upd_self]; exact hnt.right
    · rw [upd_ne _ _ huc]
      by_cases hut : u = t
      · subst hut; rw [upd_self]; exact hnt.left
      · rw [upd_ne _ _ hut]; exact ho.noCur.1 u

/-- Two threads' parts are disjoint. -/
theorem disj (ho : FOwned own rO m) {u v : ThreadId} (hu : u < m.threads.size)
    (hv : v < m.threads.size) (huv : u ≠ v) : FHeap.Disjoint (own u).heap (own v).heap := fun l => by
  obtain ⟨rR, hR, -, hh⟩ := ho.part hu
  cases e : (own v).heap l with
  | none => exact .inr rfl
  | some fc =>
    have := partsBut_sub hR hv (Ne.symm huv) l (by simp [e])
    exact .inl ((FHeap.disjoint_union_right.mp hh.disj).1 l |>.resolve_right this)

/-- Distinct threads' parts are disjoint even when either thread is outside the current
thread table: an absent thread owns the empty resource. -/
theorem disj_any (ho : FOwned own rO m) {u v : ThreadId} (huv : u ≠ v) :
    FHeap.Disjoint (own u).heap (own v).heap := by
  by_cases hu : u < m.threads.size
  · by_cases hv : v < m.threads.size
    · exact ho.disj hu hv huv
    · rw [(ho.outside v (Nat.le_of_not_lt hv)).1]
      exact FHeap.disjoint_empty _
  · rw [(ho.outside u (Nat.le_of_not_lt hu)).1]
    exact (FHeap.disjoint_empty _).symm

/-- **Join**: the parent `t` takes the part of thread `u`, which has ended; `u` keeps nothing. -/
theorem join {u : ThreadId} (ho : FOwned own rO m) (ht : t < m.threads.size) (hut : u ≠ t)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m')))
    (hg : ∀ l, (own t).shared l = none ∨ (own u).shared l = none := by
      intro l; exact .inl ((Res.excl_eq_erase).2 l)) :
    FOwned (upd (upd own u rnil) t (rsum (own t) (own u))) rO m' := by
  obtain ⟨rec, hr, -, hm⟩ := Proto.join_eq hj
  have hul : u < m.threads.size := (Array.getElem?_eq_some_iff.mp hr).1
  have hjoin : m'.OwnsRes t (rsum (own t) (own u)) :=
    (ho.owns t ht).join (ho.owns u hul) (by rw [ho.csize]; exact ht) hj hg
  have hother (w : ThreadId) (hw : w < m.threads.size) (hwt : w ≠ t) :
      m'.OwnsRes w (own w) := (ho.owns w hw).join_other hwt hj
  subst hm
  obtain ⟨rR, hR, hRO, hh⟩ := ho.part ht
  -- `u`'s part out of the others'
  have hR' := hR
  rw [sepN_pick hul] at hR'
  obtain ⟨ru, rR', hdu, rfl, hru, hR'⟩ := hR'
  have hut' : ¬ @Eq Nat u t := hut
  simp only [partsBut, hut', ↓reduceIte] at hru
  subst hru
  have hR₁ : sepN m.threads.size (partsBut (upd own u rnil) t) rR' := by
    rw [sepN_congr (g := fun j => if j = u then emp else partsBut own t j) fun j _ => ?_]
    · exact hR'
    · by_cases hju : j = u
      · subst hju
        have hjt : ¬ @Eq Nat j t := hut
        simp only [partsBut, hjt, ↓reduceIte]; unfold partOf; rw [upd_self]; exact partOf_rnil
      · simp only [partsBut, hju, ↓reduceIte]; unfold partOf; rw [upd_ne _ _ hju]
  have hd := FHeap.disjoint_union_right.mp hh.disj
  have hdt := FHeap.disjoint_union_right.mp hd.1
  have hdtu : FHeap.Disjoint (rsum (own t) (own u)).heap rR'.heap :=
    FHeap.disjoint_union_left.mpr ⟨hdt.2, hdu⟩
  have hsz : (m.threads.set! u { rec with joined := true }).size = m.threads.size := by
    simp [Array.set!_eq_setIfInBounds]
  refine ⟨?_, fun w hw => ?_, fun w hw => ?_, by simpa using ho.csize,
    ho.conc, ⟨fun w => ?_, ho.noCur.2⟩⟩
  · dsimp only; rw [hsz]
    have hnR := ho.partsBut_noCur hR
    have hnc : ∀ v, ((rsum (rsum (own t) (own u)) rR').gh.add rO.gh).ac.ex .cur v = 0 :=
      Res.noCur_rsum (Res.noCur_rsum (Res.noCur_rsum (ho.noCur.1 t) (ho.noCur.1 u)) hnR.right)
        ho.noCur.2
    refine ⟨_, parts_put ht hR₁ hdtu, Holds.congrMem (m := { m with current := t }) rfl rfl
      (Holds.stop ?_ hnc t)⟩
    have := Holds.join hd.1 hRO hh
    show Holds m (rsum (rsum (own t) (own u)) rR') rO
    rw [rsum_assoc]
    exact this
  · by_cases hwt : w = t
    · subst hwt
      rw [upd_self]
      exact hjoin
    · rw [upd_ne _ _ hwt]
      by_cases hwu : w = u
      · subst hwu; rw [upd_self]
        have h0 : ∀ l, rnil.owned l = none := fun l => by
          simp [rnil, Res.owned, FHeap.empty, SCell.cell_zero]
        exact (hother w hul hut).sub (fun l hl => absurd (h0 l) (Res.owned_of_excl hl))
          fun l hl => absurd (h0 l) (Res.owned_of_shared hl)
      · rw [upd_ne _ _ hwu]; exact hother w (by simpa using hw) hwt
  · dsimp only at hw; rw [hsz] at hw
    rw [upd_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le ht hw)),
      upd_ne _ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le hul hw))]
    exact ho.outside w hw
  · by_cases hwt : w = t
    · subst hwt; rw [upd_self]; exact Res.noCur_rsum (ho.noCur.1 w) (ho.noCur.1 u)
    · rw [upd_ne _ _ hwt]
      by_cases hwu : w = u
      · subst hwu; rw [upd_self]; exact fun _ => rfl
      · rw [upd_ne _ _ hwu]; exact ho.noCur.1 w

/-- **A step that changes no block, atomic location, thread, clock or recorded access** (a stop,
a futex queue, a cancelation request, a group's table) keeps the parts. -/
theorem keep (ho : FOwned own rO m) (hb : m'.blocks = m.blocks) (ha : m'.atomics = m.atomics)
    (ht : m'.threads = m.threads) (hc : m'.clocks = m.clocks) (hf : m'.footprint = m.footprint)
    (hx : m.Aux m' := by exact ⟨rfl, rfl, rfl⟩) :
    FOwned own rO m' := by
  have hsh : shapes m' = shapes m := by simp only [shapes, ha]
  refine ⟨?_, fun u hu => ?_, fun u hu => ho.outside u (ht ▸ hu), by rw [hc, ht]; exact ho.csize,
    ⟨hsh ▸ ho.conc.1, ?_, ho.conc.2.2.keep (fun _ hl _ => ha ▸ hl)
      (fun _ _ _ hin => hin.of_blocks hb) fun _ he => hf ▸ he⟩, ho.noCur⟩
  · rw [ht]; obtain ⟨rT, h1, h2⟩ := ho.holds
    exact ⟨rT, h1, Holds.congrMem (m := { m with current := m'.current }) hb ha
      (h2.stop (ho.holds_noCur h1) m'.current) (MemAuth.Keep.of_aux hb hx rfl)⟩
  · rw [ht] at hu
    have h := ho.owns u hu
    refine ⟨fun e he htc => ?_, fun e he hw htc => ?_⟩
    · rw [hf] at he; rw [hb] at htc
      show VClock.le e.clock (m'.clocks[u]!) = true
      rw [hc]; exact h.1 e he htc
    · rw [hf] at he; rw [hb] at htc
      show VClock.le e.clock (m'.clocks[u]!) = true
      rw [hc]; exact h.2 e he hw htc
  · obtain ⟨hd, hbd⟩ := ho.conc.2.1
    exact ⟨fun b b' blk blk' hne h1 h2 => hd b b' blk blk' hne (hb ▸ h1) (hb ▸ h2),
      fun b blk h1 => hbd b blk (hb ▸ h1)⟩

/-- **A recorded access of thread `t` to bytes of its part** (a futex wait's read of its word):
the parts stay. -/
theorem recordAt {b : BlockId} {off len : Nat} {kind : AccessKind} (ho : FOwned own rO m)
    (hc : m.current = t) (ht : t < m.threads.size)
    (hin : ∀ x, off ≤ x → x < off + len → (own t).heap (b, x) ≠ none) (hb : b < m.blocks.size)
    (hw : kind.isWrite = true → ¬ m.IsConst b := by intro h; exact absurd h (by decide)) :
    FOwned own rO (m.recordAt b off len kind) := by
  obtain ⟨rR, hR, hRO, hh⟩ := ho.part ht
  have hcs : m.current < m.clocks.size := by rw [hc, ho.csize]; exact ht
  have := ho.step (m' := m.recordAt b off len kind) (r' := own t) hc ht hR hRO
    (Holds.congrMem (m := m) rfl rfl hh)
    ⟨by show m.current < (m.clocks.set! m.current _).size; simpa using hcs, ho.conc.1, ho.conc.2.1⟩
    (have hot : m.OwnsRes m.current (own t) := hc ▸ ho.owns t ht
     ⟨Mem.Owns.recordAt hcs hot.1, Mem.OwnsR.recordAt hcs hot.2⟩)
    (FStepIn.recordAt hcs (hh.erase_disj_owned)
      (fun x h1 h2 => by simpa [FHeap.erase] using hin x h1 h2) hb hw) (ho.noCur.1 t)
  rwa [upd_same] at this

/-- **Every live byte belongs to a thread's part or to the rest.** -/
theorem cover (ho : FOwned own rO m) {l : Loc} {c : Cell} (hl : m.heap l = some c) :
    (∃ u < m.threads.size, (own u).owned l ≠ none) ∨ rO.owned l ≠ none := by
  obtain ⟨rT, hs, hh⟩ := ho.holds
  rcases hh.owned_of_live (l := l) (by simp [hl]) with e | e
  · obtain ⟨j, hj, rj, hf, hr⟩ := sepN_cover_owned hs e
    exact .inl ⟨j, hj, by rw [← hf]; exact hr⟩
  · exact .inr e

/-- No part and not the rest owns a byte or a share: no byte is live. -/
theorem heap_empty (ho : FOwned own rO m) (h0 : ∀ u < m.threads.size, (own u).owned = Heap.empty)
    (hO : rO.owned = Heap.empty) : m.heap = Heap.empty := by
  funext l
  cases hl : m.heap l with
  | none => rfl
  | some c =>
    rcases ho.cover hl with ⟨u, hu, hn⟩ | hn
    · rw [h0 u hu] at hn; exact absurd rfl hn
    · rw [hO] at hn; exact absurd rfl hn

end FOwned

/-- The start memory `{}` has no byte. -/
theorem fheap_empty_mem : ({} : Mem).fheap = FHeap.empty := by
  funext ⟨b, o⟩; simp [Mem.fheap, Mem.heap, FHeap.empty]

theorem FAssn.sep_ex_ex_lift {R : FAssn} {φ : Nat → BlockId → Prop} {P : Nat → BlockId → FAssn}
    {r : Res} (h : (R ⋆ FAssn.ex fun A => FAssn.ex fun b => ⟪φ A b⟫ ⋆ P A b) r) :
    ∃ A b, φ A b ∧ (R ⋆ P A b) r := by
  obtain ⟨r₁, r₂, hd, e, hr, A, b, hp⟩ := h
  obtain ⟨hφ, hp⟩ := sep_lift.mp hp
  exact ⟨A, b, hφ, r₁, r₂, hd, e, hr, hp⟩

end Full

/-! ## In a thread -/

namespace Conc
namespace Proto

open Full

variable {Tgt γ σ α : Type} {P : Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ} {m : Mem}
  {n : Nat} {own : ThreadId → Res} {rO : Res}

/-- **A `MemM` step of thread `t`** with a thread triple on its part `own t`: after it, `t`'s part
is the triple's post, the other parts and `rO` are unchanged, and the step is one of `t`'s
(`FStepIn`: the threads, the groups, the futex queue, … stay). A protocol that counts turns in
strict mode (`Proto.Partial` fails) needs the step to return (`FTTReturns`: the second half of an
`FTTotalTriple`). -/
theorem WP.liftMem_fownedS {x : MemM α} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r' hF, (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' →
      Qa a r' → FStepIn hF m m' → Q a G m' n)
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
  have hcs : m.FConc := ⟨by rw [hc, ho.csize]; exact htl, ho.conc.1, ho.conc.2.1⟩
  -- the step runs with the running thread's token in its frame, so its post holds none
  have hx := ht m (own t) _ (hh.addCurF (ho.part_noCur hR)) hp hcs (hc ▸ ho.owns t htl)
  refine WP.liftMem' (fun e he => ?_) (fun a m' hr => ?_) fun hn => hret.resolve_right fun hr => ?_
  · rw [he] at hx; exact .inr hx
  · rw [hr] at hx
    obtain ⟨r', hh', hq, hc', ho', hs⟩ := hx
    obtain ⟨hnc, hh'⟩ := hh'.dropCurF
    rw [Res.owned_addGh, Res.shared_addGh] at hs
    exact ⟨by rw [hs.threads], h a m' r' _ hr (ho.step hc htl hR hRO hh' hc' ho' hs hnc) hq hs.unread⟩
  · obtain ⟨v, m', e⟩ := hr m (own t) _ hh hp hcs (hc ▸ ho.owns t htl)
    rw [e] at hn; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at hn

/-- A resource with `cur t` added. -/
theorem _root_.Zig.Full.sep_cur_intro {R : FAssn} {r : Res} {t : ThreadId} (h : R r) :
    (R ⋆ cur t) ⟨r.heap, r.know, r.gh.add (Ghost.cur t)⟩ :=
  ⟨r, ⟨FHeap.empty, Know.none, Ghost.cur t⟩, fun _ => .inr rfl,
    by simp [FHeap.union_empty, Know.union_none], h, rfl, rfl, rfl⟩

/-- A cur-aware local step with the ACTUAL protocol rest as its protected footprint.
The running token exists only inside this step; other parts and the complete rest stay
framed, including their stack resources. -/
theorem WP.liftMem_fownedCurR {x : MemM α} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTriple (Pa ⋆ cur t) x (fun a => Qa a ⋆ cur t))
    (ho : FOwned own rO m) (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' →
      Qa a r' → FStepIn rO.owned m m' rO.shared → Q a G m' n)
    (hret : P.Partial ∨ FTTReturns (Pa ⋆ cur t) x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n := by
  obtain ⟨rR, hR, hRO, hh⟩ := ho.part htl
  have hcs : m.FConc := ⟨by rw [hc, ho.csize]; exact htl, ho.conc.1, ho.conc.2.1⟩
  have hh₁ := hh.addCur (ho.part_noCur hR)
  rw [hc] at hh₁
  have hp₁ := sep_cur_intro (t := t) hp
  have hx := ht m _ _ hh₁ hp₁ hcs (by rw [Mem.OwnsRes.addGh_iff, hc]; exact ho.owns t htl)
  refine WP.liftMem' (fun e he => ?_) (fun a m' hr => ?_) fun hn => hret.resolve_right fun hr => ?_
  · rw [he] at hx; exact .inr hx
  · rw [hr] at hx
    obtain ⟨r', hh', hq, hc', ho', hs⟩ := hx
    obtain ⟨r₁, r₂, hd, rfl, hq₁, h0, k0, g0⟩ := hq
    have hsp := Holds.split hd hh'
    have e : (⟨r₂.heap ∪ (rR.heap ∪ rO.heap), r₂.know.union (rR.know.union rO.know),
        r₂.gh.add (rR.gh.add rO.gh)⟩ : Res) = ⟨rR.heap ∪ rO.heap, rR.know.union rO.know,
          (rR.gh.add rO.gh).add (Ghost.cur t)⟩ := by
      rw [h0, k0, g0, Ghost.add_comm]; simp [FHeap.empty_union, Know.none_union]
    rw [e] at hsp
    obtain ⟨hnc, hh₂⟩ := Holds.dropCurF
      (rF := ⟨rR.heap ∪ rO.heap, rR.know.union rO.know, rR.gh.add rO.gh⟩) hsp
    have ho₂ : m'.OwnsRes m'.current r₁ := ho'.sepL rfl rfl
    exact ⟨by rw [hs.threads],
      h a m' r₁ hr (ho.step hc htl hR hRO hh₂ hc' ho₂ hs hnc) hq₁
        (hs.weakenR (fun _ hl => (Res.owned_sep rfl rfl).mpr (.inr hl))
          fun _ hl hr => Res.shared_sep' rfl rfl hr hl)⟩
  · obtain ⟨v, m', e⟩ := hr m _ _ hh₁ hp₁ hcs (by rw [Mem.OwnsRes.addGh_iff, hc]; exact ho.owns t htl)
    rw [e] at hn; simp [pure, ExceptT.pure, ExceptT.mk, ExceptT.run] at hn

/-- A local step that temporarily receives `cur t`, with an abstract protected footprint.
The exact-rest form is `WP.liftMem_fownedCurR`; this interface needs only some footprint. -/
theorem WP.liftMem_fownedCurS {x : MemM α} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTriple (Pa ⋆ cur t) x (fun a => Qa a ⋆ cur t))
    (ho : FOwned own rO m) (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r' hF, (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' →
      Qa a r' → FStepIn hF m m' → Q a G m' n)
    (hret : P.Partial ∨ FTTReturns (Pa ⋆ cur t) x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n :=
  WP.liftMem_fownedCurR ht ho hc htl hp
    (fun a m' r' hr ho' hq hs => h a m' r' _ hr ho' hq hs.unread) hret

/-- `WP.liftMem_fownedS` with the step's protocol-field equalities and its actual frame relation.
The atomic relation is `FStepIn.atomics` (`AMap`), not equality of the atomic arrays. -/
theorem WP.liftMem_fowned {x : MemM α} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r' hF, (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' → Qa a r' →
      m'.current = t → m'.threads = m.threads → m'.waiters = m.waiters →
      m'.woken = m.woken → m'.groups = m.groups → m'.clocks.size = m.clocks.size →
      FStepIn hF m m' → Q a G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t (ConcM.liftMem x : ConcM Tgt α) Q G m n :=
  WP.liftMem_fownedS ht ho hc htl hp (fun a m' r' hF hr ho' hq hs =>
    h a m' r' hF hr ho' hq (hs.current.trans hc) hs.threads hs.waiters hs.woken
      hs.groups hs.size hs) hret

/-- `WP.liftMem_fownedS` for a call of a `MemM` function (`callMC`). -/
theorem WP.callMC_fownedS {x : MemM α} {s : σ} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r' hF, (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' →
      Qa a r' → FStepIn hF m m' → Q (a, s) G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t ((Zig.callMC x : CM Tgt σ α).run s) Q G m n := by
  show P.WP t (ConcM.liftMem x >>= fun a => pure (a, s)) Q G m n
  exact WP.bind (WP.liftMem_fownedS ht ho hc htl hp (fun a m' r' hF hr ho' hq hs =>
    WP.pure' (h a m' r' hF hr ho' hq hs)) hret)

/-- `WP.liftMem_fowned` for a step of generated code (`liftM`). -/
theorem WP.liftM_fowned {x : MemM α} {s : σ} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' → Qa a r' →
      m'.current = t → m'.threads = m.threads → Q (a, s) G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t ((_root_.liftM x : CM Tgt σ α).run s) Q G m n :=
  WP.callMC_fownedS ht ho hc htl hp (fun a m' r' _ hr ho' hq hs =>
    h a m' r' hr ho' hq (hs.current.trans hc) hs.threads) hret

/-- `WP.liftMem_fowned` for a call of a `MemM` function (`callMC`). -/
theorem WP.callMC_fowned {x : MemM α} {s : σ} {Pa : FAssn} {Qa : α → FAssn}
    {Q : α × σ → (ThreadId → γ) → Mem → Nat → Prop} (ht : FTTriple Pa x Qa) (ho : FOwned own rO m)
    (hc : m.current = t) (htl : t < m.threads.size) (hp : Pa (own t))
    (h : ∀ a m' r', (x.run m).run = some (.ok (a, m')) → FOwned (upd own t r') rO m' → Qa a r' →
      m'.current = t → m'.threads = m.threads → Q (a, s) G m' n)
    (hret : P.Partial ∨ FTTReturns Pa x := by
      first
        | exact .inl (.inl rfl)
        | exact .inl (.inr rfl)
        | assumption
        | exact .inl (by assumption)
        | exact .inl (.inr (by assumption))
        | exact .inl (.inl (by assumption))) :
    P.WP t ((Zig.callMC x : CM Tgt σ α).run s) Q G m n :=
  WP.liftM_fowned ht ho hc htl hp h hret

end Proto
end Conc

end Zig
