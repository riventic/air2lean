import ThreadTuples.Gen
import ZigLean.Conc.Csl
import ZigLean.Conc.Transfer

open Zig Zig.Conc
namespace ThreadTuples.Proofs

-- These equalities inspect the generated dispatcher, including every captured pointer.
theorem zero_dispatch : ThreadTuples.dispatch (.zeroWorker ()) =
    discard (ConcM.liftMem (StateT.lift ThreadTuples.zeroWorker)) := by rfl

theorem generic_zero_dispatch : ThreadTuples.dispatch (.ZeroWorker_u8_run ()) =
    discard (ConcM.liftMem (StateT.lift ThreadTuples.ZeroWorker_u8_run)) := by rfl

theorem mixed_dispatch (first second : BitVec 32) (out other : Ptr) :
    ThreadTuples.dispatch (.mixedWorker (first, out, second, other)) =
      discard (ConcM.liftMem (ThreadTuples.mixedWorker first out second other)) := by rfl

theorem copied_dispatch (out : Ptr) (first second third : BitVec 32) :
    ThreadTuples.dispatch (.copyWorker (out, first, second, third)) =
      discard (ConcM.liftMem (ThreadTuples.copyWorker out first second third)) := by rfl

theorem atomic_dispatch (out shared : Ptr) (first second : BitVec 32) :
    ThreadTuples.dispatch (.atomicWorker (out, shared, first, second)) =
      discard (ThreadTuples.atomicWorker out shared first second) := by rfl

-- A protocol obligation receives the full tuple. It can distinguish private pointer
-- resources from shared atomic state; capture alone does not establish exclusivity.
structure Ghost where
  captured : ThreadTuples.Tgt
  privateHeap : Heap

def protocol (grant : ThreadTuples.Tgt → Heap → Prop) : Proto ThreadTuples.Tgt Ghost where
  inv := fun G m => Owned (fun u => (G u).privateHeap) m
  init := fun target g => g.captured = target ∧ grant target g.privateHeap
  fin := fun _ => True

theorem mixed_init (grant : ThreadTuples.Tgt → Heap → Prop)
    (first second : BitVec 32) (out other : Ptr) (g : Ghost) :
    ThreadTuples.Tgt.spawnInit (protocol grant)
      (.mixedWorker (first, out, second, other)) g ↔
    g.captured = .mixedWorker (first, out, second, other) ∧
      grant (.mixedWorker (first, out, second, other)) g.privateHeap := by rfl

theorem atomic_init (grant : ThreadTuples.Tgt → Heap → Prop)
    (out shared : Ptr) (first second : BitVec 32) (g : Ghost) :
    ThreadTuples.Tgt.spawnInit (protocol grant)
      (.atomicWorker (out, shared, first, second)) g ↔
    g.captured = .atomicWorker (out, shared, first, second) ∧
      grant (.atomicWorker (out, shared, first, second)) g.privateHeap := by rfl

-- The ownership transfer requires an explicit disjoint split of the parent's part.
-- A shared atomic cell belongs to the global invariant rather than both private parts.
theorem explicit_fork {own : ThreadId → Heap} {m m' : Mem} {t c : ThreadId}
    {keep child : Heap} (ho : Owned own m) (ht : t < m.threads.size)
    (hsplit : own t = keep ∪ child) (hd : Heap.Disjoint keep child)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    Owned (upd (upd own t keep) c child) m' :=
  Owned.fork ho ht hsplit hd hf

-- These concrete grants tie the captured pointer fields to the transferred resources.
def mixedGrant : ThreadTuples.Tgt → Heap → Prop
  | .mixedWorker (_, out, _, other), h =>
      Assn.sep (pts out 4 (0#32)) (pts other 4 (0#32)) h
  | _, _ => False

def atomicGrant (sharedPart : Heap) (sharedPointer : Ptr) : ThreadTuples.Tgt → Heap → Prop
  | .atomicWorker (out, shared, _, _), h =>
      pts out 4 (0#32) h ∧ shared = sharedPointer ∧ Heap.Disjoint h sharedPart
  | _, _ => False

theorem mixed_fork {own : ThreadId → Heap} {m m' : Mem} {t c : ThreadId}
    {keep child : Heap} (first second : BitVec 32) (out other : Ptr)
    (ho : Owned own m) (ht : t < m.threads.size)
    (hsplit : own t = keep ∪ child) (hd : Heap.Disjoint keep child)
    (houtputs : Assn.sep (pts out 4 (0#32)) (pts other 4 (0#32)) child)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    Owned (upd (upd own t keep) c child) m' ∧
      ThreadTuples.Tgt.spawnInit (protocol mixedGrant)
        (.mixedWorker (first, out, second, other))
        { captured := .mixedWorker (first, out, second, other), privateHeap := child } := by
  exact ⟨Owned.fork ho ht hsplit hd hf, rfl, houtputs⟩

-- The child receives its ordinary output only. The shared atomic resource is disjoint
-- from that private heap and must be governed by the application's global invariant.
theorem atomic_fork {own : ThreadId → Heap} {m m' : Mem} {t c : ThreadId}
    {keep child sharedPart : Heap} (out shared : Ptr) (first second : BitVec 32)
    (ho : Owned own m) (ht : t < m.threads.size)
    (hsplit : own t = keep ∪ child) (hd : Heap.Disjoint keep child)
    (houtput : pts out 4 (0#32) child) (hshared : Heap.Disjoint child sharedPart)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    Owned (upd (upd own t keep) c child) m' ∧
      ThreadTuples.Tgt.spawnInit (protocol (atomicGrant sharedPart shared))
        (.atomicWorker (out, shared, first, second))
        { captured := .atomicWorker (out, shared, first, second), privateHeap := child } := by
  exact ⟨Owned.fork ho ht hsplit hd hf, rfl, houtput, rfl, hshared⟩

/-! ## Generated per-argument ownership obligations

`Tgt.captures` is generated from the AIR capture types. Copied values carry no obligation;
every pointer must be handed over (`Transfer.owned`) or shown to be shared (`Transfer.shared`). -/

theorem zero_captures : ThreadTuples.Tgt.captures (.zeroWorker ()) = [] := rfl

theorem mixed_captures (first second : BitVec 32) (out other : Ptr) :
    ThreadTuples.Tgt.captures (.mixedWorker (first, out, second, other)) =
      [.value, .ptr out, .value, .ptr other] := rfl

theorem copied_captures (out : Ptr) (first second third : BitVec 32) :
    ThreadTuples.Tgt.captures (.copyWorker (out, first, second, third)) =
      [.ptr out, .value, .value, .value] := rfl

theorem atomic_captures (out shared : Ptr) (first second : BitVec 32) :
    ThreadTuples.Tgt.captures (.atomicWorker (out, shared, first, second)) =
      [.ptr out, .ptr shared, .value, .value] := rfl

/-- The child's ghost heap must discharge the generated obligation for its whole capture. -/
def ownedProtocol (mode : Ptr → Transfer) : Proto ThreadTuples.Tgt Ghost where
  inv := fun G m => Owned (fun u => (G u).privateHeap) m
  init := fun target g => g.captured = target ∧
    Capture.grant mode (ThreadTuples.Tgt.captures target) g.privateHeap
  fin := fun _ => True

/-- Value + pointer + atomic: the worker's output cell moves to the child, the atomic stays in
a part that no thread holds, and the two copied values add nothing. -/
theorem atomic_spawn {own : ThreadId → Heap} {m m' : Mem} {t c : ThreadId}
    {keep child sharedPart : Heap} {mode : Ptr → Transfer} (out shared : Ptr)
    (first second : BitVec 32)
    (hout : mode out = .owned (pts out 4 (0#32))) (hshared : mode shared = .shared sharedPart)
    (ho : Owned own m) (ht : t < m.threads.size)
    (hsplit : own t = keep ∪ child) (hd : Heap.Disjoint keep child)
    (houtput : pts out 4 (0#32) child) (hdisj : Heap.Disjoint child sharedPart)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    Owned (upd (upd own t keep) c child) m' ∧
      ThreadTuples.Tgt.spawnInit (ownedProtocol mode)
        (.atomicWorker (out, shared, first, second))
        { captured := .atomicWorker (out, shared, first, second), privateHeap := child } := by
  have hc : (Capture.ptr out).cells mode child := by
    rw [Capture.cells_ptr hout]; exact houtput
  have hs : (Capture.ptr shared).cells mode Heap.empty := by
    rw [Capture.cells_ptr hshared]; rfl
  have hcells : Capture.cellsOf mode [.ptr out, .ptr shared, .value, .value] child := by
    simpa using Capture.cellsOf_cons (Heap.disjoint_empty child) hc
      (Capture.cellsOf_cons_empty hs (Capture.cellsOf_value
        (Capture.cellsOf_value Capture.cellsOf_nil)))
  have hex : ∀ c ∈ ([.ptr out, .ptr shared, .value, .value] : List Capture),
      c.excludes mode child := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · rw [Capture.excludes_ptr hout]; trivial
    · rw [Capture.excludes_ptr hshared]; exact hdisj
    · trivial
    · trivial
  exact ⟨(Capture.fork_grant ho ht hsplit hd ⟨hcells, hex⟩ hf).1, rfl, hcells, hex⟩

/-- Value + pointer + value + pointer: both output cells move to the child. -/
theorem mixed_spawn {own : ThreadId → Heap} {m m' : Mem} {t c : ThreadId}
    {keep outCell otherCell : Heap} {mode : Ptr → Transfer} (first second : BitVec 32)
    (out other : Ptr)
    (hout : mode out = .owned (pts out 4 (0#32)))
    (hother : mode other = .owned (pts other 4 (0#32)))
    (ho : Owned own m) (ht : t < m.threads.size)
    (hsplit : own t = keep ∪ (outCell ∪ otherCell))
    (hd : Heap.Disjoint keep (outCell ∪ otherCell)) (hcells : Heap.Disjoint outCell otherCell)
    (hpo : pts out 4 (0#32) outCell) (hpt : pts other 4 (0#32) otherCell)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    Owned (upd (upd own t keep) c (outCell ∪ otherCell)) m' ∧
      ThreadTuples.Tgt.spawnInit (ownedProtocol mode)
        (.mixedWorker (first, out, second, other))
        { captured := .mixedWorker (first, out, second, other),
          privateHeap := outCell ∪ otherCell } := by
  have ho' : (Capture.ptr out).cells mode outCell := by
    rw [Capture.cells_ptr hout]; exact hpo
  have ht' : (Capture.ptr other).cells mode otherCell := by
    rw [Capture.cells_ptr hother]; exact hpt
  have hgrant : Capture.grant mode [.value, .ptr out, .value, .ptr other]
      (outCell ∪ otherCell) := by
    refine ⟨Capture.cellsOf_value (Capture.cellsOf_cons hcells ho'
      (Capture.cellsOf_value ?_)), ?_⟩
    · simpa using Capture.cellsOf_cons (Heap.disjoint_empty otherCell) ht' Capture.cellsOf_nil
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · trivial
      · rw [Capture.excludes_ptr hout]; trivial
      · trivial
      · rw [Capture.excludes_ptr hother]; trivial
  exact ⟨(Capture.fork_grant ho ht hsplit hd hgrant hf).1, rfl, hgrant⟩

/-- Join: the parent regains every cell the joined worker holds, including its outputs. -/
theorem worker_join {own : ThreadId → Heap} {m m' : Mem} {t u : ThreadId}
    (ho : Owned own m) (ht : t < m.threads.size) (hut : u ≠ t)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m'))) :
    (own u).Sub (upd (upd own t (own t ∪ own u)) u Heap.empty t) :=
  (Capture.join_regain ho ht hut hj).2

theorem pts_cell {p : Ptr} {a : Nat} {v : BitVec 32} {h : Heap} (hp : pts p a v h) :
    ∃ b, p.block = some b ∧ h (b, p.off.toNat) ≠ none := by
  obtain ⟨A, S, K, bs, -, hsize, -, ⟨b, hb, -, hl⟩, -⟩ := hp
  have hpos : 0 < bs.size := by rw [hsize]; decide
  refine ⟨b, hb, ?_⟩
  simp [hl, hpos]

/-- Negative: a parent cannot hand over an output cell that another thread `u` already holds
(for example reusing `left` for the second atomic worker). The generated obligation for the
captured `out` pointer has no discharge. -/
theorem reused_output_rejected {own : ThreadId → Heap} {m : Mem} {t u : ThreadId}
    {mode : Ptr → Transfer} {held : Heap} {v w : BitVec 32} (out shared : Ptr)
    (first second : BitVec 32) (hout : mode out = .owned (pts out 4 v))
    (ho : Owned own m) (hut : u ≠ t) (hheld : pts out 4 w held) (hsub : held.Sub (own u)) :
    ¬ ∃ keep child, own t = keep ∪ child ∧
      Capture.grant mode
        (ThreadTuples.Tgt.captures (.atomicWorker (out, shared, first, second))) child := by
  refine Capture.not_grant_of_unowned (c := .ptr out) (by simp [atomic_captures]) ?_
  intro h hc
  have hp : pts out 4 v h := by rwa [Capture.cells_ptr hout] at hc
  obtain ⟨b, hb, hl⟩ := pts_cell hp
  obtain ⟨b', hb', hl'⟩ := pts_cell hheld
  rw [hb] at hb'
  cases hb'
  exact ⟨_, hl, ho.hne hut (hsub.ne hl')⟩

/-- Negative: a parent with an empty part owns no cell to hand over. -/
theorem unowned_output_rejected {mode : Ptr → Transfer} {v : BitVec 32}
    (first second : BitVec 32) (out other : Ptr) (hout : mode out = .owned (pts out 4 v)) :
    ¬ ∃ keep child, Heap.empty = keep ∪ child ∧
      Capture.grant mode
        (ThreadTuples.Tgt.captures (.mixedWorker (first, out, second, other))) child := by
  refine Capture.not_grant_of_unowned (c := .ptr out) (by simp [mixed_captures]) ?_
  intro h hc
  have hp : pts out 4 v h := by rwa [Capture.cells_ptr hout] at hc
  obtain ⟨b, -, hl⟩ := pts_cell hp
  exact ⟨_, hl, rfl⟩

end ThreadTuples.Proofs
