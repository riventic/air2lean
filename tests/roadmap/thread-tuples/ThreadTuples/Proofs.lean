import ThreadTuples.Gen
import ZigLean.Sep.Full.ThreadSpawn

open Zig Zig.Conc Zig.Full Zig.Full.FAssn
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
  privateRes : Res

def protocol (grant : ThreadTuples.Tgt → FAssn) : Proto ThreadTuples.Tgt Ghost where
  inv := fun G m => ∃ rO, FOwned (fun u => (G u).privateRes) rO m
  init := fun target g => g.captured = target ∧ grant target g.privateRes
  fin := fun _ => True

theorem mixed_init (grant : ThreadTuples.Tgt → FAssn)
    (first second : BitVec 32) (out other : Ptr) (g : Ghost) :
    ThreadTuples.Tgt.spawnInit (protocol grant)
      (.mixedWorker (first, out, second, other)) g ↔
    g.captured = .mixedWorker (first, out, second, other) ∧
      grant (.mixedWorker (first, out, second, other)) g.privateRes := by rfl

theorem atomic_init (grant : ThreadTuples.Tgt → FAssn)
    (out shared : Ptr) (first second : BitVec 32) (g : Ghost) :
    ThreadTuples.Tgt.spawnInit (protocol grant)
      (.atomicWorker (out, shared, first, second)) g ↔
    g.captured = .atomicWorker (out, shared, first, second) ∧
      grant (.atomicWorker (out, shared, first, second)) g.privateRes := by rfl

-- The ownership transfer requires an explicit disjoint split of the parent's part.
-- A shared atomic cell belongs to the global invariant rather than both private parts.
theorem explicit_fork {own : ThreadId → Res} {rO : Res} {m m' : Mem} {t c : ThreadId}
    {keep child : Res} (ho : FOwned own rO m) (ht : t < m.threads.size)
    (hsplit : own t = rsum keep child) (hd : FHeap.Disjoint keep.heap child.heap)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    FOwned (upd (upd own t keep) c child) rO m' :=
  FOwned.fork ho ht hsplit hd hf

-- These concrete grants tie the captured pointer fields to the transferred resources.
def mixedGrant : ThreadTuples.Tgt → FAssn
  | .mixedWorker (_, out, _, other), h =>
      (up (pts out 4 (0#32)) ⋆ up (pts other 4 (0#32))) h
  | _, _ => False

def atomicGrant (sharedPart : FHeap) (sharedPointer : Ptr) : ThreadTuples.Tgt → FAssn
  | .atomicWorker (out, shared, _, _), h =>
      up (pts out 4 (0#32)) h ∧ shared = sharedPointer ∧ FHeap.Disjoint h.heap sharedPart
  | _, _ => False

theorem mixed_fork {own : ThreadId → Res} {rO : Res} {m m' : Mem} {t c : ThreadId}
    {keep child : Res} (first second : BitVec 32) (out other : Ptr)
    (ho : FOwned own rO m) (ht : t < m.threads.size)
    (hsplit : own t = rsum keep child) (hd : FHeap.Disjoint keep.heap child.heap)
    (houtputs : (up (pts out 4 (0#32)) ⋆ up (pts other 4 (0#32))) child)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    FOwned (upd (upd own t keep) c child) rO m' ∧
      ThreadTuples.Tgt.spawnInit (protocol mixedGrant)
        (.mixedWorker (first, out, second, other))
        { captured := .mixedWorker (first, out, second, other), privateRes := child } := by
  exact ⟨FOwned.fork ho ht hsplit hd hf, rfl, houtputs⟩

-- The child receives its ordinary output only. The shared atomic resource is disjoint
-- from that private heap and must be governed by the application's global invariant.
theorem atomic_fork {own : ThreadId → Res} {rO : Res} {m m' : Mem} {t c : ThreadId}
    {keep child : Res} {sharedPart : FHeap} (out shared : Ptr) (first second : BitVec 32)
    (ho : FOwned own rO m) (ht : t < m.threads.size)
    (hsplit : own t = rsum keep child) (hd : FHeap.Disjoint keep.heap child.heap)
    (houtput : up (pts out 4 (0#32)) child) (hshared : FHeap.Disjoint child.heap sharedPart)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    FOwned (upd (upd own t keep) c child) rO m' ∧
      ThreadTuples.Tgt.spawnInit (protocol (atomicGrant sharedPart shared))
        (.atomicWorker (out, shared, first, second))
        { captured := .atomicWorker (out, shared, first, second), privateRes := child } := by
  exact ⟨FOwned.fork ho ht hsplit hd hf, rfl, houtput, rfl, hshared⟩

/-! ## Generated per-argument ownership obligations

`Tgt.captures` is generated from the AIR capture types. Copied values carry no obligation;
every pointer must be handed over (`FTransfer.owned`) or shown to be shared (`FTransfer.shared`). -/

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
def ownedProtocol (mode : Ptr → FTransfer) : Proto ThreadTuples.Tgt Ghost where
  inv := fun G m => ∃ rO, FOwned (fun u => (G u).privateRes) rO m
  init := fun target g => g.captured = target ∧
    FCapture.grant mode (ThreadTuples.Tgt.captures target) g.privateRes
  fin := fun _ => True

/-- Value + pointer + atomic: the worker's output cell moves to the child, the atomic stays in
a part that no thread holds, and the two copied values add nothing. -/
theorem atomic_spawn {own : ThreadId → Res} {rO : Res} {m m' : Mem} {t c : ThreadId}
    {keep child : Res} {sharedPart : FHeap} {mode : Ptr → FTransfer} (out shared : Ptr)
    (first second : BitVec 32)
    (hout : mode out = .owned (up (pts out 4 (0#32)))) (hshared : mode shared = .shared sharedPart)
    (ho : FOwned own rO m) (ht : t < m.threads.size)
    (hsplit : own t = rsum keep child) (hd : FHeap.Disjoint keep.heap child.heap)
    (houtput : up (pts out 4 (0#32)) child) (hdisj : FHeap.Disjoint child.heap sharedPart)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    FOwned (upd (upd own t keep) c child) rO m' ∧
      ThreadTuples.Tgt.spawnInit (ownedProtocol mode)
        (.atomicWorker (out, shared, first, second))
        { captured := .atomicWorker (out, shared, first, second), privateRes := child } := by
  have hc : FCapture.cells mode (.ptr out) child := by
    rw [FCapture.cells_ptr hout]; exact houtput
  have hs : FCapture.cells mode (.ptr shared) rnil := by
    rw [FCapture.cells_ptr hshared]; exact ⟨rfl, rfl, rfl⟩
  have hcells : FCapture.cellsOf mode [.ptr out, .ptr shared, .value, .value] child := by
    simpa only [rsum_rnil] using FCapture.cellsOf_cons (FHeap.disjoint_empty child.heap) hc
      (FCapture.cellsOf_cons_empty hs (FCapture.cellsOf_value
        (FCapture.cellsOf_value FCapture.cellsOf_nil)))
  have hex : ∀ c ∈ ([.ptr out, .ptr shared, .value, .value] : List Capture),
      FCapture.excludes mode c child := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · rw [FCapture.excludes_ptr hout]; trivial
    · rw [FCapture.excludes_ptr hshared]; exact hdisj
    · trivial
    · trivial
  exact ⟨(FCapture.fork_grant ho ht hsplit hd ⟨hcells, hex⟩ hf).1, rfl, hcells, hex⟩

/-- Value + pointer + value + pointer: both output cells move to the child. -/
theorem mixed_spawn {own : ThreadId → Res} {rO : Res} {m m' : Mem} {t c : ThreadId}
    {keep outCell otherCell : Res} {mode : Ptr → FTransfer} (first second : BitVec 32)
    (out other : Ptr)
    (hout : mode out = .owned (up (pts out 4 (0#32))))
    (hother : mode other = .owned (up (pts other 4 (0#32))))
    (ho : FOwned own rO m) (ht : t < m.threads.size)
    (hsplit : own t = rsum keep (rsum outCell otherCell))
    (hd : FHeap.Disjoint keep.heap (outCell.heap ∪ otherCell.heap)) (hcells : FHeap.Disjoint outCell.heap otherCell.heap)
    (hpo : up (pts out 4 (0#32)) outCell) (hpt : up (pts other 4 (0#32)) otherCell)
    (hf : (Thread.fork.run { m with current := t }).run = some (.ok (c, m'))) :
    FOwned (upd (upd own t keep) c (rsum outCell otherCell)) rO m' ∧
      ThreadTuples.Tgt.spawnInit (ownedProtocol mode)
        (.mixedWorker (first, out, second, other))
        { captured := .mixedWorker (first, out, second, other),
          privateRes := rsum outCell otherCell } := by
  have ho' : FCapture.cells mode (.ptr out) outCell := by
    rw [FCapture.cells_ptr hout]; exact hpo
  have ht' : FCapture.cells mode (.ptr other) otherCell := by
    rw [FCapture.cells_ptr hother]; exact hpt
  have hgrant : FCapture.grant mode [.value, .ptr out, .value, .ptr other]
      (rsum outCell otherCell) := by
    refine ⟨FCapture.cellsOf_value (FCapture.cellsOf_cons hcells ho'
      (FCapture.cellsOf_value ?_)), ?_⟩
    · simpa only [rsum_rnil] using
        FCapture.cellsOf_cons (FHeap.disjoint_empty otherCell.heap) ht' FCapture.cellsOf_nil
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · trivial
      · rw [FCapture.excludes_ptr hout]; trivial
      · trivial
      · rw [FCapture.excludes_ptr hother]; trivial
  exact ⟨(FCapture.fork_grant ho ht hsplit hd hgrant hf).1, rfl, hgrant⟩

/-- Join: the parent regains every cell the joined worker holds, including its outputs. -/
theorem worker_join {own : ThreadId → Res} {rO : Res} {m m' : Mem} {t u : ThreadId}
    (ho : FOwned own rO m) (ht : t < m.threads.size) (hut : u ≠ t)
    (hj : ((Thread.join u).run { m with current := t }).run = some (.ok ((), m'))) :
    ∀ l fc, (own u).heap l = some fc →
      (upd (upd own u rnil) t (rsum (own t) (own u)) t).heap l = some fc :=
  (FCapture.join_regain ho ht hut hj).2

theorem pts_cell {p : Ptr} {a : Nat} {v : BitVec 32} {h : Res} (hp : up (pts p a v) h) :
    ∃ b, p.block = some b ∧ h.heap (b, p.off.toNat) ≠ none := by
  obtain ⟨A, S, K, bs, ⟨-, hsize, -, -⟩, hbytes⟩ := FTotalTriple.up_pts_iff_bytesAt.mp hp
  obtain ⟨b, hb, -⟩ := hbytes.1
  obtain ⟨fc, hfc, -⟩ := up_bytesAt_cell hbytes hb (j := 0) (by rw [hsize]; decide)
  refine ⟨b, hb, ?_⟩
  simpa only [Nat.add_zero] using (Option.ne_none_iff_exists'.mpr ⟨fc, hfc⟩)

/-- Negative: a parent cannot hand over an output cell that another thread `u` already holds
(for example reusing `left` for the second atomic worker). The generated obligation for the
captured `out` pointer has no discharge. -/
theorem reused_output_rejected {own : ThreadId → Res} {rO : Res} {m : Mem} {t u : ThreadId}
    {mode : Ptr → FTransfer} {held : Res} {v w : BitVec 32} (out shared : Ptr)
    (first second : BitVec 32) (hout : mode out = .owned (up (pts out 4 v)))
    (ho : FOwned own rO m) (hut : u ≠ t) (hheld : up (pts out 4 w) held)
    (hsub : ∀ l fc, held.heap l = some fc → (own u).heap l = some fc) :
    ¬ ∃ keep child, own t = rsum keep child ∧
      FCapture.grant mode
        (ThreadTuples.Tgt.captures (.atomicWorker (out, shared, first, second))) child := by
  refine FCapture.not_grant_of_unowned (c := .ptr out) (by simp [atomic_captures]) ?_
  intro h hc
  have hp : up (pts out 4 v) h := by rwa [FCapture.cells_ptr hout] at hc
  obtain ⟨b, hb, hl⟩ := pts_cell hp
  obtain ⟨b', hb', hl'⟩ := pts_cell hheld
  rw [hb] at hb'
  cases hb'
  refine ⟨_, hl, ?_⟩
  have hne : (own u).heap (b, out.off.toNat) ≠ none := by
    obtain ⟨fc, hfc⟩ := Option.ne_none_iff_exists'.mp hl'
    rw [hsub _ _ hfc]
    simp
  exact (ho.disj_any (Ne.symm hut) _).resolve_right hne

/-- Negative: a parent with an empty part owns no cell to hand over. -/
theorem unowned_output_rejected {mode : Ptr → FTransfer} {v : BitVec 32}
    (first second : BitVec 32) (out other : Ptr) (hout : mode out = .owned (up (pts out 4 v))) :
    ¬ ∃ keep child, rnil = rsum keep child ∧
      FCapture.grant mode
        (ThreadTuples.Tgt.captures (.mixedWorker (first, out, second, other))) child := by
  refine FCapture.not_grant_of_unowned (c := .ptr out) (by simp [mixed_captures]) ?_
  intro h hc
  have hp : up (pts out 4 v) h := by rwa [FCapture.cells_ptr hout] at hc
  obtain ⟨b, -, hl⟩ := pts_cell hp
  exact ⟨_, hl, rfl⟩

end ThreadTuples.Proofs
