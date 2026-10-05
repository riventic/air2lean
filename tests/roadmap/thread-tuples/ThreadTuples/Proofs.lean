import ThreadTuples.Gen
import ZigLean.Conc.Csl

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

end ThreadTuples.Proofs
