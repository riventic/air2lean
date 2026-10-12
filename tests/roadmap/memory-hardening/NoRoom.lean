import ZigLean.Sep.Total
import ZigLean.Sep.Block
import ZigLean.Sep.Full.Triple

/-! O-H / STK-01 regression: a stack block without room in the address space.

`Zig.alloc` never places a block above `Placement.addrLimit`. Without room (`Mem.roomFor`) the
run is not stuck: it throws `.stackOverflow`, the outcome of an exhausted stack budget (premise
STK-01). Partial triples read that outcome as they read a run that does not terminate; a total
triple excludes it, so a total statement that allocates needs room (`TotalTripleIn`, e.g.
`tests/roadmap/alloc-fba` `client_spec`). Checked: (1) the run's outcome, (2) no
total triple over every memory, (3) the outcome is the differential harness's `stack_overflow`
(`Zig.Error.stackOverflow`, `tests/diff/Outcome.lean` `errorKind`, `scripts/diff-report.py`). -/

open Zig Zig.Assn

/-- A memory whose address space ends at 4096: no block fits. -/
def noRoomMem : Mem := { place := { propose := fun _ => none, addrLimit := 4096 } }

theorem noRoomMem_heap : noRoomMem.heap = Heap.empty := by funext l; simp [Mem.heap, noRoomMem]; rfl

/-- (1) The allocation has an outcome: `.stackOverflow`. -/
theorem alloc_noRoom_outcome :
    ((allocStack 8 8).run noRoomMem).run = some (.error .stackOverflow) :=
  alloc_run_noRoom _ (by decide)

-- The outcome as the model runner prints it (`legacy` line `{"fail":"Zig.Error.stackOverflow"}`).
#guard (match ((allocStack 8 8).run noRoomMem).run with
  | some (.error e) => reprStr e | _ => "") == "Zig.Error.stackOverflow"

/-- (2) No total triple of a stack allocation holds over every memory. -/
theorem alloc_not_total : ¬ TotalTriple emp (allocStack 8 8) (fun _ => emp) := by
  intro h
  obtain ⟨v, m', hQ, hr, -⟩ := h noRoomMem Heap.empty Heap.empty (Heap.disjoint_empty _)
    (by rw [noRoomMem_heap, Heap.empty_union]) rfl ⟨singleThread_empty rfl (by decide)⟩
  have := alloc_noRoom_outcome
  rw [hr] at this
  cases this

#print axioms alloc_noRoom_outcome
#print axioms alloc_not_total
