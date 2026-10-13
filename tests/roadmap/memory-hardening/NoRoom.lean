import ZigLean.Sep.Full.Init

/-! O-H / STK-01 regression: a stack block without room in the address space.

`Zig.alloc` never places a block above `Placement.addrLimit`. Without room (`Mem.roomFor`) the
run is not stuck: it throws `.stackOverflow`, the outcome of an exhausted stack budget (premise
STK-01). Partial triples read that outcome as they read a run that does not terminate; a total
triple excludes it, so a total statement that allocates needs room. No assertion states that room
yet (the stack-depth resource, `sp` tokens from `Mem.withStack`, will); until then such a
statement is partial and takes the start-memory run premise of `FTriple.run_init_ok`
(`ZigLean/Sep/Full/Init.lean`). Checked: (1) the run's outcome, (2) no total triple, not even at
program start (the memory without room is a start memory), (3) the outcome is the differential
harness's `stack_overflow` (`Zig.Error.stackOverflow`, `tests/diff/Outcome.lean` `errorKind`,
`scripts/diff-report.py`). -/

open Zig Zig.Full Zig.Full.FAssn

/-- A placement whose address space ends at 4096: no block fits. -/
def noRoom : Placement := { propose := fun _ => none, addrLimit := 4096 }

/-- (1) The allocation has an outcome: `.stackOverflow`. -/
theorem alloc_noRoom_outcome :
    ((allocStack 8 8).run (Mem.ofGlobals noRoom [])).run = some (.error .stackOverflow) :=
  alloc_run_noRoom _ (by decide)

-- The outcome as the model runner prints it (`legacy` line `{"fail":"Zig.Error.stackOverflow"}`).
#guard (match ((allocStack 8 8).run (Mem.ofGlobals noRoom [])).run with
  | some (.error e) => reprStr e | _ => "") == "Zig.Error.stackOverflow"

/-- (2) No total triple of a stack allocation holds: the program-start memory without globals
under `noRoom` holds `emp`, and the run from it throws. -/
theorem alloc_not_total : ¬ FTotalTriple emp (allocStack 8 8) (fun _ => emp) := fun ht => by
  obtain ⟨v, m', -, hr, -⟩ :=
    FTotalTriple.run_init noRoom [] (by decide) nofun (ht.pre fun _ h => h)
  have := alloc_noRoom_outcome
  rw [hr] at this
  cases this

#print axioms alloc_noRoom_outcome
#print axioms alloc_not_total
