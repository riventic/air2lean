import Proofs.Iogroup.Counter

/-!
# Shared reads and join-before-free: model negatives

The all-schedules results are kernel theorems: `ZigLean/Conc/Share.lean` (the contract) and
`Proofs/Iogroup/Counter.lean`'s `groupCounter_safe`/`groupCounter_reclaim` (three tasks
read-share `io`; `main` frees the block only after joining them all). This file checks that the
model rejects freeing while a read share is outstanding.

1. **Kernel, two readers, straight-line semantics.** Two forked readers read one heap region,
   and the owner frees it with `std`'s poisoning `free`. After both joins the free succeeds.
   With one join, or none, the poison write races with the outstanding read (`.illegal`). A read
   after the free is a use after free (`.illegal`).
2. **Runtime, the translated client.** `Zig.loop` is a `partial_fixpoint`, so the kernel does
   not reduce it. These finite assertions run the compiled model of the generated `groupCounter`
   body. Its spawn loop, tasks and `Group.await` are unchanged. Only the reclamation of the
   `Counter` block is mutated. The environment is `Io.Threaded` on 8 CPUs, so each of the three
   `Group.async` tasks gets a thread (`asyncOptions`); with eager tasks no read share would be
   outstanding:
   - heap block, free after `Group.await`: every sampled schedule completes with 3;
   - heap block, free before `Group.await`: every sampled schedule is rejected with `.illegal`
     (a race with an outstanding read, or a use after free);
   - stack block, free before `Group.await`: every sampled schedule is rejected with
     `.illegal`. A stack free records no access, so the rejection is the use after free of a
     task that reads `io` after the free. `main` runs from its third spawn through the free to
     its first join without a stop, so the third task always starts after the free. An earlier
     task that already ended is not detected by a stack free. The client proof therefore
     establishes `RegionOwned` at the free instead of relying on this dynamic check.

These are bounded witnesses over sampled oracles. They do not replace the all-schedules
theorems. No `native_decide` is used.
-/

open Zig Iogroup

/-! ## Kernel: two readers of one heap region -/

/-- Two readers read the 4-byte heap region `p`; the owner joins the first `joins` of them and
frees the region with `std`'s `free` (poison write, then `rawFree`). -/
private def twoReaders (joins : Nat) : MemM Unit := do
  let p ← alloc .heap 4 4
  store 4 p (7 : BitVec 32)
  let r1 ← Thread.fork
  let r2 ← Thread.fork
  modify fun m => { m with current := r1 }
  let _ ← load (BitVec 32) 4 p
  modify fun m => { m with current := r2 }
  let _ ← load (BitVec 32) 4 p
  modify fun m => { m with current := 0 }
  if 1 ≤ joins then Thread.join r1
  if 2 ≤ joins then Thread.join r2
  poisonFree p 4

/-- The owner frees the region before the second reader reads it (`read`: the reader then
reads). -/
private def readAfterFree (read : Bool) : MemM Unit := do
  let p ← alloc .heap 4 4
  store 4 p (7 : BitVec 32)
  let r1 ← Thread.fork
  modify fun m => { m with current := r1 }
  let _ ← load (BitVec 32) 4 p
  modify fun m => { m with current := 0 }
  Thread.join r1
  let r2 ← Thread.fork
  poisonFree p 4
  if read then
    modify fun m => { m with current := r2 }
    let _ ← load (BitVec 32) 4 p

private def outcome (x : MemM Unit) : Option (Except Error Unit) :=
  ((x.run {}).run).map fun r => r.map (·.1)

/-- Both read shares returned (joined): the free is accepted. -/
theorem twoReaders_joined_free_ok : outcome (twoReaders 2) = some (.ok ()) := by decide +kernel

/-- One read share outstanding: the free's poison write races with it. -/
theorem twoReaders_one_outstanding_rejected :
    outcome (twoReaders 1) = some (.error .illegal) := by decide +kernel

/-- No read share returned: rejected. -/
theorem twoReaders_none_returned_rejected :
    outcome (twoReaders 0) = some (.error .illegal) := by decide +kernel

/-- A reader whose share was not returned before the free cannot read: use after free. -/
theorem read_after_free_rejected : outcome (readAfterFree true) = some (.error .illegal) := by
  decide +kernel

/-- The same run without the late read succeeds: the rejection above is the read. -/
theorem free_before_late_reader_ok : outcome (readAfterFree false) = some (.ok ()) := by
  decide +kernel

/-! ## Runtime: the translated `groupCounter` with a mutated reclamation -/

/-- The generated `groupCounter` (`Proofs/Iogroup/Gen.lean`) with the `Counter` block on the heap
(`heap`, freed by `std`'s poisoning `free`) or the stack, freed after `Group.await` or before it
(`early`). The spawn loop, the tasks and `Group.await` are the generated ones. -/
private def variant (heap early : Bool) (p0 : Io) : ConcM Tgt (Except ErrName (BitVec 32)) := do
  let s1 ← (if heap then alloc .heap 24 8 else allocStack 24 8 : MemM Ptr)
  let s8 ← allocStack 16 8
  let reclaim : MemM Unit := if heap then poisonFree s1 24 else free s1
  let e ← ((do
    let i1 ← pure (← get).c
    Zig.store (α := Zig.Io) 8 (i1.add 0) p0
    Zig.store (α := Io_Mutex) 4 (i1.add 16)
      ({ state := ({ raw := Io_Mutex_State.unlocked } : atomic_Value_Io_Mutex_State) } : Io_Mutex)
    Zig.store (α := BitVec 32) 4 (i1.add 20) (0 : BitVec 32)
    let i8 ← pure (← get).g
    Zig.store (α := Io_Group) 8 i8
      ({ token := ({ raw := none } : atomic_Value___anyopaque), state := (0 : BitVec 64) } : Io_Group)
    modify (fun s => { s with local10 := (0 : BitVec 64) })
    match ← ((do
      Zig.loop (groupCounter.loop13 p0 i1 i8) groupCounter.again13) :
        Zig.CM Tgt groupCounterLocals groupCounterExit) with
    | .br12 => (do
      if early then reclaim
      match ← Zig.groupAwaitC i8 p0 with
      | .error e => pure (.ret (.error e))
      | .ok _ =>
        if early then pure (.ret (.ok 0))
        else do
          let v ← Zig.load (BitVec 32) 4 (i1.add 20)
          pure (.ret (.ok v)))
    | e => pure e) : Zig.CM Tgt groupCounterLocals groupCounterExit).run'
      { (default : groupCounterLocals) with c := s1, g := s8 }
  if !early then reclaim
  free s8
  match e with
  | .ret v => pure v
  | _ => throw .panic

/-- Sampled oracles: constant, counting, and mixed choices. -/
private def oracles : List (Nat → Nat) :=
  [fun _ => 0, fun _ => 1, fun _ => 2, fun i => i, fun i => i / 2, fun i => i / 3] ++
    (List.range 40).map fun s i => (i * (2 * s + 1) + s * s + (i * i) / (s + 1)) % 97

private def fuel : Nat := 4096

private def runs (main : ConcM Tgt (Except ErrName (BitVec 32))) :
    List (Option (Except Error (Except ErrName (BitVec 32) × Mem))) :=
  oracles.map fun o => (Sched.run ⟨.threaded 8, .available⟩ dispatch fuel o main (mem0 .fresh)).run

/-- Completed with 3, every task joined and the `Counter` block dead. -/
private def reclaimedOk : Option (Except Error (Except ErrName (BitVec 32) × Mem)) → Bool
  | some (.ok (.ok v, m)) =>
    v == 3 && m.threads.all (·.joined) && m.blocks[0]?.any (fun b => !b.live)
  | _ => false

private def illegal : Option (Except Error (Except ErrName (BitVec 32) × Mem)) → Bool
  | some (.error .illegal) => true
  | _ => false

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def main : IO Unit := do
  require ((runs (groupCounter {})).all reclaimedOk)
    "groupCounter did not complete with 3, joined tasks and a freed Counter on every sample"
  require ((runs (variant true false {})).all reclaimedOk)
    "heap join-before-free variant did not complete with 3 and a freed Counter on every sample"
  require ((runs (variant true true {})).all illegal)
    "heap free with outstanding read shares was not rejected with illegal on every sample"
  require ((runs (variant false true {})).all illegal)
    "stack free before the readers' joins was not rejected with illegal on every sample"
  IO.println s!"shared-reclamation runtime regressions passed ({oracles.length} schedules each)"
