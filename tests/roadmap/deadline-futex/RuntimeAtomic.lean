import ZigLean.Conc.TimedSched

open Zig Zig.TimedSched

deriving instance DecidableEq for Except

private def check [DecidableEq α] [Repr α] (name : String) (actual expected : α) : IO Unit :=
  unless actual = expected do
    throw (IO.userError s!"C04_ATOMIC_ASSERTION: {name}: expected {reprStr expected}, got {reprStr actual}")

private def ten : Time.Timestamp := ⟨10, by decide⟩
private def eleven : Time.Timestamp := ⟨11, by decide⟩
private def noCancellation : Time.NoCancellation := ⟨fun _ => false, fun _ => rfl⟩
private def equalClock : Time.AwakeEnvironment := ⟨fun _ => ten, fun _ _ _ => Nat.le_refl _⟩
private def p : Ptr := ⟨some 0, 0⟩
private def bytes (n : Nat) : Array Byte := intBytes (BitVec.ofNat 32 n)
private def memory : Mem :=
  { blocks := #[{ bytes := bytes 0, align := 4, kind := .stack, live := true, addr := 4096 },
                { bytes := #[.int 73], align := 1, kind := .constGlobal, live := true, addr := 4104 }],
    clocks := #[#[0, 0], #[0, 1]],
    threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false }],
    atomics := #[{ block := 0, off := 0, len := 4, msgs := #[{ id := 40, bytes := bytes 7, clock := #[0, 1], relClock := #[0, 1] }, { id := 41, bytes := bytes 0, clock := #[0, 1], relClock := #[0, 1] }] }],
    nextMsg := 42 }
private def input (choice : Nat := 0) : Inputs :=
  { environment := .awake equalClock noCancellation, readChoice := fun _ => choice }
private def wait (expected : BitVec 32 := 0) (deadline : Time.Timestamp := eleven) : Program Nat :=
  .wait p expected (.deadline deadline) (fun _ => .done 73)
private def result (out : Outcome Nat) := out.result

def main : IO Unit := do
  let noClock := run {} 2 (fun _ => 0) (wait) memory
  check "default no-clock rejects before any compare" (result noClock) (some (.error .unspecified))
  check "no-clock rejection consumes no read choice" noClock.state.reads 0
  check "no-clock rejection adds no read footprint" noClock.state.kernel.mem.footprint.size 0
  let current := run (input 0) 1 (fun _ => 0) (wait) memory
  check "newest selected message registers" current.state.kernel.registration.isSome true
  check "one tracked comparison" current.state.kernel.mem.footprint.size 1
  check "newest selected id retained" current.state.kernel.mem.seen #[(0, 0, 41)]
  check "comparison choices have separate cursor" current.state.reads 1
  check "relaxed read cannot acquire foreign release clock" current.state.kernel.mem.clocks[0]? (some #[1, 0])
  let older := run (input 1) 3 (fun _ => 0) (wait) memory
  check "older readable message changes predicate result" (result older) (some (.ok 73))
  check "older mismatch is normal" older.state.reasons #[.mismatch]
  check "older selected id retained" older.state.kernel.mem.seen #[(0, 0, 40)]
  check "mismatch has exactly one tracked read" older.state.kernel.mem.footprint.size 1
  check "read did not overwrite newest block bytes" (older.state.kernel.mem.blocks[0]?.map (·.bytes)) (some (bytes 0))
  let invalid := run (input 2) 2 (fun _ => 0) (wait) memory
  check "invalid readable-option index is rejected" (result invalid) (some (.error .illegal))
  let floorMemory := { memory with seen := #[(0, 0, 41), (1, 0, 40)] }
  let belowFloor := run (input 1) 2 (fun _ => 0) (wait) floorMemory
  check "seen floor removes older option" (result belowFloor) (some (.error .illegal))
  let atFloor := run (input 0) 1 (fun _ => 0) (wait) floorMemory
  check "seen floor keeps current option" atFloor.state.kernel.registration.isSome true
  check "other owner's seen entry framed" atFloor.state.kernel.mem.seen #[(1, 0, 40), (0, 0, 41)]
  let returned := step atFloor.state (.normal .spurious)
  check "spurious return preserves coherent floor" returned.state.kernel.mem.seen atFloor.state.kernel.mem.seen
  check "spurious cleanup removes registration" returned.state.kernel.registration.isNone true
  check "spurious cleanup removes queue" returned.state.kernel.mem.waiters.size 0
  check "spurious cleanup frames sentinel" (returned.state.kernel.mem.blocks[1]?.map (·.bytes)) (some #[.int 73])
  check "fuel exhaustion retains read cursor" (resume (fun _ => 0) 0 atFloor.state).state.reads 1
  let repeatedWait : Program Nat := .wait p 7 (.deadline eleven) (fun _ => wait 7)
  let scriptedInput := { input 0 with readChoice := fun i => if i = 0 then 1 else 0 }
  let first := run scriptedInput 1 (fun _ => 0) repeatedWait memory
  check "older matching message can register" first.state.kernel.registration.isSome true
  let firstReturn := step first.state (.normal .spurious)
  let second := resume (fun _ => 0) 2 firstReturn.state
  check "resume retains choice tape and consumes next index" second.state.reads 2
  check "later newest choice mismatches previous expected word" (result second) (some (.ok 73))
  check "second read advances coherent floor" second.state.kernel.mem.seen #[(0, 0, 41)]
  check "two waits perform exactly two atomic reads" second.state.kernel.mem.footprint.size 2
  let plainRace := { memory with footprint := #[{
    tid := 1, clock := #[0, 1], block := 0, off := 0, len := 4, kind := .write }] }
  check "atomic compare rejects a concurrent plain writer"
    (result (run (input 1) 3 (fun _ => 0) (wait) plainRace)) (some (.error .illegal))
  let atomicRace := { plainRace with footprint := plainRace.footprint.map fun e => { e with kind := .atomicWrite } }
  let atomicResult := run (input 1) 3 (fun _ => 0) (wait) atomicRace
  check "atomic compare accepts concurrent atomic footprint" (result atomicResult) (some (.ok 73))
  check "accepted atomic overlap still records one read" atomicResult.state.kernel.mem.footprint.size 2
  let expired := run (input 1) 3 (fun _ => 0) (wait 7 ten) memory
  check "expiry consumes selected matching read then returns normally" expired.state.reasons #[.timeout]
  check "expired comparison retains seen id" expired.state.kernel.mem.seen #[(0, 0, 40)]
  check "expired comparison records exactly one read" expired.state.kernel.mem.footprint.size 1
  let fresh := { memory with atomics := #[], seen := #[], nextMsg := 50 }
  let created := run (input 0) 1 (fun _ => 0) (wait) fresh
  check "comparison creates the source atomic location" created.state.kernel.mem.atomics.size 1
  check "location creation records its fresh message id" created.state.kernel.mem.seen #[(0, 0, 50)]
  check "location creation advances next message id" created.state.kernel.mem.nextMsg 51
  let narrower := { memory with atomics := #[{ block := 0, off := 0, len := 1, msgs := #[{ id := 9, bytes := #[.int 0], clock := #[], relClock := #[] }] }] }
  check "source location width mismatch stays unspecified"
    (result (run (input 0) 3 (fun _ => 0) (wait) narrower)) (some (.error .unspecified))
  IO.println "C04 v5 single atomic compare regressions passed"
