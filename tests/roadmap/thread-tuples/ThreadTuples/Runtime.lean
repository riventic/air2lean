import ThreadTuples.Gen

open Zig
private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def result (o : Nat → Nat) (x : ConcM ThreadTuples.Tgt (Except ErrName (BitVec 32))) :
    Option Nat :=
  match (Sched.run ThreadTuples.dispatch 500 o x {}).run with
  | some (.ok (.ok n, _)) => some n.toNat
  | _ => none

private def bv (n : Nat) : BitVec 32 := BitVec.ofNat 32 n

private def sharedPlain : ConcM ThreadTuples.Tgt Unit := do
  let out ← ConcM.liftMem (alloc .heap 4 4)
  let other ← ConcM.liftMem (alloc .heap 4 4)
  ConcM.liftMem (store 4 out (0#32))
  ConcM.liftMem (store 4 other (0#32))
  let one ← ConcM.sync (.spawn (.mixedWorker (1, out, 2, other)))
  let two ← ConcM.sync (.spawn (.mixedWorker (3, out, 4, other)))
  let _ ← ConcM.sync (.join one)
  let _ ← ConcM.sync (.join two)
  pure ()

def main : IO Unit := do
  for seed in List.range 16 do
    let oracle := fun turn => seed + turn * 7
    require ((Sched.run ThreadTuples.dispatch 100 oracle ThreadTuples.empty {}).run matches
      some (.ok (.ok (), _))) s!"zero argument worker failed at schedule {seed}"
    require ((Sched.run ThreadTuples.dispatch 100 oracle ThreadTuples.genericEmpty {}).run matches
      some (.ok (.ok (), _))) s!"generic zero argument worker failed at schedule {seed}"
    require ((Sched.run ThreadTuples.dispatch 500 oracle sharedPlain {}).run matches
      some (.error .illegal)) s!"shared plain pointers escaped race check: {seed}"
    require (result oracle (ThreadTuples.groupMixed {} 10 2) == some 680)
      s!"Io.Group tuple failed: {seed}"
    for (a, b, c) in [(1, 2, 4), (9, 3, 17), (0, 0, 0), (4294967295, 7, 123)] do
      require (result oracle (ThreadTuples.mixed (bv a) (bv b)) ==
        some ((bv a * 52 + bv b * 80).toNat)) s!"mixed tuple order failed: {seed}, {a}, {b}"
      require (result oracle (ThreadTuples.copied (bv a) (bv b) (bv c)) ==
        some ((bv a * 3 + bv b * 5 + bv c * 7 + 99).toNat))
        s!"captured value was not copied: {seed}, {a}, {b}, {c}"
      require (result oracle (ThreadTuples.atomicShared (bv a) (bv b)) ==
        some (((bv a + bv b) * 3).toNat)) s!"shared atomic tuple failed: {seed}, {a}, {b}"
  IO.println "thread tuple generated runtime schedules passed"
