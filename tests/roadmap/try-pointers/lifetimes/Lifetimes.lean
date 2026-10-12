import TryLifetimes.Gen

/-! L04 lifetimes of addressed error unions (`try_lifetimes.zig`), on the translation of the
retained export of one Zig version (`check.sh` checks 0.14.1, 0.15.2, 0.16.0 and 0.17.0):

* a cleanup that frees the union: the error path reads the error code before the `errdefer`
  frees the block, and no heap block stays live; a payload pointer that outlives its union is a
  use after free (`.illegal`);
* payload pointers shared by threads, under every scheduler oracle tried: reads of one union
  and writes of two unions give the native results, and a write racing a read of one union's
  payload is a data race (`.illegal`), on every schedule.

Kernel-checked theorems for the sequential cases; `main` runs the schedules. -/

open Zig TryLifetimes

/-- The result of running `f` from an empty memory, and whether every heap block is freed. -/
def runFreed {α : Type} (f : MemM α) : Option (Except Error (α × Bool)) :=
  ((f.run (mem0 .fresh)).run).map fun r =>
    r.map fun (x, m) => (x, m.blocks.all fun b => b.kind != .heap || !b.live)

theorem freeOnError_ok : runFreed (freeOnError default 7 false) = some (.ok (.ok 7, true)) := by
  decide +kernel

/-- The `errdefer` frees the union after the pointer try captured the error. -/
theorem freeOnError_error : runFreed (freeOnError default 7 true) = some (.ok (.error "Bad", true)) := by
  decide +kernel

/-- The payload pointer of a freed union is dangling: the read is a use after free. -/
theorem readDangling_illegal : runFreed (readDangling default 5) = some (.error .illegal) := by
  decide +kernel

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def sched {α : Type} (o : Nat → Nat) (x : ConcM Tgt α) : Option (Except Error α) :=
  (Sched.run ⟨.any, .available⟩ dispatch 500 o x {}).run |>.map (·.map Prod.fst)

def main : IO Unit := do
  for seed in List.range 32 do
    let o := fun turn => seed + turn * 7
    require (sched o (concurrentReads 9 false) == some (.ok (.ok 18)))
      s!"concurrent reads through one union's payload: schedule {seed}"
    require (sched o (concurrentReads 9 true) == some (.ok (.ok 0)))
      s!"concurrent pointer tries on an error: schedule {seed}"
    require (sched o (concurrentWrites 3 4) == some (.ok (.ok 0x304)))
      s!"concurrent writes through two unions' payloads: schedule {seed}"
    require (sched o (racingAliases 5) == some (.error .illegal))
      s!"a write racing a read of one payload escaped the race check: schedule {seed}"
  IO.println "pointer-try lifetime theorems and 32 schedules passed"
