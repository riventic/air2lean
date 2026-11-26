import TryLifetimes.V0_16_0.Gen
import ZigLean.Sep.Full.AutoAll

/-! L04 lifetimes of addressed error unions (`try_lifetimes.zig`), on the translation of the
retained export of one Zig version (`TryLifetimes.V0_16_0.Gen`; written for Zig 0.17.1, the
modules of 0.14.1, 0.15.2 and 0.16.0 are this one with the version renamed: `check.sh`,
`scripts/fixtures.py instance`):

* a cleanup that frees the union: the error path reads the error code before the `errdefer`
  frees the block, and no heap block stays live; a payload pointer that outlives its union is a
  use after free (`.illegal`);
* payload pointers shared by threads, under every scheduler oracle tried: reads of one union
  and writes of two unions give the native results, and a write racing a read of one union's
  payload is a data race (`.illegal`), on every schedule.

Kernel-checked theorems for the sequential cases, `fsym` thread steps for the thread bodies
(`readPayload` on a shared union, `writePayload` on an owned one), the spawn targets (`reader`,
`writer`) and a result location written by an owner; `main` runs the schedules. The spawn and
the join are not composed in the logic (`README.md`). -/

open Zig TryLifetimes.V0_16_0

namespace TryLifetimes.V0_16_0.Lifetimes

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

/-! ### The thread bodies as thread steps

`fsym` walks each thread body of `concurrentReads` and `concurrentWrites` as a thread step
(`FTTotalTriple`): the readers hold a read share of the union (`spts`, the pointer-try rules on
a shared union and their locality providers, `ZigLean/Sep/Full/Try.lean`), a writer owns its
union. -/

section Threads
open Zig.Full Zig.Full.FAssn

/-- A reader of a union that holds a payload gets it, through its payload pointer. -/
theorem readPayload_ok (p : Ptr) (x : BitVec 8) (φ : Frac) :
    FTTotalTriple (spts p 2 φ (Except.ok x : Except ErrName (BitVec 8))) (readPayload p)
      (fun r => ⟪r = .ok x⟫ ⋆ spts p 2 φ (Except.ok x : Except ErrName (BitVec 8))) := by
  fsym

/-- A reader of a union that holds an error gets the error. -/
theorem readPayload_error (p : Ptr) (φ : Frac) :
    FTTotalTriple (spts p 2 φ (Except.error "Bad" : Except ErrName (BitVec 8))) (readPayload p)
      (fun r => ⟪r = .error "Bad"⟫ ⋆
        spts p 2 φ (Except.error "Bad" : Except ErrName (BitVec 8))) := by
  fsym

/-- A writer of an owned union that holds a payload replaces it through its payload pointer. -/
theorem writePayload_ok (p : Ptr) (x w : BitVec 8) :
    FTTotalTriple (up (pts p 2 (Except.ok x : Except ErrName (BitVec 8)))) (writePayload p w)
      (fun r => ⟪r = .ok ()⟫ ⋆ up (pts p 2 (Except.ok w : Except ErrName (BitVec 8)))) := by
  fsym

/-- A writer of an owned union that holds an error gets the error and writes nothing. -/
theorem writePayload_error (p : Ptr) (w : BitVec 8) :
    FTTotalTriple (up (pts p 2 (Except.error "Bad" : Except ErrName (BitVec 8)))) (writePayload p w)
      (fun r => ⟪r = .error "Bad"⟫ ⋆
        up (pts p 2 (Except.error "Bad" : Except ErrName (BitVec 8)))) := by
  fsym

/-! The spawn targets themselves (`reader`, `writer`: the thread bodies with their `catch`), on
what each thread is given: a reader a read share of the union and its own output cell, a writer
its union. -/

/-- A reader thread stores the payload of the shared union in its output cell. -/
theorem reader_ok (p out : Ptr) (x w : BitVec 8) (φ : Frac) :
    FTTotalTriple (spts p 2 φ (Except.ok x : Except ErrName (BitVec 8)) ⋆ up (pts out 1 w))
      (reader p out)
      (fun _ => spts p 2 φ (Except.ok x : Except ErrName (BitVec 8)) ⋆ up (pts out 1 x)) := by
  fsym

/-- A reader thread of a union that holds an error stores 0 (`catch 0`). -/
theorem reader_error (p out : Ptr) (w : BitVec 8) (φ : Frac) :
    FTTotalTriple (spts p 2 φ (Except.error "Other" : Except ErrName (BitVec 8)) ⋆ up (pts out 1 w))
      (reader p out)
      (fun _ => spts p 2 φ (Except.error "Other" : Except ErrName (BitVec 8)) ⋆
        up (pts out 1 (0 : BitVec 8))) := by
  fsym

/-- A writer thread replaces the payload of the union it owns. -/
theorem writer_ok (p : Ptr) (x w : BitVec 8) :
    FTTotalTriple (up (pts p 2 (Except.ok x : Except ErrName (BitVec 8)))) (writer p w)
      (fun _ => up (pts p 2 (Except.ok w : Except ErrName (BitVec 8)))) := by
  fsym

/-- A writer thread of a union that holds an error writes nothing (`catch {}`). -/
theorem writer_error (p : Ptr) (w : BitVec 8) :
    FTTotalTriple (up (pts p 2 (Except.error "Bad" : Except ErrName (BitVec 8)))) (writer p w)
      (fun _ => up (pts p 2 (Except.error "Bad" : Except ErrName (BitVec 8)))) := by
  fsym

/-- A result location written by a thread that owns the union (`errunion_payload_ptr_set`, then
the payload write): whatever the union held, it holds the payload. The error code is written, so
the step is local only for an owner (`ThreadLocal.errSetOk_pts`, `errOkSlot_store`). -/
theorem setPayload_owned (p : Ptr) (u : Except ErrName (BitVec 8)) (y : BitVec 8) :
    FTTotalTriple (up (pts p 2 u))
      (do let q ← Zig.errSetOk (BitVec 8) 2 p; Zig.store (α := BitVec 8) 1 q y)
      (fun _ => up (pts p 2 (Except.ok y : Except ErrName (BitVec 8)))) := by
  fsym

/-- The same for a payload that lies before the error code (`E!u32`). -/
theorem setPayload32_owned (p : Ptr) (u : Except ErrName (BitVec 32)) (y : BitVec 32) :
    FTTotalTriple (up (pts p 4 u))
      (do let q ← Zig.errSetOk (BitVec 32) 4 p; Zig.store (α := BitVec 32) 4 q y)
      (fun _ => up (pts p 4 (Except.ok y : Except ErrName (BitVec 32)))) := by
  fsym

/-- A share gives no write: `errunion_payload_ptr_set` on a shared union has no rule, sequential
or in a thread (fail closed; the control fails for either reason). -/
theorem setPayload_shared_rejected (p : Ptr) (u : Except ErrName (BitVec 8)) (φ : Frac) : True := by
  fail_if_success
    have : FTTotalTriple (spts p 2 φ u) (Zig.errSetOk (BitVec 8) 2 p)
        (fun _ => spts p 2 φ u) := by
      fsym
  trivial

end Threads

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

end TryLifetimes.V0_16_0.Lifetimes
