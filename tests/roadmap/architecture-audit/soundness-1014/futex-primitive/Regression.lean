import ZigLean.Os.Futex
import ZigLean.Os.Thread
import ZigLean.Conc.Sched

/-!
# Audit S6: regressions of the corrected OS futex primitive

Each theorem observes the actual definitions in `ZigLean/Os/Futex.lean` and
`ZigLean/Os/Thread.lean` at a fixed state, as the corrected model must behave natively. The
first observes `Sched.runTrace`; the second observes the actual call's `CoN` frontier and its
continuation, before the scheduler's separate child-handle completion check. They are not
client proofs, native executions, valid std join ownership claims or whole-program termination
claims. The open witnesses are in `CurrentModel.lean`.

Linux v6.16, commit 038d61fd642278bab63ee8ef722c50d10ab01e8f, supplies the comparison:
`kernel/futex/core.c` (`get_futex_key`) and `kernel/fork.c:1418–1428` (`mm_release`).
See `docs/architecture-audit/soundness-2026-10-14.md` §S6.
-/

open Zig Zig.Os

namespace AuditS6

private def env : Zig.Env := { io := .any, spawn := .available }
private def noKids : Nat → ConcM Nat Unit := fun _ => pure ()

private def block (addr size : Nat) : Block := {
  bytes := Array.replicate size (.int 0)
  align := 4
  kind := .heap
  live := true
  addr
}

private def p : Ptr := ⟨some 0, 0⟩
private def base : Mem := { blocks := #[block 4096 8] }

private def observeWake (call : ConcM Nat (BitVec 64)) (m : Mem) :
    Option (Except Error (Int × Array (ThreadId × Ptr) × Array ThreadId)) :=
  (Sched.runTrace env noKids 20 (fun _ => 0) call m).1.map
    (·.map fun (v, m') => (v.toInt, m'.waiters, m'.woken))

/-- Linux key validation rejects unaligned address 4097 before queue lookup: `-EINVAL`, with
the queue unchanged. -/
theorem unaligned_wake_einval :
    observeWake (Linux.futex_3arg (p.add 1) 0x81 1) base =
      some (.ok (-22, #[], #[])) := by
  decide +kernel

private def twoRawWaiters : Mem := {
  base with
  blocks := #[{ block 4096 8 with
    bytes := #[.int 1, .int 0, .int 0, .int 0, .int 0, .int 0, .int 0, .int 0] }]
  threads := #[{ spawner := 0, joined := true },
    { spawner := 0, joined := false }, { spawner := 0, joined := false }]
  clocks := #[#[0, 0, 0], #[0, 0, 0], #[0, 0, 0]]
  waiters := #[(1, p), (2, p)]
}

/-- `CHILD_CLEARTID` wakes at most one waiter (Linux `mm_release`: `FUTEX_WAKE` with count 1).
With two raw waiters queued at `ctid`, the actual `cloneExit` has exactly two options, one for
each waiter: each clears the word and wakes that waiter alone, and the other stays queued. -/
theorem cleartid_wakes_one :
    ∃ (count : Mem → Nat) (k : Nat → Mem → CoN Nat (Unit × Mem) 1),
      (Linux.cloneExit p : ConcM Nat Unit) 2 twoRawWaiters =
        .sync (.pick count) twoRawWaiters k ∧
      count twoRawWaiters = 2 ∧
      (match k 0 twoRawWaiters with
       | .leaf r => r.map (·.map fun (_, m') =>
           (m'.waiters, m'.woken, m'.blocks[0]?.map fun b => b.bytes.extract 0 4))
       | .sync .. => none) =
        some (.ok (#[(2, p)], #[1], some #[.int 0, .int 0, .int 0, .int 0])) ∧
      (match k 1 twoRawWaiters with
       | .leaf r => r.map (·.map fun (_, m') =>
           (m'.waiters, m'.woken, m'.blocks[0]?.map fun b => b.bytes.extract 0 4))
       | .sync .. => none) =
        some (.ok (#[(1, p)], #[2], some #[.int 0, .int 0, .int 0, .int 0])) := by
  refine ⟨_, _, rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩

end AuditS6
