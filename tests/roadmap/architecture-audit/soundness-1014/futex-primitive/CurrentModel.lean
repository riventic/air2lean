import ZigLean.Os.Futex
import ZigLean.Os.Thread
import ZigLean.Conc.Sched

/-!
# Audit S6: Linux alignment regression and remaining primitive mismatches

These four assertions check the primitive at fixed states. The first observes
`Sched.runTrace`; the other three observe the actual call's `CoN` frontier and continuation,
before the scheduler's separate child-handle completion check. They are not client proofs,
native executions, valid std join ownership claims, or whole-program termination claims.

Linux v6.16, commit 038d61fd642278bab63ee8ef722c50d10ab01e8f, supplies the comparison:
`kernel/futex/core.c` (`get_futex_key`) and `kernel/fork.c:1418–1428` (`mm_release`).
See `docs/architecture-audit/soundness-2026-10-14.md` §S6. These are current-model
counterexamples except for the corrected alignment assertion; the other three remain open.
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

/-- Linux key validation rejects unaligned address 4097 before queue lookup. This positive
    regression observes the corrected returned EINVAL; it does not close the other S6 cases. -/
theorem unaligned_wake_einval :
    observeWake (Linux.futex_3arg (p.add 1) 0x81 1) base =
      some (.ok (-22, #[], #[])) := by
  decide +kernel

private def queued : Mem := {
  base with
  threads := #[{ spawner := 0, joined := true }, { spawner := 0, joined := false }]
  clocks := #[#[0, 0], #[0, 0]]
  waiters := #[(1, p)]
}

/-- Primitive-boundary evidence: the actual WAIT rows are equal, and the actual private
    WAKE continuation removes the shared-origin waiter. No scheduler completion claim. -/
theorem private_wakes_shared :
    (Linux.futex_4arg p 0 0 none : ConcM Nat (BitVec 64)) =
        Linux.futex_4arg p 0x80 0 none ∧
    ∃ (count : Mem → Nat) (k : Nat → Mem → CoN Nat (BitVec 64 × Mem) 1),
      (Linux.futex_3arg p 0x81 1 : ConcM Nat (BitVec 64)) 2 queued =
        .sync (.pick count) queued k ∧
      (match k 0 queued with
       | .leaf r => r.map (·.map fun (v, m') => (v.toInt, m'.waiters, m'.woken))
       | .sync .. => none) = some (.ok (1, #[], #[1])) := by
  constructor
  · rfl
  · refine ⟨_, _, rfl, ?_⟩
    decide +kernel

private def adjacent : Mem := {
  queued with
  blocks := #[block 4096 4, block 4100 4]
  waiters := #[(1, ⟨some 1, 0⟩)]
}

/-- Primitive-boundary evidence: equal numeric addresses 4100, but the actual WAKE
    continuation misses the other provenance pointer's waiter. No completion claim. -/
theorem equal_address_ptr_miss :
    (ptrAddr ⟨some 0, 4⟩).run adjacent = (ptrAddr ⟨some 1, 0⟩).run adjacent ∧
    ∃ (count : Mem → Nat) (k : Nat → Mem → CoN Nat (BitVec 64 × Mem) 1),
      (Linux.futex_3arg ⟨some 0, 4⟩ 0x81 1 : ConcM Nat (BitVec 64)) 2 adjacent =
        .sync (.pick count) adjacent k ∧
      (match k 0 adjacent with
       | .leaf r => r.map (·.map fun (v, m') => (v.toInt, m'.waiters, m'.woken))
       | .sync .. => none) = some (.ok (0, #[(1, ⟨some 1, 0⟩)], #[])) := by
  constructor
  · rfl
  · refine ⟨_, _, rfl, ?_⟩
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

/-- Primitive-boundary evidence: actual cloneExit clears ctid and wakes both queued
    raw waiters. No claim that two valid std join-handle owners coexist or complete. -/
theorem cleartid_over_wake :
    ∃ (count : Mem → Nat) (k : Nat → Mem → CoN Nat (Unit × Mem) 1),
      (Linux.cloneExit p : ConcM Nat Unit) 2 twoRawWaiters =
        .sync (.pick count) twoRawWaiters k ∧
      (match k 0 twoRawWaiters with
       | .leaf r => r.map (·.map fun (_, m') =>
           (m'.waiters, m'.woken, m'.blocks[0]?.map fun b => b.bytes.extract 0 4))
       | .sync .. => none) =
        some (.ok (#[], #[1, 2], some #[.int 0, .int 0, .int 0, .int 0])) := by
  refine ⟨_, _, rfl, ?_⟩
  decide +kernel

end AuditS6
