import ZigLean.Os.Futex
import ZigLean.Os.Thread
import ZigLean.Conc.Sched

/-!
# Audit S6: remaining primitive mismatches (current-model witnesses)

These two assertions observe the actual call's `CoN` frontier and continuation at fixed states.
They are not client proofs, native executions or whole-program termination claims. The
corrected cases (alignment, `CHILD_CLEARTID` wake-one) are regressions in `Regression.lean`.

Linux v6.16, commit 038d61fd642278bab63ee8ef722c50d10ab01e8f, supplies the comparison:
`kernel/futex/core.c` (`get_futex_key`). See `docs/architecture-audit/soundness-2026-10-14.md`
§S6. Both remain open.
-/

open Zig Zig.Os

namespace AuditS6

private def block (addr size : Nat) : Block := {
  bytes := Array.replicate size (.int 0)
  align := 4
  kind := .heap
  live := true
  addr
}

private def p : Ptr := ⟨some 0, 0⟩
private def base : Mem := { blocks := #[block 4096 8] }

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

end AuditS6
