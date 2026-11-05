import ZigLean.Os.Futex

/-!
# Audit S6: remaining primitive mismatches (current-model witnesses)

These two assertions observe the actual call's `CoN` frontier: the stop or result that option 0
of the call's first pick reaches, at fixed states. They are not client proofs, native executions
or whole-program termination claims. The corrected cases (alignment, address validation,
`CHILD_CLEARTID` wake-one) are regressions in `Regression.lean`.

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

/-- The futex `wait` stop that option 0 of a call's first pick reaches: its address and value. -/
private def waitStop {α : Type} : CoN Nat α 3 → Option (Ptr × BitVec 32)
  | .sync (.pick _) m k =>
    match k (0 : Nat) m with
    | .sync (.wait q e) _ _ => some (q, e)
    | _ => none
  | _ => none

/-- The result of a WAKE row after option 0 of its pick: the value, the queue and the woken. -/
private def wakeObs : CoN Nat (BitVec 64 × Mem) 2 →
    Option (Except Error (Int × Array (ThreadId × Ptr) × Array ThreadId))
  | .sync (.pick _) m k =>
    match k (0 : Nat) m with
    | .leaf r => r.map (·.map fun (v, m') => (v.toInt, m'.waiters, m'.woken))
    | .sync .. => none
  | _ => none

/-- Primitive-boundary evidence: a shared and a private WAIT at `p` reach the same `wait` stop,
which carries no key domain, and the actual private WAKE removes the waiter queued there. No
scheduler completion claim. -/
theorem private_wakes_shared :
    waitStop ((Linux.futex_4arg p 0 0 none : ConcM Nat (BitVec 64)) 3 base) = some (p, 0) ∧
    waitStop ((Linux.futex_4arg p 0x80 0 none : ConcM Nat (BitVec 64)) 3 base) = some (p, 0) ∧
    wakeObs ((Linux.futex_3arg p 0x81 1 : ConcM Nat (BitVec 64)) 2 queued) =
      some (.ok (1, #[], #[1])) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

private def adjacent : Mem := {
  queued with
  blocks := #[block 4096 4, block 4100 4]
  waiters := #[(1, ⟨some 1, 0⟩)]
}

/-- Primitive-boundary evidence: equal numeric addresses 4100, but the actual private WAKE
misses the other provenance pointer's waiter. No completion claim. -/
theorem equal_address_ptr_miss :
    (ptrAddr ⟨some 0, 4⟩).run adjacent = (ptrAddr ⟨some 1, 0⟩).run adjacent ∧
    wakeObs ((Linux.futex_3arg ⟨some 0, 4⟩ 0x81 1 : ConcM Nat (BitVec 64)) 2 adjacent) =
      some (.ok (0, #[(1, ⟨some 1, 0⟩)], #[])) :=
  ⟨rfl, by decide +kernel⟩

end AuditS6
