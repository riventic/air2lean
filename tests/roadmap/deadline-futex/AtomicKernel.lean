import ZigLean.Conc.TimedSched
import ZigLean.Conc.Lemmas

open Zig Zig.TimedSched

namespace DeadlineAtomicKernelTests

/-- The kernel comparison uses exactly the existing relaxed atomic load action. -/
theorem readWord_atomic (choice : Nat) (p : Ptr) :
    readWord choice p = atomicLoadAt (n := 32) choice .relaxed 4 p := rfl

/-- A selected successful atomic read is the sole input to enqueueing. The post-read
memory, including its location and seen updates, is carried into the registration. -/
theorem begin_enqueue_after_read (s : Kernel) (choice : Nat) (p : Ptr)
    (expected : BitVec 32) (deadline : Option Time.Timestamp) (now : Time.Timestamp)
    (readMem : Mem)
    (hr : s.registration = none)
    (hq : s.mem.waiters.any (·.1 == s.mem.current) = false)
    (hw : s.mem.woken.contains s.mem.current = false)
    (read : (readWord choice p).run s.mem = pure (expected, readMem))
    (future : deadline.any (fun expiry => expiry.nanoseconds ≤ now.nanoseconds) = false) :
    s.begin choice p expected deadline now = pure (none,
      { mem := { readMem with waiters := readMem.waiters.push (readMem.current, p) },
        registration := some ⟨readMem.current, p, deadline⟩ }) := by
  have notWoken : s.mem.current ∉ s.mem.woken := by
    intro member
    have isWoken : s.mem.woken.contains s.mem.current = true :=
      Array.contains_iff_mem.mpr member
    rw [hw] at isWoken
    cases isWoken
  simp [Kernel.begin, hr, hq, hw, notWoken, read, future]

/-- Cleanup does not undo the selected read's coherent seen floor. -/
theorem release_seen (s : Kernel) (r : Registration) (h : s.registration = some r) :
    s.release.mem.seen = s.mem.seen := by
  simp [Kernel.release, h]

/-- Relaxed load completion adds the observation only; it creates no acquire edge and
no second footprint record after location preparation. -/
theorem relaxed_load_frame (located : Mem) (li : Nat) (msg : Msg) :
    (Conc.Proto.loadM located li .relaxed msg).clocks = located.clocks ∧
    (Conc.Proto.loadM located li .relaxed msg).footprint = located.footprint ∧
    (Conc.Proto.loadM located li .relaxed msg).blocks = located.blocks := ⟨rfl, rfl, rfl⟩

end DeadlineAtomicKernelTests
