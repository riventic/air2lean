import ZigLean.Sep.Full.AutoAll

/-!
# What a triple over the device state does not say about a run

A run equation over every memory that fixes the whole final memory
(`c.run m = pure (v, { m with dev := D' })` for every `m` with `m.dev = D`) is **not** a
consequence of a total triple `FTotalTriple (devOwn D) c (fun x => ⟪x = v⟫ ⋆ devOwn D')`. Two
kernel-checked counterexamples, one for each thing the run equation says more:

* `not_exact`: **the final memory is not fixed.** `skew` (one arbitrary word, discarded) keeps
  every resource, so it has the triple with `D' = D`; its run moves the oracle's position
  (`Mem.arbitraryNext`), which `Holds` does not read.
* `not_every_memory`: **a memory that is not `Mem.FSeq` is not covered.** `guard` returns on a
  memory whose running thread has a clock and throws otherwise; it has the same triple, and it
  throws on a memory without clocks.

What a triple does say is `FTotalTriple.run_dev`/`run_dev_val` (`ZigLean/Sep/Full/Device.lean`)
and `FTotalTriple.run_dev_ticks` (`ZigLean/Sep/Full/Cost.lean`): from every `Mem.FSeq` memory
that holds a resource and a frame without a device fragment, the run returns the value, the
final device state is the postcondition's, the frame is held again, and (with credits) the step
count is exact.

Kernel-checked; the expected axioms are `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace SepAuto.DeviceRunCX
open Zig Zig.Full Zig.Full.FAssn

/-- A command that moves only the arbitrary-word oracle's position. -/
def skew : MemM Unit := do
  let _ ← Zig.arbitraryWord
  pure ()

theorem skew_run (m : Mem) :
    skew.run m = pure ((), { m with arbitraryNext := m.arbitraryNext + 1 }) := rfl

/-- `skew` keeps every resource: `Holds` does not read the oracle's position. -/
theorem skew_triple (P : FAssn) : FTotalTriple P skew (fun x => ⟪x = ()⟫ ⋆ P) :=
  FTotalTriple.of_run fun m r rF hh hp hs =>
    ⟨(), _, r, skew_run m, Holds.congrMem (m := m) rfl rfl hh, sep_lift.mpr ⟨rfl, hp⟩,
      hs.congrMem rfl rfl hs.1.single⟩

/-- **The final memory is not fixed by the triple.** -/
theorem not_exact : ¬ ∀ (c : MemM Unit) (D D' : DevState),
    FTotalTriple (devOwn D) c (fun x => ⟪x = ()⟫ ⋆ devOwn D') →
      ∀ m : Mem, m.dev = D → c.run m = pure ((), { m with dev := D' }) := by
  intro h
  have h1 := h skew {} {} (skew_triple _) {} rfl
  rw [skew_run] at h1
  have h2 : ({ ({} : Mem) with arbitraryNext := ({} : Mem).arbitraryNext + 1 } : Mem).arbitraryNext
      = ({ ({} : Mem) with dev := {} } : Mem).arbitraryNext := by
    injection h1 with h1
    injection h1 with h1
    injection h1 with _ h1
    exact congrArg Mem.arbitraryNext h1
  exact absurd h2 (by decide)

/-- A command that returns only on a memory whose running thread has a clock. -/
def guard : MemM Unit := do
  let m ← get
  if m.current < m.clocks.size then pure () else throw .illegal

theorem guard_triple (P : FAssn) : FTotalTriple P guard (fun x => ⟪x = ()⟫ ⋆ P) :=
  FTotalTriple.of_read fun m _ _ _ _ hs => by
    have hc : m.current < m.clocks.size := hs.1.single.1
    have e : guard.run m =
        (if m.current < m.clocks.size then (pure () : MemM Unit) else throw .illegal).run m := rfl
    rw [e, ite_eq_left hc]; rfl

/-- A memory that is not `Mem.FSeq`: no clock for its running thread. -/
def noClock : Mem := { clocks := #[] }

/-- **The triple says nothing about a memory that is not `Mem.FSeq`**: not even that the run
returns. -/
theorem not_every_memory : ¬ ∀ (c : MemM Unit) (D D' : DevState),
    FTotalTriple (devOwn D) c (fun x => ⟪x = ()⟫ ⋆ devOwn D') →
      ∀ m : Mem, m.dev = D → ∃ m', c.run m = pure ((), m') := by
  intro h
  obtain ⟨m', h1⟩ := h guard {} {} (guard_triple _) noClock rfl
  have h2 : guard.run noClock = throw .illegal := rfl
  rw [h2] at h1
  injection h1 with h1
  cases h1

end SepAuto.DeviceRunCX
