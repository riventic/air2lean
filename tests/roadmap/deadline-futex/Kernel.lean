import ZigLean.Conc.TimedSched

open Zig Zig.TimedSched

namespace DeadlineKernelTests

/-- The new queue wake is exactly the existing memory wake, with the same ordering. -/
theorem wake_legacy (s : Kernel) (p : Ptr) (n : Nat) :
    ((Thread.futexWake p n []).run s.mem).run = some (.ok ((), (s.wake p n).mem)) := by
  unfold Kernel.wake
  split
  · simp_all
  · rename_i heq
    simp [Thread.futexWake, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      StateT.run, ExceptT.run, pure, ExceptT.pure, ExceptT.mk] at heq
  · rename_i heq
    simp [Thread.futexWake, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      StateT.run, ExceptT.run, pure, ExceptT.pure, ExceptT.mk] at heq

/-- Cleanup is an actual function over the Mem queue, not an assumed relation. -/
theorem release_registration (s : Kernel) (r : Registration)
    (h : s.registration = some r) : s.release.registration = none := by
  simp [Kernel.release, h]

theorem release_owner (s : Kernel) (r : Registration)
    (h : s.registration = some r) :
    (∀ w ∈ s.release.mem.waiters, w.1 ≠ r.owner) ∧
    r.owner ∉ s.release.mem.woken := by
  constructor
  · intro w hw
    have hw' : w ∈ s.mem.waiters.filter (fun x => x.1 != r.owner) := by
      simpa only [Kernel.release, h] using hw
    have hx := (Array.mem_filter.mp hw').2
    simpa using hx
  · intro hw
    have hw' : r.owner ∈ s.mem.woken.filter (fun t => t != r.owner) := by
      simpa only [Kernel.release, h] using hw
    have hx := (Array.mem_filter.mp hw').2
    simpa using hx

theorem release_other_waiter (s : Kernel) (r : Registration)
    (h : s.registration = some r) (w : ThreadId × Ptr) (owner : w.1 ≠ r.owner) :
    w ∈ s.release.mem.waiters ↔ w ∈ s.mem.waiters := by
  simp [Kernel.release, h, Array.mem_filter, owner]

/-- Normal completion changes no source bytes, vector clocks or access evidence. -/
theorem release_frame (s : Kernel) (r : Registration)
    (h : s.registration = some r) :
    s.release.mem.blocks = s.mem.blocks ∧ s.release.mem.clocks = s.mem.clocks ∧
    s.release.mem.footprint = s.mem.footprint ∧ s.release.mem.atomics = s.mem.atomics ∧
    s.release.mem.threads = s.mem.threads ∧ s.release.mem.groups = s.mem.groups := by
  simp [Kernel.release, h]

theorem wake_no_acquire (s : Kernel) (p : Ptr) (n : Nat) :
    (s.wake p n).mem.clocks = s.mem.clocks ∧
    (s.wake p n).mem.footprint = s.mem.footprint := ⟨rfl, rfl⟩

/-- Expiry does not suppress an already enabled boundary wake. -/
theorem boundary_alternatives (s : Kernel) (r : Registration) (now : Time.Timestamp)
    (hr : s.registration = some r) (hd : r.deadline = some now)
    (hw : s.mem.woken.contains r.owner = true) :
    s.enabled (some now) .wake = true ∧ s.enabled (some now) .timeout = true := by
  have hw' : r.owner ∈ s.mem.woken := Array.contains_iff_mem.mp hw
  simp [Kernel.enabled, hr, hd, hw']

/-- No-result snapshots retain the exact paused continuation and registration. -/
theorem zero_fuel_snapshot (s : State α) (oracle : Nat → Nat) :
    (resume oracle 0 s).result = none ∧ (resume oracle 0 s).state = s := ⟨rfl, rfl⟩

theorem normal_resumes_unit (s : State α) (next : Unit → Program α) (r : ReturnReason)
    (hc : s.control = .waiting next) (he : s.kernel.enabled s.now r = true) :
    (step s (.normal r)).state.control = .running (next ()) := by
  simp [step, hc, he, resumeNormal]

theorem normal_result_pending (s : State α) (next : Unit → Program α) (r : ReturnReason)
    (hc : s.control = .waiting next) (he : s.kernel.enabled s.now r = true) :
    (step s (.normal r)).result = none := by
  simp [step, hc, he]

theorem normal_registration_cleanup (s : State α) (next : Unit → Program α)
    (reason : ReturnReason) (registration : Registration)
    (hc : s.control = .waiting next) (he : s.kernel.enabled s.now reason = true)
    (hr : s.kernel.registration = some registration) :
    (step s (.normal reason)).state.kernel.registration = none := by
  simp [step, hc, he, resumeNormal, Kernel.release, hr]

end DeadlineKernelTests
