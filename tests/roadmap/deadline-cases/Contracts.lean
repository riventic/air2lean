import ZigLean.Conc.TimedBudget
import ZigLean.Conc.TimedCall

/-! C04 named-case contracts over the selected timed kernel and interpreter: deadline
boundary, timeout, wake-before-timeout and wake-at-timeout. Every time is an explicit
monotonic awake observation (`Time.Timestamp`); wall-clock values have a separate type and
are rejected by the selected adapter. No fairness, OS or cancellation claim is made. -/
open Zig Zig.TimedSched

namespace DeadlineCaseContracts

private theorem not_woken {s : Kernel} (hw : s.mem.woken.contains s.mem.current = false) :
    s.mem.current ∉ s.mem.woken := fun member => by
  rw [Array.contains_iff_mem.mpr member] at hw
  cases hw

/-- Deadline boundary and past deadline: a matching word whose deadline is at or before
the current observation returns `timeout` at once, without registering. -/
theorem begin_at_or_after_deadline (s : Kernel) (choice : Nat) (p : Ptr)
    (expected : BitVec 32) (deadline now : Time.Timestamp) (readMem : Mem)
    (hr : s.registration = none)
    (hq : s.mem.waiters.any (·.1 == s.mem.current) = false)
    (hw : s.mem.woken.contains s.mem.current = false)
    (read : (readWord choice p).run s.mem = pure (expected, readMem))
    (reached : deadline.nanoseconds ≤ now.nanoseconds) :
    s.begin choice p expected (some deadline) now = pure (some .timeout, { s with mem := readMem }) := by
  simp [Kernel.begin, hr, hq, not_woken hw, read, reached]

/-- The boundary itself, `now = deadline`, is expired (the comparison is not strict). -/
theorem begin_boundary (s : Kernel) (choice : Nat) (p : Ptr) (expected : BitVec 32)
    (now : Time.Timestamp) (readMem : Mem)
    (hr : s.registration = none)
    (hq : s.mem.waiters.any (·.1 == s.mem.current) = false)
    (hw : s.mem.woken.contains s.mem.current = false)
    (read : (readWord choice p).run s.mem = pure (expected, readMem)) :
    s.begin choice p expected (some now) now = pure (some .timeout, { s with mem := readMem }) :=
  begin_at_or_after_deadline s choice p expected now now readMem hr hq hw read (Nat.le_refl _)

/-- One nanosecond before the boundary the caller registers and pauses instead. -/
theorem begin_before_deadline (s : Kernel) (choice : Nat) (p : Ptr) (expected : BitVec 32)
    (deadline now : Time.Timestamp) (readMem : Mem)
    (hr : s.registration = none)
    (hq : s.mem.waiters.any (·.1 == s.mem.current) = false)
    (hw : s.mem.woken.contains s.mem.current = false)
    (read : (readWord choice p).run s.mem = pure (expected, readMem))
    (early : now.nanoseconds < deadline.nanoseconds) :
    s.begin choice p expected (some deadline) now = pure (none,
      { mem := { readMem with waiters := readMem.waiters.push (readMem.current, p) },
        registration := some ⟨readMem.current, p, some deadline⟩ }) := by
  have : ¬ deadline.nanoseconds ≤ now.nanoseconds := by omega
  simp [Kernel.begin, hr, hq, not_woken hw, read, this]

/-- A mismatching word wins over an expired deadline: the predicate is decided first. -/
theorem begin_mismatch_first (s : Kernel) (choice : Nat) (p : Ptr)
    (expected word : BitVec 32) (deadline now : Time.Timestamp) (readMem : Mem)
    (hr : s.registration = none)
    (hq : s.mem.waiters.any (·.1 == s.mem.current) = false)
    (hw : s.mem.woken.contains s.mem.current = false)
    (read : (readWord choice p).run s.mem = pure (word, readMem)) (differs : word ≠ expected) :
    s.begin choice p expected (some deadline) now = pure (some .mismatch, { s with mem := readMem }) := by
  simp [Kernel.begin, hr, hq, not_woken hw, read, differs]

/-- Timeout: a registered wait may time out exactly when the latest observation has reached
its deadline. -/
theorem timeout_enabled_iff (s : Kernel) (r : Registration) (deadline now : Time.Timestamp)
    (hr : s.registration = some r) (hd : r.deadline = some deadline) :
    s.enabled (some now) .timeout = true ↔ deadline.nanoseconds ≤ now.nanoseconds := by
  simp [Kernel.enabled, hr, hd]

/-- No early timeout: before the deadline, a timeout return is rejected as a model error
and the snapshot is retained unchanged. -/
theorem timeout_not_early (st : State α) (next : Unit → Program α) (r : Registration)
    (deadline now : Time.Timestamp) (hc : st.control = .waiting next)
    (hr : st.kernel.registration = some r) (hd : r.deadline = some deadline)
    (hnow : st.now = some now) (early : now.nanoseconds < deadline.nanoseconds) :
    step st (.normal .timeout) = ⟨some (.error .illegal), st⟩ := by
  have : ¬ deadline.nanoseconds ≤ now.nanoseconds := by omega
  simp [step, hc, Kernel.enabled, hr, hd, hnow, this]

theorem wake_registration (s : Kernel) (p : Ptr) (n : Nat) :
    (s.wake p n).registration = s.registration := by
  unfold Kernel.wake
  split
  · rfl
  all_goals rename_i heq; cases heq

/-- Timeout from a later observation: a paused caller's next awake observation that reaches
the deadline enables timeout, whatever wake the environment delivers at that boundary. -/
theorem observe_enables_timeout (st : State α) (next : Unit → Program α)
    (clock : Time.AwakeEnvironment) (policy : Time.NoCancellation) (r : Registration)
    (deadline : Time.Timestamp) (hc : st.control = .waiting next)
    (henv : st.inputs.environment = .awake clock policy)
    (hr : st.kernel.registration = some r) (hd : r.deadline = some deadline)
    (reached : deadline.nanoseconds ≤ (clock.observe st.observations).nanoseconds) :
    let out := step st .observe
    out.result = none ∧ out.state.now = some (clock.observe st.observations) ∧
      out.state.kernel.enabled out.state.now .timeout = true := by
  simp only [step, hc, withObservation, State.observe, henv]
  split <;> simp [Kernel.enabled, wake_registration, hr, hd, reached]

/-- Wake before timeout: a woken caller before its deadline can only return by wake (or a
permitted spurious return); timeout is not enabled. -/
theorem wake_before_timeout (s : Kernel) (r : Registration) (deadline now : Time.Timestamp)
    (hr : s.registration = some r) (hd : r.deadline = some deadline)
    (hw : s.mem.woken.contains r.owner = true) (early : now.nanoseconds < deadline.nanoseconds) :
    s.enabled (some now) .wake = true ∧ s.enabled (some now) .timeout = false := by
  have : ¬ deadline.nanoseconds ≤ now.nanoseconds := by omega
  have hw' : r.owner ∈ s.mem.woken := Array.contains_iff_mem.mp hw
  simp [Kernel.enabled, hr, hd, hw', this]

/-- Wake at timeout: at the boundary both reasons are enabled ... -/
theorem wake_at_timeout_enabled (s : Kernel) (r : Registration) (deadline now : Time.Timestamp)
    (hr : s.registration = some r) (hd : r.deadline = some deadline)
    (hw : s.mem.woken.contains r.owner = true) (reached : deadline.nanoseconds ≤ now.nanoseconds) :
    s.enabled (some now) .wake = true ∧ s.enabled (some now) .timeout = true := by
  have hw' : r.owner ∈ s.mem.woken := Array.contains_iff_mem.mp hw
  simp [Kernel.enabled, hr, hd, hw', reached]

/-- ... and whichever wins, the resulting interpreter states agree except for the internal
reason log: same memory, queue cleanup, continuation (applied to Unit) and clock. The race
is not observable by the source, which must recheck its predicate and time. -/
theorem wake_at_timeout_indistinguishable (st : State α) (next : Unit → Program α)
    (hc : st.control = .waiting next)
    (hwake : st.kernel.enabled st.now .wake = true)
    (htimeout : st.kernel.enabled st.now .timeout = true) :
    (step st (.normal .wake)).result = none ∧ (step st (.normal .timeout)).result = none ∧
    (step st (.normal .wake)).state =
      { (step st (.normal .timeout)).state with reasons := st.reasons.push .wake } := by
  simp [step, hc, hwake, htimeout, resumeNormal]

/-- Clock-kind distinction at the adapter: a wall-clock (`real`) deadline or duration is
rejected, never reinterpreted as a monotonic awake value. -/
theorem real_deadline_rejected (raw : TimedCall.Timestamp) :
    TimedCall.checkedTimeout (.deadline ⟨raw, .real⟩) = none := by
  simp [TimedCall.checkedTimeout]

theorem real_duration_rejected (raw : TimedCall.Duration) :
    TimedCall.checkedTimeout (.duration ⟨raw, .real⟩) = none := by
  simp [TimedCall.checkedTimeout]

/-- Reading the wall clock fails closed: see `TimedCall.wrong_clock_rejected`. -/
example (io : Io) : TimedCall.clockNow .real io = .fail .unspecified :=
  TimedCall.wrong_clock_rejected io

end DeadlineCaseContracts
