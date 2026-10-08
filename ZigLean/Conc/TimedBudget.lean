import ZigLean.Conc.TimedSched

/-!
Opt-in solver budget client over the selected timed interpreter (C04). It is not imported
by the runtime umbrella and no translated Zig call targets it.

Clock kinds are separate types. `Time.Timestamp` is the awake monotonic observation used
for every deadline decision; `MonoDuration` is a monotonic budget length; `WallTimestamp`
is a signed wall-clock label with no ordering contract and no coercion to either. A
budget deadline is `start + budget` over one monotonic observation, and an unrepresentable
sum is an explicit outcome rather than a clamp.

Safety (`*_sound`) holds for every oracle, fuel and selected awake clock, including an
equal clock that never advances: no fairness is assumed. The single liveness statement
(`loop_decides`) requires an explicit premise that the monotonic clock reaches the
deadline at a stated observation index within the iteration cap.
-/
namespace Zig.TimedBudget

open TimedSched

/-- Wall-clock (realtime) timestamp: signed and free to jump in either direction. -/
structure WallTimestamp where
  nanoseconds : Int
  deriving DecidableEq, Repr

/-- A monotonic duration. Not a timestamp: it only becomes a deadline against an observation. -/
structure MonoDuration where
  nanoseconds : Nat
  deriving DecidableEq, Repr

/-- Overflow beyond the i96 timestamp range is rejected, never clamped. -/
def MonoDuration.deadlineFrom (budget : MonoDuration) (start : Time.Timestamp) :
    Option Time.Timestamp :=
  Time.Timestamp.ofNat (start.nanoseconds + budget.nanoseconds)

/-- `observed` fields are the monotonic observation on which the decision was taken. -/
inductive Verdict (σ ρ : Type) where
  | solved (answer : ρ) (observed : Time.Timestamp)
  | expired (state : σ) (observed : Time.Timestamp)
  /-- The iteration cap ran out first: neither a timeout nor a result. -/
  | capped (state : σ)
  | unrepresentable

def Verdict.decided : Verdict σ ρ → Bool
  | .solved .. | .expired .. => true
  | _ => false

variable {σ ρ : Type}

/-- Solver states reachable from `start` through unsolved steps. -/
inductive Reachable (advance : σ → Except σ ρ) (start : σ) : σ → Prop
  | refl : Reachable advance start start
  | tail {a b : σ} : Reachable advance start a → advance a = .error b →
      Reachable advance start b

/-- Check the monotonic clock before every solver step. -/
def loop (advance : σ → Except σ ρ) (deadline : Time.Timestamp) :
    Nat → σ → Program (Verdict σ ρ)
  | 0, s => .done (.capped s)
  | n + 1, s => .observe fun now =>
    if deadline.nanoseconds ≤ now.nanoseconds then .done (.expired s now)
    else match advance s with
      | .ok answer => .done (.solved answer now)
      | .error s' => loop advance deadline n s'

/-- As `loop`, but an unsolved step pauses on the caller's word until a wake, the same
deadline, or a spurious return. Every return rechecks the monotonic clock. -/
def pausedLoop (advance : σ → Except σ ρ) (deadline : Time.Timestamp) (word : Ptr) :
    Nat → σ → Program (Verdict σ ρ)
  | 0, s => .done (.capped s)
  | n + 1, s => .observe fun now =>
    if deadline.nanoseconds ≤ now.nanoseconds then .done (.expired s now)
    else match advance s with
      | .ok answer => .done (.solved answer now)
      | .error s' => .wait word 0 (.deadline deadline) fun _ => pausedLoop advance deadline word n s'

/-- Observe a start, derive the deadline from the monotonic budget, then run `body`. -/
def within (budget : MonoDuration) (body : Time.Timestamp → Program (Verdict σ ρ)) :
    Program (Verdict σ ρ) :=
  .observe fun start => match budget.deadlineFrom start with
    | none => .done .unrepresentable
    | some deadline => body deadline

def solveWithin (advance : σ → Except σ ρ) (budget : MonoDuration) (cap : Nat) (s : σ) :
    Program (Verdict σ ρ) :=
  within budget fun deadline => loop advance deadline cap s

/-- What a returned outcome guarantees about the solver and the monotonic observations. -/
def Spec (advance : σ → Except σ ρ) (clock : Time.AwakeEnvironment)
    (deadline : Time.Timestamp) (start : σ) : Verdict σ ρ → Prop
  | .solved answer now => (∃ s, Reachable advance start s ∧ advance s = .ok answer) ∧
      now.nanoseconds < deadline.nanoseconds ∧ ∃ i, clock.observe i = now
  | .expired s now => Reachable advance start s ∧
      deadline.nanoseconds ≤ now.nanoseconds ∧ ∃ i, clock.observe i = now
  | .capped s => Reachable advance start s
  | .unrepresentable => False

/-! ## Generic soundness of `resume` from a one-step invariant -/

/-- Any state invariant preserved by every single event, whose source results satisfy `P`,
bounds every source result of `resume`, for every oracle and fuel. -/
theorem resume_sound {α : Type} (I : State α → Prop) (P : α → Prop)
    (bookkeeping : ∀ st (c : Nat) (t : Array Nat), I st → I { st with choices := c, trace := t })
    (preserve : ∀ st ev, I st →
      (∀ o, (step st ev).result = some (.ok o) → P o) ∧
      ((step st ev).result = none → I (step st ev).state)) :
    ∀ (oracle : Nat → Nat) (fuel : Nat) (st : State α), I st →
      ∀ o, (resume oracle fuel st).result = some (.ok o) → P o := by
  intro oracle fuel
  induction fuel with
  | zero => intro st _ o h; simp [resume] at h
  | succ fuel ih =>
    intro st hI o h
    have hI' := bookkeeping st (st.choices + 1) (st.trace.push st.events.size) hI
    simp only [resume] at h
    split at h
    · exact (preserve _ _ hI').1 o h
    · rename_i hr
      exact ih _ ((preserve _ _ hI').2 hr) o h

/-! ## Invariants of the budget programs -/

/-- Control states of `pausedLoop`, including the paused continuation. -/
inductive PausedControl (advance : σ → Except σ ρ) (clock : Time.AwakeEnvironment)
    (deadline : Time.Timestamp) (word : Ptr) (start : σ) : Control (Verdict σ ρ) → Prop
  | loop {n s} : Reachable advance start s →
      PausedControl advance clock deadline word start (.running (pausedLoop advance deadline word n s))
  | wait {n s} : Reachable advance start s →
      PausedControl advance clock deadline word start
        (.running (.wait word 0 (.deadline deadline) fun _ => pausedLoop advance deadline word n s))
  | waiting {n s} : Reachable advance start s →
      PausedControl advance clock deadline word start
        (.waiting fun _ => pausedLoop advance deadline word n s)
  | done {o} : Spec advance clock deadline start o →
      PausedControl advance clock deadline word start (.running (.done o))

def PausedInv (advance : σ → Except σ ρ) (clock : Time.AwakeEnvironment)
    (deadline : Time.Timestamp) (word : Ptr) (start : σ) (st : State (Verdict σ ρ)) : Prop :=
  (∃ policy, st.inputs.environment = .awake clock policy) ∧
    PausedControl advance clock deadline word start st.control

/-- An awake observation reports `clock.observe` at the cursor and changes no inputs or control. -/
theorem observe_awake {α : Type} {st : State α} {clock : Time.AwakeEnvironment}
    {policy : Time.NoCancellation} (h : st.inputs.environment = .awake clock policy) :
    ∃ st', st.observe = .ok (clock.observe st.observations, st') ∧
      st'.inputs = st.inputs ∧ st'.control = st.control := by
  simp only [State.observe, h]
  exact ⟨_, rfl, rfl, rfl⟩

private theorem decide_observed (advance : σ → Except σ ρ) (clock : Time.AwakeEnvironment)
    (deadline : Time.Timestamp) (start s : σ) (i : Nat) (hs : Reachable advance start s)
    (continue_ : σ → Program (Verdict σ ρ)) (Q : Program (Verdict σ ρ) → Prop)
    (hdone : ∀ o, Spec advance clock deadline start o → Q (.done o))
    (hcont : ∀ s', Reachable advance start s' → Q (continue_ s')) :
    Q (if deadline.nanoseconds ≤ (clock.observe i).nanoseconds then
        .done (.expired s (clock.observe i))
      else match advance s with
        | .ok answer => .done (.solved answer (clock.observe i))
        | .error s' => continue_ s') := by
  split
  · exact hdone _ ⟨hs, by assumption, i, rfl⟩
  · cases ha : advance s with
    | ok answer => exact hdone _ ⟨⟨s, hs, ha⟩, by omega, i, rfl⟩
    | error s' => exact hcont s' (.tail hs ha)

theorem pausedInv_step (advance : σ → Except σ ρ) (clock : Time.AwakeEnvironment)
    (deadline : Time.Timestamp) (word : Ptr) (start : σ) (st : State (Verdict σ ρ))
    (ev : Event) (hI : PausedInv advance clock deadline word start st) :
    (∀ o, (step st ev).result = some (.ok o) → Spec advance clock deadline start o) ∧
    ((step st ev).result = none → PausedInv advance clock deadline word start (step st ev).state) := by
  obtain ⟨⟨policy, henv⟩, hc⟩ := hI
  obtain ⟨st₁, hobs, hin, hctl⟩ := observe_awake henv
  have henv₁ : st₁.inputs.environment = .awake clock policy := hin ▸ henv
  generalize hcs : st.control = c at hc
  cases hc with
  | @done o hspec => cases ev <;> simp_all [step]
  | @loop n s hs =>
    cases n with
    | zero => cases ev <;> simp_all [step, pausedLoop, Spec]
    | succ n =>
      cases ev with
      | observe | normal => simp [step, hcs, pausedLoop]
      | run =>
        simp only [step, hcs, pausedLoop, withObservation, hobs]
        refine ⟨by simp, fun _ => ⟨⟨policy, henv₁⟩, ?_⟩⟩
        exact decide_observed advance clock deadline start s _ hs _
          (PausedControl advance clock deadline word start ∘ Control.running)
          (fun _ h => .done h) (fun _ h => .wait h)
  | @wait n s hs =>
    cases ev with
    | observe | normal => simp [step, hcs]
    | run =>
      simp only [step, hcs, withObservation, hobs, Time.Timeout.resolve]
      split
      · exact ⟨by simp, fun _ => ⟨⟨policy, henv₁⟩, by simp [hctl, hcs]; exact .wait hs⟩⟩
      · exact ⟨by simp, by simp⟩
      · rename_i reason kernel _
        cases reason with
        | none => exact ⟨by simp, fun _ => ⟨⟨policy, henv₁⟩, .waiting hs⟩⟩
        | some r => exact ⟨by simp, fun _ => ⟨⟨policy, henv₁⟩, .loop hs⟩⟩
  | @waiting n s hs =>
    cases ev with
    | run => simp [step, hcs]
    | observe =>
      simp only [step, hcs, withObservation, hobs]
      exact ⟨by simp, fun _ => ⟨⟨policy, henv₁⟩, by simp [hctl, hcs]; exact .waiting hs⟩⟩
    | normal reason =>
      simp only [step, hcs]
      split
      · exact ⟨by simp, fun _ => ⟨⟨policy, henv⟩, .loop hs⟩⟩
      · exact ⟨by simp, by simp⟩

/-- Safety of the paused solver path: whatever the oracle, fuel, wake schedule and selected
monotone clock, a returned outcome is correct. A model error (for example an invalid word)
is not a source outcome and is not constrained here. -/
theorem pausedLoop_sound (advance : σ → Except σ ρ) (deadline : Time.Timestamp) (word : Ptr)
    (cap : Nat) (start : σ) (inputs : Inputs) (clock : Time.AwakeEnvironment)
    (policy : Time.NoCancellation) (henv : inputs.environment = .awake clock policy)
    (oracle : Nat → Nat) (fuel : Nat) (mem : Mem) (o : Verdict σ ρ)
    (h : (run inputs fuel oracle (pausedLoop advance deadline word cap start) mem).result =
      some (.ok o)) :
    Spec advance clock deadline start o :=
  resume_sound (PausedInv advance clock deadline word start) _
    (fun _ _ _ hI => hI) (pausedInv_step advance clock deadline word start)
    oracle fuel _ ⟨⟨policy, henv⟩, .loop .refl⟩ o h

/-! ## The non-pausing loop -/

/-- `loop` is `pausedLoop` without the pause; its control states are a subset. -/
inductive LoopControl (advance : σ → Except σ ρ) (clock : Time.AwakeEnvironment)
    (deadline : Time.Timestamp) (start : σ) : Control (Verdict σ ρ) → Prop
  | loop {n s} : Reachable advance start s →
      LoopControl advance clock deadline start (.running (loop advance deadline n s))
  | done {o} : Spec advance clock deadline start o →
      LoopControl advance clock deadline start (.running (.done o))

def LoopInv (advance : σ → Except σ ρ) (clock : Time.AwakeEnvironment)
    (deadline : Time.Timestamp) (start : σ) (st : State (Verdict σ ρ)) : Prop :=
  (∃ policy, st.inputs.environment = .awake clock policy) ∧
    LoopControl advance clock deadline start st.control

theorem loopInv_step (advance : σ → Except σ ρ) (clock : Time.AwakeEnvironment)
    (deadline : Time.Timestamp) (start : σ) (st : State (Verdict σ ρ)) (ev : Event)
    (hI : LoopInv advance clock deadline start st) :
    (∀ o, (step st ev).result = some (.ok o) → Spec advance clock deadline start o) ∧
    ((step st ev).result = none → LoopInv advance clock deadline start (step st ev).state) := by
  obtain ⟨⟨policy, henv⟩, hc⟩ := hI
  obtain ⟨st₁, hobs, hin, _⟩ := observe_awake henv
  have henv₁ : st₁.inputs.environment = .awake clock policy := hin ▸ henv
  generalize hcs : st.control = c at hc
  cases hc with
  | @done o hspec => cases ev <;> simp_all [step]
  | @loop n s hs =>
    cases n with
    | zero => cases ev <;> simp_all [step, loop, Spec]
    | succ n =>
      cases ev with
      | observe | normal => simp [step, hcs, loop]
      | run =>
        simp only [step, hcs, loop, withObservation, hobs]
        refine ⟨by simp, fun _ => ⟨⟨policy, henv₁⟩, ?_⟩⟩
        exact decide_observed advance clock deadline start s _ hs _
          (LoopControl advance clock deadline start ∘ Control.running)
          (fun _ h => .done h) (fun _ h => .loop h)

theorem loop_sound (advance : σ → Except σ ρ) (deadline : Time.Timestamp) (cap : Nat)
    (start : σ) (inputs : Inputs) (clock : Time.AwakeEnvironment)
    (policy : Time.NoCancellation) (henv : inputs.environment = .awake clock policy)
    (oracle : Nat → Nat) (fuel : Nat) (mem : Mem) (o : Verdict σ ρ)
    (h : (run inputs fuel oracle (loop advance deadline cap start) mem).result = some (.ok o)) :
    Spec advance clock deadline start o :=
  resume_sound (LoopInv advance clock deadline start) _
    (fun _ _ _ hI => hI) (loopInv_step advance clock deadline start)
    oracle fuel _ ⟨⟨policy, henv⟩, .loop .refl⟩ o h

/-- One `resume` step of a running program takes the only enabled event, `run`. -/
theorem resume_running {α : Type} (oracle : Nat → Nat) (fuel : Nat) (st : State α)
    (program : Program α) (hc : st.control = .running program) :
    resume oracle (fuel + 1) st =
      let st' := { st with choices := st.choices + 1, trace := st.trace.push 1 }
      match (step st' .run).result with
      | some _ => step st' .run
      | none => resume oracle fuel (step st' .run).state := by
  have hev : st.events = #[.run] := by simp [State.events, hc]
  have hpick : ∀ i, (#[Event.run] : Array Event)[i % 1]! = .run := by
    intro i; rw [Nat.mod_one]; rfl
  simp only [resume, hev, List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
    hpick]
  rfl

/-- Liveness under an explicit clock premise only: if the monotonic observation with index
`cursor + k` reaches the deadline and `k` is below the remaining iteration cap, the loop
returns `solved` or `expired` within `k + 2` scheduler steps. No fairness is involved:
a running caller has exactly one enabled event. -/
theorem loop_decides_from (advance : σ → Except σ ρ) (deadline : Time.Timestamp)
    (clock : Time.AwakeEnvironment) (policy : Time.NoCancellation) (oracle : Nat → Nat) :
    ∀ (k n fuel : Nat) (s : σ) (st : State (Verdict σ ρ)),
      st.inputs.environment = .awake clock policy →
      st.control = .running (loop advance deadline n s) →
      deadline.nanoseconds ≤ (clock.observe (st.observations + k)).nanoseconds →
      k < n → k + 2 ≤ fuel →
      ∃ o, (resume oracle fuel st).result = some (.ok o) ∧ o.decided = true := by
  intro k
  induction k with
  | zero =>
    intro n fuel s st henv hc hd hk hf
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨fuel, rfl⟩ : ∃ m, fuel = m + 2 := ⟨fuel - 2, by omega⟩
    rw [resume_running oracle _ st _ hc]
    simp only [Nat.add_zero] at hd
    simp [step, hc, loop, withObservation, State.observe, henv, hd,
      resume_running, Verdict.decided]
  | succ k ih =>
    intro n fuel s st henv hc hd hk hf
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨fuel, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
    rw [resume_running oracle _ st _ hc]
    by_cases hnow : deadline.nanoseconds ≤ (clock.observe st.observations).nanoseconds
    · obtain ⟨fuel, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
      simp [step, hc, loop, withObservation, State.observe, henv, hnow,
        resume_running, Verdict.decided]
    · cases ha : advance s with
      | ok answer =>
        obtain ⟨fuel, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by omega⟩
        simp [step, hc, loop, withObservation, State.observe, henv, hnow, ha,
          resume_running, Verdict.decided]
      | error s' =>
        simp only [step, hc, loop, withObservation, State.observe, henv, hnow, ha,
          ite_false]
        exact ih n fuel s' _ henv rfl (by simpa [Nat.add_assoc, Nat.add_comm 1 k] using hd)
          (by omega) (by omega)

theorem loop_decides (advance : σ → Except σ ρ) (deadline : Time.Timestamp) (cap : Nat)
    (start : σ) (inputs : Inputs) (clock : Time.AwakeEnvironment)
    (policy : Time.NoCancellation) (henv : inputs.environment = .awake clock policy)
    (oracle : Nat → Nat) (fuel : Nat) (mem : Mem) (k : Nat)
    (reached : deadline.nanoseconds ≤ (clock.observe k).nanoseconds)
    (withinCap : k < cap) (enoughFuel : k + 2 ≤ fuel) :
    ∃ o, (run inputs fuel oracle (loop advance deadline cap start) mem).result = some (.ok o) ∧
      o.decided = true :=
  loop_decides_from advance deadline clock policy oracle k cap fuel start _ henv rfl
    (by simpa using reached) withinCap enoughFuel

/-! ## Budget from a monotonic duration -/

/-- What `within` adds: the deadline is a representable `start + budget` for an actual
monotonic observation `start`; otherwise the outcome is `unrepresentable`. -/
def WithinSpec (budget : MonoDuration) (clock : Time.AwakeEnvironment)
    (spec : Time.Timestamp → Verdict σ ρ → Prop) (o : Verdict σ ρ) : Prop :=
  (o = .unrepresentable ∧ ∃ i, budget.deadlineFrom (clock.observe i) = none) ∨
  ∃ i deadline, budget.deadlineFrom (clock.observe i) = some deadline ∧
    deadline.nanoseconds = (clock.observe i).nanoseconds + budget.nanoseconds ∧
    spec deadline o

theorem deadlineFrom_nanoseconds {budget : MonoDuration} {start deadline : Time.Timestamp}
    (h : budget.deadlineFrom start = some deadline) :
    deadline.nanoseconds = start.nanoseconds + budget.nanoseconds := by
  unfold MonoDuration.deadlineFrom Time.Timestamp.ofNat at h
  split at h
  · cases h; rfl
  · cases h

/-- Lift a deadline-indexed body invariant through `within`'s start observation. -/
theorem within_sound (budget : MonoDuration) (clock : Time.AwakeEnvironment)
    (body : Time.Timestamp → Program (Verdict σ ρ))
    (I : Time.Timestamp → State (Verdict σ ρ) → Prop) (spec : Time.Timestamp → Verdict σ ρ → Prop)
    (enter : ∀ deadline st, (∃ policy, st.inputs.environment = .awake clock policy) →
      st.control = .running (body deadline) → I deadline st)
    (bookkeeping : ∀ d st (c : Nat) (t : Array Nat), I d st → I d { st with choices := c, trace := t })
    (preserve : ∀ d st ev, I d st →
      (∀ o, (step st ev).result = some (.ok o) → spec d o) ∧
      ((step st ev).result = none → I d (step st ev).state))
    (inputs : Inputs) (policy : Time.NoCancellation)
    (henv : inputs.environment = .awake clock policy)
    (oracle : Nat → Nat) (fuel : Nat) (mem : Mem) (o : Verdict σ ρ)
    (h : (run inputs fuel oracle (within budget body) mem).result = some (.ok o)) :
    WithinSpec budget clock spec o := by
  let J : State (Verdict σ ρ) → Prop := fun st =>
    ((∃ policy, st.inputs.environment = .awake clock policy) ∧
      st.control = .running (within budget body)) ∨
    ((∃ i, budget.deadlineFrom (clock.observe i) = none) ∧
      st.control = .running (.done .unrepresentable)) ∨
    ∃ i deadline, budget.deadlineFrom (clock.observe i) = some deadline ∧ I deadline st
  refine resume_sound J (WithinSpec budget clock spec) ?_ ?_ oracle fuel _
    (.inl ⟨⟨policy, henv⟩, rfl⟩) o h
  · rintro st c t (hJ | hJ | ⟨i, d, hd, hI⟩)
    · exact .inl hJ
    · exact .inr (.inl hJ)
    · exact .inr (.inr ⟨i, d, hd, bookkeeping d st c t hI⟩)
  · rintro st ev (⟨⟨pol, hen⟩, hc⟩ | ⟨hi, hc⟩ | ⟨i, d, hd, hI⟩)
    · obtain ⟨st₁, hobs, hin, _⟩ := observe_awake hen
      cases ev with
      | observe | normal => simp_all [step, within]
      | run =>
        simp only [step, hc, within, withObservation, hobs]
        refine ⟨by simp, fun _ => ?_⟩
        cases hdl : budget.deadlineFrom (clock.observe st.observations) with
        | none => exact .inr (.inl ⟨⟨_, hdl⟩, rfl⟩)
        | some d =>
          exact .inr (.inr ⟨_, d, hdl, enter d _ ⟨pol, hin ▸ hen⟩ rfl⟩)
    · cases ev <;> simp_all [step, WithinSpec]
    · have hp := preserve d st ev hI
      exact ⟨fun o ho => .inr ⟨i, d, hd, deadlineFrom_nanoseconds hd, hp.1 o ho⟩,
        fun hn => .inr (.inr ⟨i, d, hd, hp.2 hn⟩)⟩

/-- Solver budget path: from a monotonic duration budget, the result is either
`unrepresentable` (overflowing start + budget) or satisfies `Spec` against the deadline
`start + budget` for an actual monotonic observation `start`. -/
theorem solveWithin_sound (advance : σ → Except σ ρ) (budget : MonoDuration) (cap : Nat)
    (start : σ) (inputs : Inputs) (clock : Time.AwakeEnvironment)
    (policy : Time.NoCancellation) (henv : inputs.environment = .awake clock policy)
    (oracle : Nat → Nat) (fuel : Nat) (mem : Mem) (o : Verdict σ ρ)
    (h : (run inputs fuel oracle (solveWithin advance budget cap start) mem).result =
      some (.ok o)) :
    WithinSpec budget clock (fun d => Spec advance clock d start) o :=
  within_sound budget clock _ (fun d => LoopInv advance clock d start) _
    (fun _ _ hen hc => ⟨hen, hc ▸ .loop .refl⟩) (fun _ _ _ _ hI => hI)
    (fun d => loopInv_step advance clock d start) inputs policy henv oracle fuel mem o h

/-- The paused solver budget path, from a monotonic duration budget. -/
theorem pausedWithin_sound (advance : σ → Except σ ρ) (budget : MonoDuration) (word : Ptr)
    (cap : Nat) (start : σ) (inputs : Inputs) (clock : Time.AwakeEnvironment)
    (policy : Time.NoCancellation) (henv : inputs.environment = .awake clock policy)
    (oracle : Nat → Nat) (fuel : Nat) (mem : Mem) (o : Verdict σ ρ)
    (h : (run inputs fuel oracle
      (within budget fun d => pausedLoop advance d word cap start) mem).result = some (.ok o)) :
    WithinSpec budget clock (fun d => Spec advance clock d start) o :=
  within_sound budget clock _
    (fun d => PausedInv advance clock d word start) _
    (fun _ _ hen hc => ⟨hen, hc ▸ .loop .refl⟩) (fun _ _ _ _ hI => hI)
    (fun d => pausedInv_step advance clock d word start) inputs policy henv oracle fuel mem o h

end Zig.TimedBudget
