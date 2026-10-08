import ZigLean.Sep.DispatchTemplate

/-!
# Dispatch-template regressions on small machines

`Mach` has the shape the emitter gives a labelled `switch` (`f.loopN` reads `dispatchValueN`,
stores the next selector on `.dispatchN`, `f.againN` repeats only on `.dispatchN`). It checks
the per-state split, the premise report, the `using` automation, the lexicographic measure, the
report of the state where a wrong invariant fails, and the rejection of goals that are not
loop-switch dispatch loops.
-/

open Zig Assn

namespace DispatchTemplateTest

inductive Phase where
  | idle | count | done
  deriving DecidableEq, Inhabited

structure machLocals where
  n : Nat
  acc : Nat
  dispatchValue3 : Phase
  deriving Inhabited

inductive machExit where
  | ret (v : Nat)
  | dispatch3 (v : Phase)

def mach.again3 : machExit → Bool
  | .dispatch3 _ => true
  | _ => false

/-- `idle` moves to `count` (lower rank) or `done`; `count` consumes one unit, back to `idle`. -/
def mach.loop3 : Zig.M machLocals machExit := do
  let dispatchValue := (← get).dispatchValue3
  let dispatchExit ← (do
    match dispatchValue with
    | .idle => if (← get).n = 0 then pure (.dispatch3 .done) else pure (.dispatch3 .count)
    | .count => do
      modify fun s => { s with n := s.n - 1, acc := s.acc + 1 }
      pure (.dispatch3 .idle)
    | .done => pure (.ret (← get).acc) : Zig.M machLocals machExit)
  match dispatchExit with
  | .dispatch3 dispatchValue => do
    modify fun s => { s with dispatchValue3 := dispatchValue }
    pure dispatchExit
  | _ => pure dispatchExit

def rank : Phase → Nat
  | .done => 0 | .count => 1 | .idle => 2

/-- The state-indexed invariant: `count` is entered only with work left. -/
def inv (N : Nat) : Phase → machLocals → Prop
  | .idle, s => s.acc + s.n = N
  | .count, s => s.acc + s.n = N ∧ 0 < s.n
  | .done, s => s.acc = N

def μ (s : machLocals) : Nat × Nat := (s.n, rank s.dispatchValue3)

def post (N : Nat) (e : machExit) (_ : machLocals) : Prop := e = .ret N

/-- One prong of the pure machine, by case analysis and arithmetic. -/
macro "mach_step" : tactic => `(tactic| (
  intro s hk hi
  obtain ⟨n, acc, d⟩ := s
  simp only at hk
  subst hk
  by_cases hn : n = 0 <;>
    simp_all [mach.loop3, mach.again3, inv, μ, rank, post, dispatchLt_iff, zig_unfold,
      get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk] <;> omega))

/-- info: dispatch_template remaining premises (4):
  step.idle : ∀ (s : machLocals),
  s.dispatchValue3 = Phase.idle →
    inv N Phase.idle s →
      ∃ e s',
        mach.loop3.run s = pure (e, s') ∧
          if mach.again3 e = true then DispatchLt (μ s') (μ s) ∧ inv N s'.dispatchValue3 s' else post N e s'
  step.count : ∀ (s : machLocals),
  s.dispatchValue3 = Phase.count →
    inv N Phase.count s →
      ∃ e s',
        mach.loop3.run s = pure (e, s') ∧
          if mach.again3 e = true then DispatchLt (μ s') (μ s) ∧ inv N s'.dispatchValue3 s' else post N e s'
  step.done : ∀ (s : machLocals),
  s.dispatchValue3 = Phase.done →
    inv N Phase.done s →
      ∃ e s',
        mach.loop3.run s = pure (e, s') ∧
          if mach.again3 e = true then DispatchLt (μ s') (μ s) ∧ inv N s'.dispatchValue3 s' else post N e s'
  entry : inv N Phase.idle { n := N, acc := 0, dispatchValue3 := Phase.idle } -/
#guard_msgs in
-- One premise per selector state, named by the state; `exit` closes because `post` is the goal's.
example (N : Nat) : ∃ r, (Zig.loop mach.loop3 mach.again3).run ⟨N, 0, .idle⟩ = pure r ∧
    post N r.1 r.2 := by
  dispatch_template? (inv N) μ (post N)
  case idle => mach_step
  case count => mach_step
  case done => mach_step
  case entry => simp [inv]

-- `using` discharges every state; only `entry` remains.
theorem mach_total (N : Nat) : ∃ r, (Zig.loop mach.loop3 mach.again3).run ⟨N, 0, .idle⟩ = pure r ∧
    r.1 = .ret N := by
  dispatch_template (inv N) μ (post N) using mach_step
  case entry => simp [inv]

/-- A wrong invariant: `count` may be entered without work left. -/
def badInv (N : Nat) : Phase → machLocals → Prop
  | .count, s => s.acc + s.n = N
  | k, s => inv N k s

/-- error: dispatch_template: the invariant/measure is not established at 1 state(s):
  state count: the step tactic failed
    ∀ (s : machLocals),
  s.dispatchValue3 = Phase.count →
    badInv N Phase.count s →
      ∃ e s',
        mach.loop3.run s = pure (e, s') ∧
          if mach.again3 e = true then DispatchLt (μ s') (μ s) ∧ badInv N s'.dispatchValue3 s' else post N e s' -/
#guard_msgs in
example (N : Nat) : ∃ r, (Zig.loop mach.loop3 mach.again3).run ⟨N, 0, .idle⟩ = pure r ∧
    post N r.1 r.2 := by
  dispatch_template (badInv N) μ (post N) using mach_step
  all_goals sorry

/-- A measure that ignores the state rank fails at every non-consuming transition. -/
def flatμ (s : machLocals) : Nat × Nat := (s.n, 0)

/-- error: dispatch_template: the invariant/measure is not established at 1 state(s):
  state idle: the step tactic failed
    ∀ (s : machLocals),
  s.dispatchValue3 = Phase.idle →
    inv N Phase.idle s →
      ∃ e s',
        mach.loop3.run s = pure (e, s') ∧
          if mach.again3 e = true then DispatchLt (flatμ s') (flatμ s) ∧ inv N s'.dispatchValue3 s' else post N e s' -/
#guard_msgs in
example (N : Nat) : ∃ r, (Zig.loop mach.loop3 mach.again3).run ⟨N, 0, .idle⟩ = pure r ∧
    post N r.1 r.2 := by
  dispatch_template (inv N) flatμ (post N) using
    (unfold flatμ; mach_step)
  all_goals sorry

/-! ## Rejected targets -/

/-- An ordinary generated loop: its iterator `f.againN` has no selector field. -/
structure plainLocals where
  n : Nat
  deriving Inhabited

inductive plainExit where
  | rep4 | ret

def plain.again4 : plainExit → Bool
  | .rep4 => true
  | _ => false

def plain.loop4 : Zig.M plainLocals plainExit := do
  if (← get).n = 0 then pure .ret else do modify fun s => { n := s.n - 1 }; pure .rep4

/-- error: dispatch_template: plain.again4 is not a loop-switch dispatch target: plainLocals has no selector field dispatchValue4 -/
#guard_msgs in
example : ∃ r, (Zig.loop plain.loop4 plain.again4).run ⟨3⟩ = pure r ∧ True := by
  dispatch_template (fun (_ : Nat) _ => True) (fun _ => (0, 0)) (fun _ _ => True)

def alwaysAgain (_ : machExit) : Bool := true

/-- error: dispatch_template: the loop iterator DispatchTemplateTest.alwaysAgain is not a generated `f.againN` -/
#guard_msgs in
-- The iterator must be a generated `againN`, not any function.
example : ∃ r, (Zig.loop mach.loop3 alwaysAgain).run ⟨0, 0, .done⟩ = pure r ∧ True := by
  dispatch_template (fun (_ : Phase) _ => True) (fun _ => (0, 0)) (fun _ _ => True)

/-- error: dispatch_template: the goal is not a TotalTriple, Triple or `∃ r, _ = pure r ∧ _` about (Zig.loop body again).run s -/
#guard_msgs in
example : TotalTriple emp (pure 0 : MemM Nat) (fun _ => emp) ∧ True := by
  dispatch_template (fun (_ : Phase) _ => emp) (fun (_ : machLocals) => (0, 0)) (fun _ _ => emp)

/-! ## Integer selectors -/

structure wordLocals where
  dispatchValue7 : BitVec 8
  deriving Inhabited

inductive wordExit where
  | ret (v : BitVec 8)
  | dispatch7 (v : BitVec 8)

def word.again7 : wordExit → Bool
  | .dispatch7 _ => true
  | _ => false

/-- `0 → 1 → 2 → return 42`; other selectors return 9. -/
def word.loop7 : Zig.M wordLocals wordExit := do
  let dispatchValue := (← get).dispatchValue7
  let dispatchExit ← (do
    if dispatchValue = 0 then pure (.dispatch7 1)
    else if dispatchValue = 1 then pure (.dispatch7 2)
    else if dispatchValue = 2 then pure (.ret 42)
    else pure (.ret 9) : Zig.M wordLocals wordExit)
  match dispatchExit with
  | .dispatch7 dispatchValue => do
    modify fun s => { s with dispatchValue7 := dispatchValue }
    pure dispatchExit
  | _ => pure dispatchExit

/-- error: dispatch_template: the selector type BitVec 8 is not an enumeration; name its states with `states [v₁, …]` -/
#guard_msgs in
example : ∃ r, (Zig.loop word.loop7 word.again7).run ⟨0⟩ = pure r ∧ True := by
  dispatch_template (fun (_ : BitVec 8) _ => True) (fun _ => (0, 0)) (fun _ _ => True)

def wordInv (k : BitVec 8) (_ : wordLocals) : Prop := k.toNat ≤ 2

macro "word_step" : tactic => `(tactic| (
  intro s hk hi
  obtain ⟨d⟩ := s
  simp only at hk
  subst hk
  simp_all [word.loop7, word.again7, wordInv, dispatchLt_iff, zig_unfold, get, getThe,
    MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk]))

/-- info: dispatch_template remaining premises (4):
  step.0 : ∀ (s : wordLocals),
  s.dispatchValue7 = 0 →
    wordInv 0 s →
      ∃ e s',
        word.loop7.run s = pure (e, s') ∧
          if word.again7 e = true then
            DispatchLt (0, 2 - s'.dispatchValue7.toNat) (0, 2 - s.dispatchValue7.toNat) ∧
              wordInv s'.dispatchValue7 s'
          else e = wordExit.ret 42
  step.1 : ∀ (s : wordLocals),
  s.dispatchValue7 = 1 →
    wordInv 1 s →
      ∃ e s',
        word.loop7.run s = pure (e, s') ∧
          if word.again7 e = true then
            DispatchLt (0, 2 - s'.dispatchValue7.toNat) (0, 2 - s.dispatchValue7.toNat) ∧
              wordInv s'.dispatchValue7 s'
          else e = wordExit.ret 42
  step.2 : ∀ (s : wordLocals),
  s.dispatchValue7 = 2 →
    wordInv 2 s →
      ∃ e s',
        word.loop7.run s = pure (e, s') ∧
          if word.again7 e = true then
            DispatchLt (0, 2 - s'.dispatchValue7.toNat) (0, 2 - s.dispatchValue7.toNat) ∧
              wordInv s'.dispatchValue7 s'
          else e = wordExit.ret 42
  step.other : ∀ k ∉ [0, 1, 2],
  ∀ (s : wordLocals),
    s.dispatchValue7 = k →
      wordInv k s →
        ∃ e s',
          word.loop7.run s = pure (e, s') ∧
            if word.again7 e = true then
              DispatchLt (0, 2 - s'.dispatchValue7.toNat) (0, 2 - s.dispatchValue7.toNat) ∧
                wordInv s'.dispatchValue7 s'
            else e = wordExit.ret 42 -/
#guard_msgs in
-- A state-ranked measure `(0, 2 - selector)`; listed states and the excluded rest.
example : ∃ r, (Zig.loop word.loop7 word.again7).run ⟨0⟩ = pure r ∧ r.1 = .ret 42 := by
  dispatch_template? wordInv (fun s => (0, 2 - s.dispatchValue7.toNat)) (fun e _ => e = .ret 42)
    states [0, 1, 2]
  case «0» => word_step
  case «1» => word_step
  case «2» => word_step
  case other =>
    intro k hk s hs hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    exfalso
    simp only [wordInv] at hi
    bv_omega
  case entry => simp [wordInv]

end DispatchTemplateTest

-- Only the standard axioms.
/-- info: 'DispatchTemplateTest.mach_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DispatchTemplateTest.mach_total
