import ZigLean.Conc.Progress

open Zig

deriving instance DecidableEq for Except

private def check [DecidableEq α] [Repr α] (name : String) (actual expected : α) : IO Unit :=
  unless actual = expected do
    throw (IO.userError s!"{name}: expected {reprStr expected}, got {reprStr actual}")

private def value (r : Sched.Out α) : Option (Except Error α) := r.map (·.map Prod.fst)

private def spinForever : ConcM Unit Unit := do
  let _ ← (Zig.loop (spinLoopHintC : CM Unit Unit Unit) (fun _ => true)).run ()
  pure ()

private def observedBeforeJoin : ConcM Unit Nat := do
  let .ok tid ← ConcM.sync (.spawn ()) | pure 0
  spinLoopHint
  spinLoopHint
  let observed ← ConcM.liftMem (do pure (← get).allocs)
  let _ ← ConcM.sync (.join tid)
  pure observed

-- Kernel-checkable safety contracts for the source model operations, for any protocol.
example {Tgt γ : Type} {P : Conc.Proto Tgt γ} {t : ThreadId} {G : ThreadId → γ}
    {m : Mem} {n : Nat} {Q : Unit → (ThreadId → γ) → Mem → Nat → Prop}
    (h : ∀ k, n = k + 1 → ∃ g, P.inv (Conc.upd G t g) m ∧
      ∀ G₁ m₁, G₁ t = g → P.inv G₁ m₁ → Q () G₁ { m₁ with current := t } k) :
    P.WP t (spinLoopHint : ConcM Tgt Unit) Q G m n :=
  Conc.Proto.WP.spinLoopHint h

example : threadYieldResult 0 = .ok () := rfl
example : threadYieldResult 1 = .error "SystemCannotYield" := rfl

private def hintProtocol : Conc.Proto Unit Unit where
  inv := fun _ m => m.threads = ({} : Mem).threads
  init := fun _ _ => False
  fin := fun _ => True
  strict := true
  spawnFails := true

private theorem hintProtocol_joined {G : ThreadId → Unit} {m : Mem}
    (h : hintProtocol.inv G m) : Conc.Proto.joinedAll 0 m := by
  unfold Conc.Proto.joinedAll
  change m.threads = ({} : Mem).threads at h
  rw [h]
  simp

/-- Kernel-checkable absence of model failures for a source spin hint, for every oracle and
fuel. No result is allowed; this is not an eventual-completion theorem. -/
theorem spin_all_schedules_safe (env : Env) (fuel : Nat) (o : Nat → Nat) (e : Error) :
    (Sched.run env (fun _ => pure ()) fuel o (spinLoopHint : ConcM Unit Unit) {}).run ≠
      some (.error e) := by
  apply Conc.Proto.run_safe (P := hintProtocol) (QM := fun _ G m _ => hintProtocol.inv G m)
    env (fun _ => rfl) (fun _ => pure ()) (fun _ => ()) rfl
  · intro tgt g h
    exact False.elim h
  · intro v G m d h
    exact hintProtocol_joined h
  · rfl
  · intro n
    apply Conc.Proto.WP.spinLoopHint
    intro k hk
    exact ⟨(), rfl, fun G₁ m₁ hg hi => hi⟩

/-- An ordinary source error returned by yield is allowed; no oracle produces a model panic. -/
theorem yield_all_schedules_safe (env : Env) (fuel : Nat) (o : Nat → Nat) (e : Error) :
    (Sched.run env (fun _ => pure ()) fuel o (threadYield : ConcM Unit (Except ErrName Unit)) {}).run ≠
      some (.error e) := by
  apply Conc.Proto.run_safe (P := hintProtocol) (QM := fun _ G m _ => hintProtocol.inv G m)
    env (fun _ => rfl) (fun _ => pure ()) (fun _ => ()) rfl
  · intro tgt g h
    exact False.elim h
  · intro v G m d h
    exact hintProtocol_joined h
  · rfl
  · intro n
    apply Conc.Proto.WP.threadYield
    intro k hk
    exact ⟨(), rfl, fun G₁ m₁ hg hi c hc => hi⟩

-- Mutants that make hints pure, force success, or force handoff fail these assertions.
def main : IO Unit := do
  let run := fun {α : Type} (fuel : Nat) (o : Nat → Nat) (x : ConcM Unit α) =>
    value (Sched.runTrace ⟨.any, .available⟩ (fun _ => pure ()) fuel o x {}).1
  check "spin depth zero is no result" (run 0 (fun _ => 0) spinLoopHint) none
  check "yield depth zero is no result" (run 0 (fun _ => 0) threadYield) none
  check "yield source success" (run 10 (fun _ => 0) threadYield) (some (.ok (.ok ())))
  check "yield source failure is an ordinary value" (run 10 (fun _ => 1) threadYield)
    (some (.ok (.error "SystemCannotYield")))
  let (_, trace) := Sched.runTrace ⟨.any, .available⟩ (fun _ => pure ()) 10 (fun _ => 0)
    (spinLoopHint : ConcM Unit Unit) {}
  check "spin has a scheduler opportunity" trace #[1]
  for fuel in [0, 1, 2, 10, 100] do
    check "unbounded idle loop stays no result" (run fuel (fun _ => 0) spinForever) none
  let dispatch : Unit → ConcM Unit Unit := fun _ =>
    ConcM.liftMem (modify fun m => { m with allocs := 42 })
  check "hints permit immediate same-thread continuation"
    (value (Sched.runTrace ⟨.any, .available⟩ dispatch 20 (fun _ => 0) observedBeforeJoin {}).1) (some (.ok 0))
  check "hints permit another ready thread to run"
    (value (Sched.runTrace ⟨.any, .available⟩ dispatch 20 (fun _ => 1) observedBeforeJoin {}).1) (some (.ok 42))
  let m : Mem := { allocs := 9 }
  let after := (Sched.runTrace ⟨.any, .available⟩ (fun _ => pure ()) 10 (fun _ => 0)
    (spinLoopHint : ConcM Unit Unit) m).1
  check "spin adds no access or clock edge"
    (after.map fun r => r.map fun (_, m') => (m'.allocs, m'.footprint.size, m'.clocks))
    (some (.ok (9, 0, m.clocks)))
  IO.println "Progress hint regressions passed"
