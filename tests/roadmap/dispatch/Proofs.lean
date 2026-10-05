import ZigLean.Loop

/-! Kernel-checked invariant/measure example. Dispatch values and captures are separate;
a foreign dispatch/exit must stop this target's iterator. No compiler proof axioms. -/
namespace DispatchProof

structure State where
  selector : Nat
  captured : Nat

inductive Exit where
  | dispatch (selector : Nat)
  | done (captured : Nat)
  | foreign (selector : Nat)

def next : Exit → Option Nat
  | .dispatch value => some value
  | _ => none

def body : Zig.M State Exit := do
  let s ← get
  if s.selector = 0 then pure (.done s.captured)
  else
    let value := s.selector - 1
    modify fun s => { s with selector := value }
    pure (.dispatch value)

def inv (captured : Nat) (s : State) : Prop := s.captured = captured

def post (captured : Nat) (r : Exit × State) : Prop :=
  r.1 = .done captured ∧ r.2.selector = 0 ∧ r.2.captured = captured

/-- The selector decreases on each own-target dispatch; fixed captures are invariant. -/
theorem terminates (selector captured : Nat) :
    ∃ r, (Zig.loop body (fun e => (next e).isSome)).run ⟨selector, captured⟩ = pure r ∧
      post captured r := by
  apply Zig.loop_dispatch_spec body next (inv captured) State.selector (post captured) ?_
    ⟨selector, captured⟩ rfl
  intro s hs
  by_cases h : s.selector = 0
  · refine ⟨.done s.captured, s, ?_, ?_⟩
    · simp [body, h, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
        ExceptT.mk, Option.bind]
    · simpa [next, post] using
        (show s.captured = captured ∧ s.selector = 0 ∧ s.captured = captured from ⟨hs, h, hs⟩)
  · let s' : State := { s with selector := s.selector - 1 }
    refine ⟨.dispatch (s.selector - 1), s', ?_, ?_⟩
    · simp [body, h, s', StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
        ExceptT.mk, Option.bind, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet]
    · exact ⟨hs, Nat.sub_lt (Nat.pos_of_ne_zero h) (by decide)⟩

example (n : Nat) : next (.foreign n) = none := rfl
example (n : Nat) : (fun e => (next e).isSome) (.done n) = false := rfl

end DispatchProof
