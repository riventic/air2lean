import ZigLean.VC.Result

open Zig VC

-- A generated arithmetic obligation retains the exact overflow bound and desired value.
example (a b : BitVec 8) (Q : BitVec 8 → Prop) :
    ResultProgram.vc (.add a b) Q ↔ a.toNat + b.toNat < 256 ∧ Q (a + b) := Iff.rfl

example : ResultProgram.vc (.add (254#8) (1#8)) (fun value => value = 255#8) := by
  simp only [ResultProgram.vc] <;> decide
example : ¬ ResultProgram.vc (.add (255#8) (1#8)) (fun _ => True) := by
  simp only [ResultProgram.vc] <;> decide

-- This is an executable-model counterexample, distinct from an unsolved VC.
example : ResultProgram.eval (.add (255#8) (1#8)) = (throw Error.overflow) := by
  have overflow : (255#8).toNat + (1#8).toNat ≥ 2 ^ 8 := by decide
  simp only [ResultProgram.eval, Zig.add_unsigned, ite_eq_left overflow]

-- Bind generates the continuation's obligation; a wrong return is rejected.
example : ¬ ResultProgram.vc
    (.bind (.ret (2 : Nat)) (fun n => .ret (n + 1))) (fun n => n = 4) := by
  simp only [ResultProgram.vc] <;> decide
example : ResultProgram.vc
    (.bind (.ret (2 : Nat)) (fun n => .ret (n + 1))) (fun n => n = 3) := by
  simp only [ResultProgram.vc] <;> decide

-- Safety remains necessary even if the requested functional postcondition is True.
example (b : Bool) : ResultProgram.vc (.guard b) (fun _ => True) ↔ b = true := by
  simp [ResultProgram.vc]
example : ¬ ResultProgram.obligation True (.guard false) (fun _ => True) := by
  simp [ResultProgram.obligation, ResultProgram.vc]

-- Both conditional paths are handled according to the actual input condition.
example (b : Bool) : ResultProgram.vc
    (.branch b (.ret (0 : Nat)) (.panic Error.illegal)) (fun _ => True) ↔ b = true := by
  cases b <;> simp [ResultProgram.vc]

-- Zig errors returned through an error union are checked values, not safety panics.
example : ResultProgram.vc
    (.ret (Except.error "Empty" : Except ErrName Nat))
    (fun value => value = Except.error "Empty") := rfl
example : ¬ ResultProgram.vc
    (.ret (Except.error "Empty" : Except ErrName Nat))
    (fun value => value = Except.ok 0) := by
  intro h
  change (Except.error "Empty" : Except ErrName Nat) = Except.ok 0 at h
  cases h

-- A claimed modular call summary needs an actual kernel-checked callee contract.
example : ¬ (True → ∃ value : Nat, (throw Error.panic : Result Nat) = pure value ∧ True) := by
  intro h
  obtain ⟨value, hr, _⟩ := h trivial
  change some (Except.error Error.panic) = some (Except.ok value) at hr
  cases hr

example (a : Nat) : ResultProgram.vc
    (.call "identity" (pure a) True (fun value => value = a)
      (fun _ => ⟨a, rfl, rfl⟩)) (fun value => value = a) := by
  exact ⟨trivial, fun _ h => h⟩

-- No rule can discharge the False obligation of a raw safety panic.
example : ¬ ResultProgram.vc (.panic (α := Nat) Error.panic) (fun _ => True) := by
  exact id
