/-!
Statement-binding fixtures for `scripts/project.py coverage` (I06). Every theorem's proof term
mentions `root`, so all of them depend on it directly in the declaration graph; only
`root_spec` states its conclusion about `root` and may bind as a `direct` goal.
-/

namespace StatementFixture

/-- Stands in for a generated root definition. -/
def root (x : Nat) : Nat := x + 1

def wrapper (x : Nat) : Nat := root x

/-- (a) The statement is about the wrapper; only the proof term mentions `root`. -/
theorem wrapper_spec (x : Nat) : wrapper x = x + 1 :=
  have h : root x = x + 1 := rfl
  h

/-- (b) A trivial statement whose proof term mentions `root`. -/
theorem trivial_spec : True :=
  have _h : root 0 = 1 := rfl
  trivial

/-- `root` occurs only in a hypothesis; the conclusion says nothing about it. -/
theorem premise_only (x : Nat) (_h : root x = 0) : True := trivial

/-- (c) A genuine theorem about `root`. -/
theorem root_spec (x : Nat) : root x = x + 1 := rfl

end StatementFixture
