import Lean

namespace AssuranceFixture
open Lean Meta

/-- Tactic-engine code: a `partial def` over `MetaM` and an `initialize`d cache, reached by no theorem. -/
partial def metaWalk (e : Expr) : MetaM Expr := do
  match e with
  | .app f _ => metaWalk f
  | _ => return e

initialize metaCache : IO.Ref (Array Nat) ← IO.mkRef #[]

theorem unrelated : (1 : Nat) + 1 = 2 := rfl

end AssuranceFixture
