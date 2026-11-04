import ZigLean.Sep.Full.Auto

/-!
# Projections of constructor applications reach the kernel one step at a time

`(a, r).2.f = s.f` holds by unfolding, but the kernel compares the two projections' arguments
first: `(a, r).2 =?= s`, by structure eta down to `r`'s fields against `s`'s. A literal field
(`Pk.ofBits 65537#32 =?= s.prev`) then unfolds until the recursion limit: an error, not a failed
comparison, so the kernel never reaches the reduction that would succeed. Plain
`simp only [eq_self]` on this goal elaborates and is rejected by the kernel ("deep recursion
detected"). fsym's simp runs (`fsimp`, `withProjCtor`) rewrite such a projection with an explicit
proof first (`projCtorStep?`): the value against its constructor application, then the
projection of the constructor application, each of which the kernel reduces at once.

The shapes are those of `Proofs.Sync.Cond`'s inner wait loop: a loop's exit paired with its
locals, whose packed state is a literal after a compare-and-swap.
-/

namespace SepAuto.ProjCtorKernel

open Lean Meta Elab Tactic Zig.Full.Auto

class Pk (α : Type) (n : outParam Nat) where
  ofBits : BitVec n → α

instance {n : Nat} : Pk (BitVec n) n where
  ofBits v := v

def Pk.get {α : Type} {n w : Nat} [Pk α n] (host : BitVec w) (o : Nat) : α :=
  Pk.ofBits (host.extractLsb' o n)

/-- A packed state of two counters (`Io.Condition.State`). -/
structure St where
  waiters : BitVec 16
  signals : BitVec 16

instance : Pk St 32 where
  ofBits b := { waiters := Pk.get b 0, signals := Pk.get b 16 }

/-- A loop's locals. -/
structure Loc where
  epoch : BitVec 32
  prev : St

/-- A loop's exit. -/
inductive Ex where
  | again | done

/-- `fsimp` with `eq_self` closes the goal, and the kernel accepts the proof. -/
theorem fsimp_epoch (s : Loc) :
    (Ex.again, ({ epoch := s.epoch, prev := Pk.ofBits (65537 : BitVec 32) } : Loc)).2.epoch
      = s.epoch := by
  run_tac do
    let g ← getMainGoal
    let ctx ← Simp.mkContext (simpTheorems := #[← ({} : SimpTheorems).addConst ``eq_self])
    let (r, _) ← fsimp (← g.getType) ctx
    unless r.expr.isTrue do throwError "fsimp did not close {r.expr}"
    g.assign (← mkOfEqTrue (← r.getProof))

set_option linter.unusedVariables false in
/-- A class projection stays folded: `a + b` is not unfolded to its instance's field. -/
example (a b : BitVec 32) : True := by
  run_tac do
    let a := (← getLocalDeclFromUserName `a).toExpr
    let b := (← getLocalDeclFromUserName `b).toExpr
    if (← projCtorStep? (← mkAppM ``HAdd.hAdd #[a, b])).isSome then
      throwError "a class projection was unfolded"
  trivial

end SepAuto.ProjCtorKernel
