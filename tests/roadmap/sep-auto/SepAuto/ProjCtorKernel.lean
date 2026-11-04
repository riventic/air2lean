import ZigLean.Sep.Full.Auto

/-!
# Projections of constructor applications reach the kernel one step at a time

`(a, r).2.f = s.f` holds by unfolding, but the kernel compares the two projections' arguments
first: `(a, r).2 =?= s`, by structure eta down to `r`'s fields against `s`'s. A literal field
(`Packed.ofBits 65537#32 =?= s.prev`) then unfolds until the recursion limit: an error, not a failed
comparison, so the kernel never reaches the reduction that would succeed. Plain
`simp only [eq_self]` on this goal elaborates and is rejected by the kernel ("deep recursion
detected"). fsym's simp runs (`fsimp`, `withProjCtor`) rewrite such a projection with an explicit
proof first (`projCtorStep?`): the value against its constructor application, then the
projection of the constructor application, each of which the kernel reduces at once. The
engine's own reductions of projections (`reduceProjsEq`: the entailment planner's postcondition,
the hypotheses, the goals of its walks) take the same steps, each a proof of its own.

The shapes are those of `Proofs.Sync.Cond`'s inner wait loop: a loop's exit paired with its
locals, whose packed state is a literal after a compare-and-swap.
-/

namespace SepAuto.ProjCtorKernel

open Lean Meta Elab Tactic Zig.Full.Auto

/-- A packed state of two counters (`Io.Condition.State`, as the translator emits it). -/
structure St where
  waiters : BitVec 16
  signals : BitVec 16

instance : Zig.Packed St 32 where
  toBits v := (v.waiters.setWidth 32 <<< 0) ||| (v.signals.setWidth 32 <<< 16)
  ofBits b := { waiters := Zig.Packed.get b 0, signals := Zig.Packed.get b 16 }

/-- A loop's locals. -/
structure Loc where
  epoch : BitVec 32
  prev : St

/-- A loop's exit. -/
inductive Ex where
  | again | done

set_option quotPrecheck false in
/-- The loop's exit paired with its locals after the compare-and-swap: `s`'s epoch, a packed
literal. A notation, not a definition: each use elaborates to the term written out (no
precheck: the structure instance is elaborated at each use). -/
local notation "again% " s:max =>
  (Ex.again, ({ epoch := Loc.epoch s, prev := Zig.Packed.ofBits (65537 : BitVec 32) } : Loc))

/-- `fsimp` with `eq_self` closes the goal, and the kernel accepts the proof. -/
theorem fsimp_epoch (s : Loc) : (again% s).2.epoch = s.epoch := by
  run_tac do
    let g ← getMainGoal
    let ctx ← Simp.mkContext (simpTheorems := #[← ({} : SimpTheorems).addConst ``eq_self])
    let (r, _) ← fsimp (← g.getType) ctx
    unless r.expr.isTrue do throwError "fsimp did not close {r.expr}"
    g.assign (← mkOfEqTrue (← r.getProof))

open Zig.Full Zig.Full.FAssn

/-- The same projection in a postcondition, by `fsym`: the entailment planner reduces the
postcondition's projections (`reduceProjsEq`) with a proof, so the kernel accepts the
entailment. As a definitional step (`reduceProjs` with the reduced form installed by its type)
the kernel rejected it (deep recursion, ledger `kernel-proj-ctor`). -/
theorem fsym_post_epoch (s : Loc) :
    FTotalTriple emp (pure (again% s) : Zig.MemM (Ex × Loc)) (fun r => ⟪r.2.epoch = s.epoch⟫) := by
  fsym

-- The definitional step the engine no longer takes, on a goal: its reduced form installed by
-- its type (`replaceTargetDefEq`, `show`) is rejected by the kernel.
/-- error: (kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit -/
#guard_msgs in
example (s : Loc) : (again% s).2.epoch = s.epoch :=
  show s.epoch = s.epoch from rfl

-- The same on a hypothesis: used at its reduced type (`replaceLocalDeclDefEq`), it is rejected
-- by the kernel.
/-- error: (kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit -/
#guard_msgs in
example (s : Loc) (P : BitVec 32 → Prop) (h : P (again% s).2.epoch) : P s.epoch := h

/-- The same projection in a hypothesis, by `fsym`: its projections are reduced with a proof
(`reduceProjsHyps`: a new local by `Eq.mp`), not definitionally (rejected above). -/
theorem fsym_hyp_epoch (s : Loc) (P : BitVec 32 → Prop) (h : P (again% s).2.epoch) :
    FTotalTriple emp (pure () : Zig.MemM Unit) (fun _ => ⟪P s.epoch⟫) := by
  fsym

/-- The same with the hypothesis a binder after the colon: `fsym` introduces it, and replaces it
in the goal's context. -/
theorem fsym_hyp_binder : ∀ (s : Loc) (P : BitVec 32 → Prop),
    P (again% s).2.epoch → FTotalTriple emp (pure () : Zig.MemM Unit) (fun _ => ⟪P s.epoch⟫) := by
  fsym

/-- A command that a caller's rule covers. -/
@[irreducible] def tick : Zig.MemM Unit := pure ()

theorem tick_spec (R : Prop) (hR : R) : FTotalTriple emp tick (fun _ => ⟪R⟫) := by
  unfold tick; fsym

/-- A caller's term that names the replaced hypothesis: it takes the new local cast back to the
hypothesis's type (`Eq.mpr`, the run's substitution), not the new local itself, which would meet
the term at the reduced type (the definitional step rejected above). -/
theorem fsym_caller_term (s : Loc) (P : BitVec 32 → Prop) (h : P (again% s).2.epoch) :
    FTotalTriple emp tick (fun _ => ⟪P s.epoch⟫) := by
  fsym [tick_spec _ h]

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
