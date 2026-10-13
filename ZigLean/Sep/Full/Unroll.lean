import ZigLean.Conc.Unroll
import ZigLean.Sep.Full.Conc

/-!
# Runs in the caller's thread of programs with loops, by the kernel

`unroll_solo k` is `unroll_sched k` (`ZigLean/Conc/Unroll.lean`) for the in-thread reading of a
concurrent function (`Sched.soloRun`, the run that `CTriple` speaks about): it closes a goal
`g ((Sched.soloRun fuel x).run m) = v` (an observation `g` of the run, e.g. `Witness.errOf`) where
`g` of a run without a result is not `v`. It cuts every loop and `partial_fixpoint` group of `x`
after `k` iterations (`Unroll.expand`), proves the cut program below `x`, and lets the kernel
compute the cut run: a reading with a result of a program below `x` is `x`'s reading
(`Sched.soloTree_le`, `Sched.soloRun_apply_le`). Not imported by `ZigLean.lean`; see
docs/proof-tools.md.
-/

namespace Zig.Sched

open Lean.Order

/-- **A reading with a result is the reading of every tree above.** -/
theorem soloTree_le {Tgt α : Type} : ∀ {n : Nat} {x y : CoN Tgt (α × Mem) n}, CoN.le x y →
    ∀ {r : Except Error (α × Mem)}, soloTree x = some r → soloTree y = some r := by
  intro n x y h
  induction h with
  | bot => intro r hr; cases hr
  | leaf => intro r hr; exact hr
  | sync op m₀ k₁ k₂ _ ih => intro r hr; exact ih _ _ hr

/-- **Any observation of an in-thread reading with a result is the program's** (`apply_le` for
`soloRun`). -/
theorem soloRun_apply_le {Tgt α β : Type} {x₁ x₂ : ConcM Tgt α} (hx : x₁ ⊑ x₂) {fuel : Nat}
    {m : Mem} (g : Result (α × Mem) → β) {v : β} (hg : g noResult ≠ v)
    (h : g ((soloRun fuel x₁).run m) = v) : g ((soloRun fuel x₂).run m) = v := by
  cases hr : soloTree (Tgt := Tgt) (α := α) (x₁ fuel m) with
  | none =>
    have e : (soloRun fuel x₁).run m = noResult := by
      show (ExceptT.mk (soloTree (Tgt := Tgt) (α := α) (x₁ fuel m)) : Result (α × Mem)) = ExceptT.mk none
      rw [hr]
    exact absurd (e ▸ h) hg
  | some r =>
    have e : (soloRun fuel x₂).run m = (soloRun fuel x₁).run m := by
      show (ExceptT.mk (soloTree (Tgt := Tgt) (α := α) (x₂ fuel m)) : Result (α × Mem)) =
        ExceptT.mk (soloTree (Tgt := Tgt) (α := α) (x₁ fuel m))
      rw [soloTree_le (hx fuel m) hr, hr]
    rw [e]; exact h

end Zig.Sched

namespace Zig.Unroll

open Lean Meta Elab Tactic

/-- `unroll_solo k` proves a goal `g ((Sched.soloRun fuel x).run m) = v` where `g` of a run without a
result is not `v` (module doc; `unrollAt`, `Sched.soloRun_apply_le`). -/
elab "unroll_solo " k:num : tactic => withMainContext do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let some run := ty.find? fun e =>
      e.isAppOfArity ``StateT.run 5 && (e.getArg! 3).isAppOfArity ``Sched.soloRun 4
    | throwError "unroll_solo: the goal has no `(Sched.soloRun fuel x).run m`"
  let args := run.getAppArgs
  let solo := args[3]!
  unrollAt "unroll_solo" k.getNat run #[solo.appArg!]
    (fun cs => mkAppN run.getAppFn (args.set! 3 (mkApp solo.appFn! cs[0]!))) fun les g v bot sub =>
      mkAppOptM ``Sched.soloRun_apply_le #[none, none, none, none, none, les[0]!, none, none, g, v, bot, sub]

end Zig.Unroll
