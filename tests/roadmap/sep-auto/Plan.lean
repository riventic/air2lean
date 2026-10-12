import ZigLean.Sep.Full.AutoClaims

/-!
# Range laws of `fsym` (`@[fsym_plan]`, `docs/proof-automation.md` §Range laws)

The planner carves an atom of the postcondition out of a state atom that covers it and joins
adjacent state atoms first when none does, for every head with a range law (a declared table, not
code `fsym` evaluates): the library's claims (`bclaim_split`) and a user's own range assertion.
Rejected: a range the state does not cover, a claim of another tag, and a statement that is not a
range law (when the attribute is added).
-/

namespace SepAuto.Plan

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

set_option linter.unusedVariables false

/-- A claim with symbolic bounds is carved out of a covering claim; the rest is dropped. -/
theorem carve {b : BlockId} {lo a c hi : Nat} (h1 : lo ≤ a) (h2 : a ≤ c) (h3 : c ≤ hi) :
    EUpd (bclaim b lo hi) (bclaim b a c) := by
  fsym_entail

/-- Adjacent claims are joined, then carved. -/
theorem join {b : BlockId} {t : STag} :
    EUpd (bclaim b 8 16 t ⋆ bclaim b 0 8 t ⋆ bclaim b 16 32 t) (bclaim b 4 20 t ⋆ bclaim b 24 28 t) := by
  fsym_entail

/-- A user's range assertion: a law makes it planned like a claim. -/
def span (lo hi : Nat) : FAssn := bclaim 7 lo hi (some (3, 0))

theorem span_split {lo m hi : Nat} (h1 : lo ≤ m) (h2 : m ≤ hi) : (span lo m ⋆ span m hi) = span lo hi :=
  bclaim_split h1 h2

theorem span_drop {lo hi : Nat} {R : FAssn} : EUpd (span lo hi ⋆ R) R := claim_drop

attribute [fsym_plan] span_split
attribute [fsym_drop] span_drop

theorem user_head (P : FAssn) : EUpd (P ⋆ span 0 10 ⋆ span 10 20) (span 5 15 ⋆ P) := by
  fsym_entail

/-- Rejected: the state's claims do not cover the range. -/
example {b : BlockId} : True := by
  fail_if_success
    have : EUpd (bclaim b 0 8 ⋆ bclaim b 10 16) (bclaim b 4 12) := by fsym_entail
  trivial

/-- Rejected: a claim of another tag. -/
example {b : BlockId} : True := by
  fail_if_success
    have : EUpd (bclaim b 0 8 (some (1, 0))) (bclaim b 0 8 (some (2, 0))) := by fsym_entail
  trivial

theorem not_law {lo hi : Nat} : span lo hi = span lo hi := rfl

/-- error: @[fsym_plan] SepAuto.Plan.not_law: the left side is not a separating conjunction; expected a range law `X … lo m … ⋆ X … m hi … = X … lo hi …` -/
#guard_msgs in
attribute [fsym_plan] not_law

end SepAuto.Plan
