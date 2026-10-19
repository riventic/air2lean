import ZigLean.Sep.Full.Auto

/-!
# `fsym_arith`: the arithmetic solver of `fsym` (`docs/proof-automation.md`)

Word arithmetic of generated code as natural numbers: alignment masks against symbolic powers of
two, overflow bits, shifts, no wrap-around where it cannot happen.
-/

namespace SepAuto.Arith

open Zig

/-- `std.mem.alignForward` on a 64-bit address (`(x + (a - 1)) & ~(a - 1)` with `a = 1 << k`):
a multiple of `2 ^ k`. -/
theorem alignForward_aligned (x : BitVec 64) (k : Nat) (hk : k < 64) (h : x.toNat + 2 ^ k < 2 ^ 64) :
    ((x + (Zig.shl (1 : BitVec 64) (BitVec.ofNat 6 k) - 1)) &&&
      ~~~(Zig.shl (1 : BitVec 64) (BitVec.ofNat 6 k) - 1)).toNat % 2 ^ k = 0 := by
  fsym_arith

/-- … and at most `2 ^ k - 1` above `x`. -/
theorem alignForward_bound (x : BitVec 64) (k : Nat) (hk : k < 64) (h : x.toNat + 2 ^ k < 2 ^ 64) :
    ((x + (Zig.shl (1 : BitVec 64) (BitVec.ofNat 6 k) - 1)) &&&
      ~~~(Zig.shl (1 : BitVec 64) (BitVec.ofNat 6 k) - 1)).toNat < x.toNat + 2 ^ k := by
  fsym_arith

/-- `std.math.isPowerOfTwo` of `1 << k`. -/
theorem isPowerOfTwo_shl (k : Nat) (hk : k < 64) :
    (Zig.shl (1 : BitVec 64) (BitVec.ofNat 6 k) &&& (Zig.shl (1 : BitVec 64) (BitVec.ofNat 6 k) - 1)) = 0 := by
  fsym_arith

/-- The overflow bit of `@addWithOverflow` is clear when the sum fits. -/
theorem add_no_overflow (a b : BitVec 64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (Zig.addWithOverflow false a b).snd = 0#1 ∧ (Zig.addWithOverflow false a b).fst.toNat = a.toNat + b.toNat := by
  constructor <;> fsym_arith

/-! ## Range conversions (the scenarios of the retired `zig_range`) -/

/-- A sum that fits does not wrap. -/
theorem add_fits (a b : BitVec 8) (h : a.toNat + b.toNat < 200) : (a + b).toNat = a.toNat + b.toNat := by
  fsym_arith

/-- A difference below the minuend does not wrap. -/
theorem sub_fits (a b : BitVec 32) (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  fsym_arith

/-- A natural number below the width, through `Int`. -/
theorem ofInt_natCast (k : Nat) (h : k < 256) : (BitVec.ofInt 8 (k : Int)).toNat = k := by
  fsym_arith

open Zig.Full Zig.Full.FAssn in
/-- A narrowing unsigned `@intCast` of a value that fits succeeds and keeps the value. -/
theorem intCast_fits (P : FAssn) (a : BitVec 64) (h : a.toNat < 256) :
    FTotalTriple P (StateT.lift (Zig.intCast false false 8 a) : MemM (BitVec 8))
      (fun r => ⟪r.toNat = a.toNat⟫ ⋆ P) := by
  fsym

/-! ## Normal forms (`ZigLean/Sep/Full/AutoArith.lean`): signed values, width changes, casts -/

/-- Widening keeps the value. -/
theorem setWidth_widen (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  fsym_arith

/-- `@truncate` of a value that fits keeps it; any `@truncate` is below its width. -/
theorem trunc_fits (a : BitVec 64) (h : a.toNat < 256) :
    (Zig.trunc 8 a).toNat = a.toNat ∧ (Zig.trunc 8 a).toNat < 256 := by
  constructor <;> fsym_arith

/-- A value below the sign bit reads the same signed and unsigned. -/
theorem toInt_nonneg (a : BitVec 16) (h : a.toNat < 100) : a.toInt = (a.toNat : Int) := by
  fsym_arith

/-- The range of a signed value, and the unsigned reading of `-1`. -/
theorem toInt_range (a : BitVec 16) : -2 ^ 15 ≤ a.toInt ∧ a.toInt < 2 ^ 15 := by
  constructor <;> fsym_arith

theorem toInt_neg_one (a : BitVec 8) (h : a.toInt = -1) : a.toNat = 255 := by
  fsym_arith

/-- Sign extension through `Int` keeps the signed value. -/
theorem ofInt_toInt (a : BitVec 8) : (BitVec.ofInt 64 a.toInt).toInt = a.toInt := by
  fsym_arith

/-- Signed comparisons of generated code, and `Zig.val`. -/
theorem lt_signed (a b : BitVec 16) (h : Zig.lt true a b = true) (hb : b.toInt ≤ 0) : a.toInt < 0 := by
  fsym_arith

theorem val_nonneg (a : BitVec 16) (h : 0 ≤ Zig.val true a) : Zig.val true a = Zig.val false a := by
  fsym_arith

/-- No signed overflow for small nonnegative operands. -/
theorem sadd_no_overflow (a b : BitVec 32) (h1 : 0 ≤ a.toInt) (h2 : a.toInt < 100) (h3 : 0 ≤ b.toInt)
    (h4 : b.toInt < 100) : a.saddOverflow b = false := by
  fsym_arith

open Zig.Full Zig.Full.FAssn in
/-- A narrowing signed `@intCast` of a value that fits keeps the signed value. -/
theorem intCast_signed_fits (P : FAssn) (a : BitVec 64) (h1 : -128 ≤ a.toInt) (h2 : a.toInt < 128) :
    FTotalTriple P (StateT.lift (Zig.intCast true true 8 a) : MemM (BitVec 8))
      (fun r => ⟪r.toInt = a.toInt⟫ ⋆ P) := by
  fsym

open Zig.Full Zig.Full.FAssn in
/-- After a narrowing unsigned `@intCast`, the result's value is the operand's (an equation in
the context, usable beyond `omega`). -/
theorem intCast_then_eq (P : FAssn) (a : BitVec 64) (h : a.toNat < 256) :
    FTotalTriple P (do let r ← (StateT.lift (Zig.intCast false false 8 a) : MemM (BitVec 8)); pure r.toNat)
      (fun v => ⟪v = a.toNat⟫ ⋆ P) := by
  fsym

open Zig.Full Zig.Full.FAssn in
/-- An unsigned value cast to a signed type that holds it. -/
theorem intCast_to_signed (P : FAssn) (a : BitVec 8) (h : a.toNat < 100) :
    FTotalTriple P (StateT.lift (Zig.intCast false true 8 a) : MemM (BitVec 8))
      (fun r => ⟪r.toInt = (a.toNat : Int)⟫ ⋆ P) := by
  fsym

open Zig.Full Zig.Full.FAssn in
/-- A nonnegative signed value cast to an unsigned type. -/
theorem intCast_to_unsigned (P : FAssn) (a : BitVec 32) (h1 : 0 ≤ a.toInt) :
    FTotalTriple P (StateT.lift (Zig.intCast true false 64 a) : MemM (BitVec 64))
      (fun r => ⟪(r.toNat : Int) = a.toInt⟫ ⋆ P) := by
  fsym

/-- A sum of at most `2 ^ 32` items of width 32 fits in 64 bits (a plain lemma). -/
theorem sum_fits (xs : List (BitVec 32)) (h : xs.length ≤ 2 ^ 32) : (xs.map BitVec.toNat).sum < 2 ^ 64 :=
  sum_toNat_lt (k := 32) xs h

set_option linter.unusedVariables false in
/-- Without a range premise the sum may wrap: nothing is proved. -/
example (a b : BitVec 8) : True := by
  fail_if_success
    have : (a + b).toNat = a.toNat + b.toNat := by fsym_arith
  trivial

open Zig.Full Zig.Full.FAssn in
set_option linter.unusedVariables false in
/-- Without a range premise a narrowing `@intCast` may panic: no step. -/
example (P : FAssn) (a : BitVec 64) : True := by
  fail_if_success
    have : FTotalTriple P (StateT.lift (Zig.intCast false false 8 a) : MemM (BitVec 8))
        (fun r => ⟪r.toNat = a.toNat⟫ ⋆ P) := by
      fsym
  trivial

set_option linter.unusedVariables false in
/-- Above the sign bit the signed reading differs: nothing is proved. -/
example (a : BitVec 16) : True := by
  fail_if_success
    have : a.toInt = (a.toNat : Int) := by fsym_arith
  trivial

set_option linter.unusedVariables false in
/-- `@truncate` may drop bits. -/
example (a : BitVec 64) : True := by
  fail_if_success
    have : (Zig.trunc 8 a).toNat = a.toNat := by fsym_arith
  trivial

set_option linter.unusedVariables false in
/-- Signed `+` of arbitrary operands may overflow. -/
example (a b : BitVec 32) : True := by
  fail_if_success
    have : a.saddOverflow b = false := by fsym_arith
  trivial

open Zig.Full Zig.Full.FAssn in
set_option linter.unusedVariables false in
/-- A negative value cast to an unsigned type panics: no step. -/
example (P : FAssn) (a : BitVec 32) (h : a.toInt < 0) : True := by
  fail_if_success
    have : FTotalTriple P (StateT.lift (Zig.intCast true false 64 a) : MemM (BitVec 64))
        (fun _ => P) := by
      fsym
  trivial

open Zig.Full Zig.Full.FAssn in
set_option linter.unusedVariables false in
/-- `128` does not fit in `i8`: no step. -/
example (P : FAssn) (a : BitVec 16) (h : a.toNat = 128) : True := by
  fail_if_success
    have : FTotalTriple P (StateT.lift (Zig.intCast false true 8 a) : MemM (BitVec 8))
        (fun _ => P) := by
      fsym
  trivial

/-! Implications (a loop invariant's `⟪s.it = none → x0 = none⟫`, ledger #arith-implications):
the premise is a fact for the conclusion; an implication among the facts gives its conclusion
once its premise normalizes to `True`; a fact that is the target closes it without `omega`. -/

/-- A premise that the facts refute. -/
theorem implies_refuted (p : Ptr) (x : Option Ptr) : some p = none → x = none := by
  fsym_arith

/-- An implication among the facts whose premise holds. -/
theorem implies_fact (y : BitVec 64) (h : (none : Option Ptr) = none → y.toNat = 3) :
    y.toNat < 4 := by
  fsym_arith

/-- … with a conclusion that is no arithmetic. -/
theorem implies_fact_target (x : Option Ptr) (h : (none : Option Ptr) = none → x = none) :
    x = none := by
  fsym_arith

open Zig.Full Zig.Full.FAssn in
/-- A postcondition fact that is an implication (a loop invariant's, at the next iteration). -/
theorem implies_post (P : FAssn) (p : Ptr) (x : Option Ptr) :
    FTotalTriple P (pure (some p) : MemM (Option Ptr)) (fun r => ⟪r = none → x = none⟫ ⋆ P) := by
  fsym

/-! ## A probe's budget (`withBudget`, ledger #probe-case-budget)

A probe searches the case facts within a budget of heartbeats of its own. These checks spend the
budget at once (`IO.addHeartbeats`); a misbehaving engine fails the elaboration. -/

section Budget
open Lean Meta Zig.Full.Auto

/-- **A budget hit outside `omega`** (the rewrite of a split term, `omegaFactsOn`): the probe
fails with `none`; the heartbeat exception does not escape to end the run. -/
def budget_outside_omega : MetaM Unit :=
  withLocalDeclD `a (mkConst ``Nat) fun a => withLocalDeclD `b (mkConst ``Nat) fun b => do
  let sub ← mkAppM ``HSub.hSub #[a, b]
  withLocalDeclD `h (← mkAppM ``LE.le #[sub, mkNatLit 10]) fun h => do
  let ty ← mkAppM ``LE.le #[sub, mkNatLit 11]
  let r ← withBudget 1 do
    IO.addHeartbeats 2000
    omegaFactsOn #[(h, ← inferType h)] ty
  if r.isSome then throwError "budget_outside_omega: a proof past the budget"

run_meta budget_outside_omega

/-- **No failure cached past the budget**: a case probe of a split term (`detProbe`) that fails
because its budget ran out is not recorded; the same probe outside the budget, in the same run,
is tried and succeeds. -/
def budget_no_failure_cache : MetaM Unit := do
  let id ← fsymRunCounter.modifyGet fun n => (n + 1, n + 1)
  fsymRuns.modify (·.insert id (← RunCaches.new))
  try
    withOptions (·.set `fsym.run id) <|
    withLocalDeclD `a (mkConst ``Nat) fun a => withLocalDeclD `b (mkConst ``Nat) fun b => do
    let prop ← mkAppM ``LE.le #[b, a]
    withLocalDeclD `h prop fun h => do
    let key := mkApp2 (mkConst `fsym.det) (← mkAppM ``HSub.hSub #[a, b]) prop
    let r ← withBudget 1 do
      IO.addHeartbeats 2000
      detProbe key #[h] (omegaRaw #[h] prop)
    if r.isSome then throwError "budget_no_failure_cache: a proof past the budget"
    if (← detProbe key #[h] (omegaRaw #[h] prop)).isNone then
      throwError "budget_no_failure_cache: the failure past the budget was cached"
  finally fsymRuns.modify (·.erase id)

run_meta budget_no_failure_cache

/-- **The context's limit binds a budget**: a budget above what remains of `maxHeartbeats` ends
at that limit, and its exception is rethrown (the limit ends the run), not a probe's `none`. -/
def budget_within_limit : MetaM Unit := do
  let r ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun c => { c with maxHeartbeats := 5000 }) <| withCurrHeartbeats do
      some <$> withBudget 10000 do
        IO.addHeartbeats 100000
        Core.checkSystem "budget_within_limit"
        return some ())
    fun ex => if ex.isMaxHeartbeat then pure none else throw ex
  if r.isSome then throwError "budget_within_limit: the budget raised the context's limit"

run_meta budget_within_limit

end Budget

end SepAuto.Arith
