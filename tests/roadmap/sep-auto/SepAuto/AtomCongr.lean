import ZigLean.Sep.Full.AutoAll

/-!
# The congruence of the arithmetic's atoms (`docs/proof-automation.md`, ledger #arith-atom-congruence)

A loop whose cell adds a value of its counter (`acc.* += i`, `counted.tri`) has the invariant
`v + (tsum n g - tsum i g) = v₀ + (tsum n g - tsum i₀ g)` over the library sum `tsum`
(`ZigLean/Sep/Full/TSum.lean`). Its step leaves a fresh word `x` with `x.toNat = i.toNat + 1`:
`omega` reads `tsum x.toNat g` and `tsum i.toNat g` as unrelated atoms, and the solver relates them
(`atomCongr`: `tsum x.toNat g = tsum (i.toNat + 1) g`, in normal form `tsum i.toNat g + g i.toNat`).
The goals below are the side goals of `tri.loop5`'s step as `fsym` states them.
-/

namespace SepAuto.AtomCongr

open Zig Zig.Full

/-- The counter's step: the invariant at `x = i + 1` from the invariant at `i`, the cell's add
`x₂ = v + i` and the loop test `i < n`. -/
theorem counter_step (v x₂ x₅ w : BitVec 64) (i n i₀ x : BitVec 32)
    (hfit : w.toNat + (tsum n.toNat (fun u => u) - tsum i₀.toNat (fun u => u)) < 2 ^ 64)
    (hc : Zig.lt false i n = true)
    (hinv : v.toNat + (tsum n.toNat (fun u => u) - tsum i.toNat (fun u => u)) =
      w.toNat + (tsum n.toNat (fun u => u) - tsum i₀.toNat (fun u => u)))
    (h₅ : x₅.toNat = (BitVec.ofInt 64 (Zig.val false i)).toNat) (h₂ : x₂.toNat = v.toNat + x₅.toNat)
    (hx : x.toNat = i.toNat + (1#32).toNat) :
    x₂.toNat + (tsum n.toNat (fun u => u) - tsum x.toNat (fun u => u)) =
      w.toNat + (tsum n.toNat (fun u => u) - tsum i₀.toNat (fun u => u)) := by
  fsym_arith

/-- The cell's add does not overflow: the terms still to come include `i` (`tsum_sub_of_lt`, its
side condition the loop test, a fact after the invariant). -/
theorem add_fits (v x w : BitVec 64) (i n i₀ : BitVec 32)
    (hfit : w.toNat + (tsum n.toNat (fun u => u) - tsum i₀.toNat (fun u => u)) < 2 ^ 64)
    (hinv : v.toNat + (tsum n.toNat (fun u => u) - tsum i.toNat (fun u => u)) =
      w.toNat + (tsum n.toNat (fun u => u) - tsum i₀.toNat (fun u => u)))
    (hc : Zig.lt false i n = true) (hx : x.toNat = (BitVec.ofInt 64 (Zig.val false i)).toNat) :
    v.toNat + x.toNat < 2 ^ 64 := by
  fsym_arith

/-- The exit: no terms are left at `i = n` (`tsum_sub_of_le`). -/
theorem exit_sum (v w : BitVec 64) (i n i₀ : BitVec 32) (hle : i.toNat ≤ n.toNat)
    (hinv : v.toNat + (tsum n.toNat (fun u => u) - tsum i.toNat (fun u => u)) =
      w.toNat + (tsum n.toNat (fun u => u) - tsum i₀.toNat (fun u => u)))
    (hc : ¬Zig.lt false i n = true) :
    v.toNat = w.toNat + (tsum n.toNat (fun u => u) - tsum i₀.toNat (fun u => u)) := by
  fsym_arith

/-- Any summand, and any function of the arithmetic's atoms: congruence is not about `tsum`. -/
theorem any_summand (i x : BitVec 32) (hx : x.toNat = i.toNat + 1) :
    tsum x.toNat (fun u => 2 * u + 1) = tsum i.toNat (fun u => 2 * u + 1) + 2 * i.toNat + 1 := by
  fsym_arith

theorem any_function (f : Nat → Nat) (i x : BitVec 32) (hx : x.toNat = i.toNat + 1)
    (hf : f (i.toNat + 1) = 7) : f x.toNat = 7 := by
  fsym_arith

/-- A numeral bound is not unfolded (`tsumSucc` only rewrites a bound written `n + 1`). -/
theorem numeral_bound (g : Nat → Nat) (h : tsum 5000 g = 7) : tsum 5000 g + 1 = 8 := by
  fsym_arith

set_option linter.unusedVariables false in
/-- A step of two is not a step of one: nothing is proved. -/
example (i x : BitVec 32) (hx : x.toNat = i.toNat + 2) : True := by
  fail_if_success
    have : tsum x.toNat (fun u => u) = tsum i.toNat (fun u => u) + i.toNat := by fsym_arith
  trivial

set_option linter.unusedVariables false in
/-- A bound is no equation: no congruence. -/
example (i x : BitVec 32) (hx : x.toNat ≤ i.toNat + 1) : True := by
  fail_if_success
    have : tsum x.toNat (fun u => u) = tsum i.toNat (fun u => u) + i.toNat := by fsym_arith
  trivial

set_option linter.unusedVariables false in
/-- Without the loop test the terms still to come may be none: the add may overflow. -/
example (v x w : BitVec 64) (i n i₀ : BitVec 32)
    (hfit : w.toNat + (tsum n.toNat (fun u => u) - tsum i₀.toNat (fun u => u)) < 2 ^ 64)
    (hinv : v.toNat + (tsum n.toNat (fun u => u) - tsum i.toNat (fun u => u)) =
      w.toNat + (tsum n.toNat (fun u => u) - tsum i₀.toNat (fun u => u)))
    (hx : x.toNat = (BitVec.ofInt 64 (Zig.val false i)).toNat) : True := by
  fail_if_success
    have : v.toNat + x.toNat < 2 ^ 64 := by fsym_arith
  trivial

end SepAuto.AtomCongr
