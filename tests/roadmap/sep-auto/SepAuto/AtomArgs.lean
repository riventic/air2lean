import ZigLean.Sep.Full.AutoAll

/-!
# An existential's witnesses in a state atom's arguments (`docs/proof-automation.md`, ledger #atom-args-normal-form)

The stores of `counted.pairAt`'s body (`acc[0] += 1; acc[1] += 2`) leave the array's list as
`arr_store` states it, `([a, b].set 0 x).set (1#64).toNat y`, and its invariant owns
`∃ w₀ w₁, … ⋆ up (arr p [w₀, w₁])`. The planner matches the pattern's list constructors against
the value's head normal form (`matchArgs`), so `?w₀ := x` and `?w₁ := y`; the match itself is
proved (`proveEq`) and checked by the kernel.
-/

namespace SepAuto.AtomArgs

open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- Two stores into a two-item array, into an invariant's existential list. -/
theorem store_pair (p : Ptr) (a b x y : BitVec 64) :
    FTotalTriple (up (arr p [a, b]))
      (Zig.store (α := BitVec 64) 8 p x >>= fun _ => Zig.store (α := BitVec 64) 8 (p.elem 8 1) y)
      (fun _ => FAssn.ex fun w₀ : BitVec 64 => FAssn.ex fun w₁ : BitVec 64 =>
        ⟪w₀ = x ∧ w₁ = y⟫ ⋆ up (arr p [w₀, w₁])) := by
  fsym

/-- The witnesses by value: a cell's fact through the witness. -/
theorem store_pair_toNat (p : Ptr) (a b x y : BitVec 64) (hx : x.toNat = a.toNat + 1) :
    FTotalTriple (up (arr p [a, b]))
      (Zig.store (α := BitVec 64) 8 p x >>= fun _ => Zig.store (α := BitVec 64) 8 (p.elem 8 1) y)
      (fun _ => FAssn.ex fun w₀ : BitVec 64 => FAssn.ex fun w₁ : BitVec 64 =>
        ⟪w₀.toNat = a.toNat + 1⟫ ⋆ up (arr p [w₀, w₁])) := by
  fsym

set_option linter.unusedVariables false in
/-- The items swapped: the witnesses are the stored values, whose facts then fail. -/
example (p : Ptr) (a b x y : BitVec 64) (hxy : x ≠ y) : True := by
  fail_if_success
    have : FTotalTriple (up (arr p [a, b]))
        (Zig.store (α := BitVec 64) 8 p x >>= fun _ => Zig.store (α := BitVec 64) 8 (p.elem 8 1) y)
        (fun _ => FAssn.ex fun w₀ : BitVec 64 => FAssn.ex fun w₁ : BitVec 64 =>
          ⟪w₀ = y ∧ w₁ = x⟫ ⋆ up (arr p [w₀, w₁])) := by
      fsym
  trivial

set_option linter.unusedVariables false in
/-- A list of another length: no match. -/
example (p : Ptr) (a b x y : BitVec 64) : True := by
  fail_if_success
    have : FTotalTriple (up (arr p [a, b]))
        (Zig.store (α := BitVec 64) 8 p x >>= fun _ => Zig.store (α := BitVec 64) 8 (p.elem 8 1) y)
        (fun _ => FAssn.ex fun w₀ : BitVec 64 => FAssn.ex fun w₁ : BitVec 64 =>
          FAssn.ex fun w₂ : BitVec 64 => up (arr p [w₀, w₁, w₂])) := by
      fsym
  trivial

end SepAuto.AtomArgs
