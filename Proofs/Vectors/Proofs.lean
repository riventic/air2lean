import Proofs.Vectors.Gen

/-!
# Proofs about `examples/vectors/vectors.zig`

`uDotWrap` (wrapping int dot product) gets a full scalar spec: it equals the explicit
4-term wrapping sum of pairwise wrapping products, lane 0 first (Zig's lane order). `fDot`
only gets a monadic-scaffolding reduction (`fDot_body`) — no claim that it equals a
particular scalar expression, since float addition is not associative and the reduce order
is exactly the thing that would make such a claim wrong. `maxLane` gets the property a
`@reduce(.Max)` bug would violate: the result dominates every lane, in particular the last
one (`scripts/mutate.sh`'s mutation (i) drops it). `satAdd` gets its per-lane spec. `reverse`
is a pure shuffle, exact by unfolding. `checkedAdd` has no proof here: characterizing its
`Vec.map2M` short-circuit on the first overflowing lane needs `Vector.mapM`'s internal
`go` recursion, out of scope for this milestone.

Local helper lemmas about `Zig.Vec` and `BitVec.sle` are named to move into
`ZigLean/Vec.lean` / a general `BitVec` lemmas file later (same convention as
`Proofs/Floats/Proofs.lean`).
-/

namespace Zig

/-- A 4-lane `Vec`'s lanes, written out explicitly (lane 0 first). The only fact this file
needs about `Vec`'s representation: everything else goes through `map2`/`reduce`. -/
theorem Vec.lanes_eq_four {α : Type} (v : Vec α 4) :
    v.lanes = #v[v.lanes[0], v.lanes[1], v.lanes[2], v.lanes[3]] := by
  ext i hi
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- `@reduce` on 4 lanes, in explicit left-to-right form (Zig's lane order: lane 0 first). -/
theorem Vec.reduce_four {α : Type} [Inhabited α] (f : α → α → α) (v : Vec α 4) :
    Vec.reduce f v = f (f (f v.lanes[0] v.lanes[1]) v.lanes[2]) v.lanes[3] := by
  unfold Vec.reduce
  rw [Vec.lanes_eq_four v]
  rfl

/-- `map2`'s lane `i` is `f` applied to both operands' lane `i` (`Vector.getElem_zipWith`,
through `map2`'s definition). -/
theorem Vec.map2_getElem {α β γ : Type} {n : Nat} (f : α → β → γ) (a : Vec α n) (b : Vec β n)
    (i : Nat) (hi : i < n) :
    (Vec.map2 f a b).lanes[i] = f a.lanes[i] b.lanes[i] := by
  unfold Vec.map2
  exact Vector.getElem_zipWith hi

/-- `BitVec.sle` is reflexive (via `sle_iff_toInt_le` and `Int.le_refl`). -/
theorem sle_refl {n : Nat} (a : BitVec n) : a.sle a = true := by
  simp [BitVec.sle_iff_toInt_le]

/-- `BitVec.sle` is transitive (via `sle_iff_toInt_le` and `Int.le_trans`). -/
theorem sle_trans {n : Nat} {a b c : BitVec n} (hab : a.sle b = true) (hbc : b.sle c = true) :
    a.sle c = true := by
  simp only [BitVec.sle_iff_toInt_le] at hab hbc ⊢
  omega

/-- `Zig.max true a b`'s definition, with the (statically known) signed branch already taken. -/
theorem max_true_eq {n : Nat} (a b : BitVec n) : Zig.max true a b = if a.sle b then b else a := rfl

/-- The signed max of `a` and `b` is signed-`≥` `a`. -/
theorem sle_max_left {n : Nat} (a b : BitVec n) : a.sle (Zig.max true a b) = true := by
  rw [max_true_eq]
  split
  · assumption
  · exact sle_refl a

/-- The signed max of `a` and `b` is signed-`≥` `b`. -/
theorem sle_max_right {n : Nat} (a b : BitVec n) : b.sle (Zig.max true a b) = true := by
  rw [max_true_eq]
  split
  · exact sle_refl b
  next h =>
    simp only [BitVec.sle_iff_toInt_le] at h ⊢
    omega

end Zig

open Vectors

/-- `uDotWrap`'s scalar spec: the wrapping dot product of two 4-lane `u32` vectors is the
explicit 4-term wrapping sum of pairwise wrapping products, lane 0 first. Both `mulWrap` and
`addWrap` are total (no overflow check), so this holds unconditionally. -/
theorem uDotWrap_spec (a b : Zig.Vec (BitVec 32) 4) :
    uDotWrap a b = pure (
      Zig.addWrap
        (Zig.addWrap
          (Zig.addWrap (Zig.mulWrap a.lanes[0] b.lanes[0]) (Zig.mulWrap a.lanes[1] b.lanes[1]))
          (Zig.mulWrap a.lanes[2] b.lanes[2]))
        (Zig.mulWrap a.lanes[3] b.lanes[3])) := by
  unfold uDotWrap
  simp only [zig_unfold]
  rw [Zig.Vec.reduce_four]
  rw [Zig.Vec.map2_getElem _ a b 0 (by decide),
      Zig.Vec.map2_getElem _ a b 1 (by decide),
      Zig.Vec.map2_getElem _ a b 2 (by decide),
      Zig.Vec.map2_getElem _ a b 3 (by decide)]

/-- `fDot`'s monadic scaffolding reduces to the plain `reduce`-of-`map2` expression it computes.
No claim beyond this: float addition is not associative, so which scalar expression `reduce`
produces depends on the fold order, and asserting one would be a claim about rounding, not
about the translation. -/
theorem fDot_body (a b : Zig.Vec Zig.F32 4) :
    fDot a b = pure (Zig.Vec.reduce Zig.Float.add (Zig.Vec.map2 Zig.Float.mul a b)) := by
  unfold fDot
  simp only [zig_unfold]

/-- `maxLane`'s monadic scaffolding reduces to the explicit 4-lane signed-max expression. -/
theorem maxLane_body (v : Zig.Vec (BitVec 32) 4) :
    maxLane v = pure
      (Zig.max true (Zig.max true (Zig.max true v.lanes[0] v.lanes[1]) v.lanes[2]) v.lanes[3]) := by
  unfold maxLane
  simp only [zig_unfold]
  rw [Zig.Vec.reduce_four]

/-- `maxLane`'s result signed-dominates every lane, in particular the last one. A `@reduce(.Max)`
mutation that drops the last lane (`scripts/mutate.sh`'s mutation (i)) breaks exactly this
property whenever lane 3 holds the true maximum. -/
theorem maxLane_ge (v : Zig.Vec (BitVec 32) 4) :
    ∃ r, maxLane v = pure r ∧ ∀ i, (hi : i < 4) → (v.lanes[i]'hi).sle r = true := by
  refine ⟨_, maxLane_body v, ?_⟩
  intro i hi
  match i, hi with
  | 0, _ =>
    exact Zig.sle_trans (Zig.sle_trans (Zig.sle_max_left _ _) (Zig.sle_max_left _ _))
      (Zig.sle_max_left _ _)
  | 1, _ =>
    exact Zig.sle_trans (Zig.sle_trans (Zig.sle_max_right _ _) (Zig.sle_max_left _ _))
      (Zig.sle_max_left _ _)
  | 2, _ =>
    exact Zig.sle_trans (Zig.sle_max_right _ _) (Zig.sle_max_left _ _)
  | 3, _ =>
    exact Zig.sle_max_right _ _

/-- `reverse` is the exact reverse shuffle: lane `i` of the result is lane `3 - i` of the
input. -/
theorem reverse_spec (v : Zig.Vec (BitVec 32) 4) :
    reverse v =
      pure (⟨#v[v.lanes[3]!, v.lanes[2]!, v.lanes[1]!, v.lanes[0]!]⟩ : Zig.Vec (BitVec 32) 4) := by
  unfold reverse
  simp only [zig_unfold]

/-- `satAdd`'s lane `i` is the scalar saturating add of both operands' lane `i` (as opposed to,
say, a wrapping or checked add). -/
theorem satAdd_lane (a b : Zig.Vec (BitVec 32) 4) (i : Nat) (hi : i < 4) :
    ∃ r, satAdd a b = pure r ∧ r.lanes[i] = Zig.addSat false a.lanes[i] b.lanes[i] := by
  unfold satAdd
  simp only [zig_unfold]
  exact ⟨_, rfl, Zig.Vec.map2_getElem _ a b i hi⟩
