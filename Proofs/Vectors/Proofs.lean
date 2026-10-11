import Proofs.Vectors.Gen
import ZigLean.Witness

/-!
# Proofs about `examples/vectors/vectors.zig`

`uDotWrap` (wrapping int dot product) gets a full scalar spec: it equals the explicit
4-term wrapping sum of pairwise wrapping products, lane 0 first (Zig's lane order). `fDot`
only gets a monadic-scaffolding reduction (`fDot_body`) — no claim that it equals a
particular scalar expression, since float addition is not associative and the reduce order
is exactly the thing that would make such a claim wrong. `maxLane` gets the property a
`@reduce(.Max)` bug would violate: the result dominates every lane, in particular the last
one (`scripts/mutate.sh`'s mutation (i) drops it). `satAdd` gets its per-lane spec. `reverse`
is a pure shuffle, exact by unfolding. `checkedAdd` is the lane-wise sum when
no lane overflows, else `.overflow` (`Vec.map2M_four`: `map2M` on 4 lanes, lane 0 first). The coverage functions: `interleave` (a
two-vector shuffle) is exact, `pick` (`@select`) and `splatAdd` get their per-lane spec,
`xorLanes` its 4-lane fold; the other reduce kinds and `twiceInMem` have only the diff test.
The other lane-wise ops (`vDiv` .. `vToFloat`, `sRem`/`sMod`): `vMinMax` equals the lane-wise
wrapping sum (`vMinMax_spec`); the others have only the diff test.

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

/-- `map2M` of a function that never throws is `map2` (`Emit.lean`'s lane-wise lift of an op
that does not throw, e.g. `@min`). -/
theorem Vec.map2M_pure {α β γ : Type} {n : Nat} (f : α → β → γ) (a : Vec α n) (b : Vec β n) :
    Vec.map2M (fun x y => pure (f x y)) a b = pure (Vec.map2 f a b) := by
  unfold Vec.map2M Vec.map2
  rw [Vector.mapM_pure (f := fun p : α × β => f p.1 p.2), Vector.map_zip_eq_zipWith]
  rfl

/-- Two `Result`s of vectors with the same arrays are equal (`Vector.toArray` is injective). -/
theorem Result.map_toArray_inj {γ : Type} {n : Nat} {x y : Result (Vector γ n)}
    (h : Vector.toArray <$> x = Vector.toArray <$> y) : x = y := by
  change Option (Except Error (Vector γ n)) at x y
  rcases x with _ | ⟨e | v⟩ <;> rcases y with _ | ⟨e' | v'⟩ <;>
    simp_all [Functor.map, ExceptT.map, ExceptT.mk] <;>
    first
    | rw [Vector.toArray_inj.mp (Except.ok.inj (Option.some.inj h))]
    | rw [Except.error.inj (Option.some.inj h)]
    | exact absurd (Option.some.inj h) (fun h => by cases h)

/-- `map2M` on 4 lanes, in explicit form: the lanes in order, lane 0 first, so the first lane
that throws gives the result. -/
theorem Vec.map2M_four {α β γ : Type} (f : α → β → Result γ) (a : Vec α 4) (b : Vec β 4) :
    Vec.map2M f a b = (do
      let r0 ← f a.lanes[0] b.lanes[0]
      let r1 ← f a.lanes[1] b.lanes[1]
      let r2 ← f a.lanes[2] b.lanes[2]
      let r3 ← f a.lanes[3] b.lanes[3]
      pure ⟨#v[r0, r1, r2, r3]⟩) := by
  have hm : (a.lanes.zip b.lanes).mapM (fun (x, y) => f x y) = (do
      let r0 ← f a.lanes[0] b.lanes[0]
      let r1 ← f a.lanes[1] b.lanes[1]
      let r2 ← f a.lanes[2] b.lanes[2]
      let r3 ← f a.lanes[3] b.lanes[3]
      pure #v[r0, r1, r2, r3]) := by
    apply Result.map_toArray_inj
    rw [Vector.toArray_mapM, Vec.lanes_eq_four a, Vec.lanes_eq_four b]
    simp [Array.mapM_eq_mapM_toList]
  unfold Vec.map2M
  rw [hm]
  simp only [bind_assoc, pure_bind]

/-- `@min(x, y) +% @max(x, y)` is `x +% y`: one of them is `x`, the other `y`. -/
theorem addWrap_min_max {n : Nat} (s : Bool) (x y : BitVec n) :
    Zig.addWrap (Zig.min s x y) (Zig.max s x y) = Zig.addWrap x y := by
  unfold Zig.addWrap Zig.min Zig.max
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split <;>
    first | rfl | exact BitVec.add_comm _ _

end Zig

namespace Vectors

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

/-! ### The coverage functions (`splatAdd` .. `twiceInMem`) -/

/-- `interleave` takes lanes `a[0], b[0], a[1], b[3]`: a mask entry `~i` selects lane `i` of
the second vector. -/
theorem interleave_spec (a b : Zig.Vec (BitVec 32) 4) :
    interleave a b =
      pure (⟨#v[a.lanes[0]!, b.lanes[0]!, a.lanes[1]!, b.lanes[3]!]⟩ : Zig.Vec (BitVec 32) 4) := by
  unfold interleave
  simp only [zig_unfold]

/-- `pick`'s lane `i` is `a`'s lane where the mask is true, else `b`'s. -/
theorem pick_lane (m : Zig.Vec Bool 4) (a b : Zig.Vec (BitVec 32) 4) (i : Nat) (hi : i < 4) :
    ∃ r, pick m a b = pure r ∧ r.lanes[i] = if m.lanes[i] then a.lanes[i] else b.lanes[i] := by
  unfold pick
  simp only [zig_unfold]
  exact ⟨_, rfl, by simp [Zig.Vec.select]⟩

/-- `splatAdd` adds the same scalar to every lane (wrapping). -/
theorem splatAdd_lane (v : Zig.Vec (BitVec 32) 4) (s : BitVec 32) (i : Nat) (hi : i < 4) :
    ∃ r, splatAdd v s = pure r ∧ r.lanes[i] = Zig.addWrap v.lanes[i] s := by
  unfold splatAdd
  simp only [zig_unfold]
  exact ⟨_, rfl, by rw [Zig.Vec.map2_getElem _ v _ i hi]; simp [Zig.Vec.splat]⟩

/-- `xorLanes` folds all 4 lanes with xor, the last lane too. -/
theorem xorLanes_spec (v : Zig.Vec (BitVec 32) 4) :
    xorLanes v = pure (v.lanes[0] ^^^ v.lanes[1] ^^^ v.lanes[2] ^^^ v.lanes[3]) := by
  unfold xorLanes
  simp only [zig_unfold]
  rw [Zig.Vec.reduce_four]

/-! ### The other lane-wise ops (`vDiv` .. `vToFloat`) -/

/-- `vMinMax` is the lane-wise wrapping sum: in each lane, `@min` and `@max` are the two
operands (the lift applies the scalar op to each lane). -/
theorem vMinMax_spec (a b : Zig.Vec (BitVec 32) 4) :
    vMinMax a b = pure (Zig.Vec.map2 Zig.addWrap a b) := by
  unfold vMinMax
  rw [Zig.Vec.map2M_pure (Zig.min true), Zig.Vec.map2M_pure (Zig.max true)]
  simp only [zig_unfold]
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  congr 2
  simp only [Zig.Vec.map2, Zig.Vec.mk.injEq]
  ext i hi
  simp only [Vector.getElem_zipWith, Zig.addWrap_min_max]

/-! ### `checkedAdd` -/

/-- `checkedAdd` with no lane that overflows is the lane-wise sum. -/
theorem checkedAdd_ok (a b : Zig.Vec (BitVec 32) 4)
    (h : ∀ i (hi : i < 4), (a.lanes[i]'hi).toNat + (b.lanes[i]'hi).toNat < 2 ^ 32) :
    checkedAdd a b = pure (Zig.Vec.map2 (· + ·) a b) := by
  unfold checkedAdd
  rw [Zig.Vec.map2M_four]
  simp only [Zig.add_unsigned, ge_iff_le, Nat.not_le.mpr (h 0 (by decide)),
    Nat.not_le.mpr (h 1 (by decide)), Nat.not_le.mpr (h 2 (by decide)),
    Nat.not_le.mpr (h 3 (by decide)), ite_false, pure_bind]
  rw [show Zig.Vec.map2 (· + ·) a b = ⟨#v[a.lanes[0] + b.lanes[0], a.lanes[1] + b.lanes[1],
      a.lanes[2] + b.lanes[2], a.lanes[3] + b.lanes[3]]⟩ by
    rw [← Zig.Vec.map2_getElem (· + ·) a b 0 (by decide),
      ← Zig.Vec.map2_getElem (· + ·) a b 1 (by decide),
      ← Zig.Vec.map2_getElem (· + ·) a b 2 (by decide),
      ← Zig.Vec.map2_getElem (· + ·) a b 3 (by decide), ← Zig.Vec.lanes_eq_four]]
  simp only [zig_unfold]

/-- `checkedAdd` with a lane that overflows throws `.overflow` (Zig's `+` on vectors is a
checked add in every lane). -/
theorem checkedAdd_overflow (a b : Zig.Vec (BitVec 32) 4)
    (h : ∃ i, ∃ hi : i < 4, 2 ^ 32 ≤ (a.lanes[i]'hi).toNat + (b.lanes[i]'hi).toNat) :
    checkedAdd a b = throw .overflow := by
  unfold checkedAdd
  rw [Zig.Vec.map2M_four]
  obtain ⟨i, hi, hov⟩ := h
  simp only [Zig.add_unsigned, ge_iff_le]
  match i, hi with
  | 0, _ => simp only [hov, ite_true]; rfl
  | 1, _ =>
    by_cases h0 : 2 ^ 32 ≤ a.lanes[0].toNat + b.lanes[0].toNat
    · simp only [h0, ite_true]; rfl
    · simp only [h0, hov, ite_true, ite_false, pure_bind]; rfl
  | 2, _ =>
    by_cases h0 : 2 ^ 32 ≤ a.lanes[0].toNat + b.lanes[0].toNat
    · simp only [h0, ite_true]; rfl
    by_cases h1 : 2 ^ 32 ≤ a.lanes[1].toNat + b.lanes[1].toNat
    · simp only [h0, h1, ite_true, ite_false, pure_bind]; rfl
    · simp only [h0, h1, hov, ite_true, ite_false, pure_bind]; rfl
  | 3, _ =>
    by_cases h0 : 2 ^ 32 ≤ a.lanes[0].toNat + b.lanes[0].toNat
    · simp only [h0, ite_true]; rfl
    by_cases h1 : 2 ^ 32 ≤ a.lanes[1].toNat + b.lanes[1].toNat
    · simp only [h0, h1, ite_true, ite_false, pure_bind]; rfl
    by_cases h2 : 2 ^ 32 ≤ a.lanes[2].toNat + b.lanes[2].toNat
    · simp only [h0, h1, h2, ite_true, ite_false, pure_bind]; rfl
    · simp only [h0, h1, h2, hov, ite_true, ite_false, pure_bind]; rfl

/-- Complete result classification for every pair of four-lane unsigned 32-bit vectors.
The finite lane witness makes the condition decidable without a classical oracle. -/
theorem checkedAdd_spec (a b : Zig.Vec (BitVec 32) 4) :
    checkedAdd a b =
      if ∃ i : Fin 4, 2 ^ 32 ≤ a.lanes[i.val].toNat + b.lanes[i.val].toNat then
        throw .overflow
      else pure (Zig.Vec.map2 (· + ·) a b) := by
  by_cases h : ∃ i : Fin 4, 2 ^ 32 ≤ a.lanes[i.val].toNat + b.lanes[i.val].toNat
  · rw [if_pos h]
    obtain ⟨i, hi⟩ := h
    exact checkedAdd_overflow a b ⟨i.val, i.isLt, hi⟩
  · rw [if_neg h]
    apply checkedAdd_ok
    intro i hi
    exact Nat.lt_of_not_ge (fun hov => h ⟨⟨i, hi⟩, hov⟩)

/-- Overflow is exactly the existence of an overflowing lane; it is not merely a
sufficient condition. Earlier lanes may also overflow. -/
theorem checkedAdd_overflow_iff (a b : Zig.Vec (BitVec 32) 4) :
    checkedAdd a b = throw .overflow ↔
      ∃ i : Fin 4, 2 ^ 32 ≤ a.lanes[i.val].toNat + b.lanes[i.val].toNat := by
  constructor
  · intro result
    by_cases h : ∃ i : Fin 4, 2 ^ 32 ≤ a.lanes[i.val].toNat + b.lanes[i.val].toNat
    · exact h
    · have ok := checkedAdd_ok a b (fun i hi =>
        Nat.lt_of_not_ge (fun hov => h ⟨⟨i, hi⟩, hov⟩))
      rw [ok] at result
      change (some (.ok (Zig.Vec.map2 (· + ·) a b)) :
        Option (Except Zig.Error (Zig.Vec (BitVec 32) 4))) = some (.error .overflow) at result
      cases result
  · rintro ⟨i, hi⟩
    exact checkedAdd_overflow a b ⟨i.val, i.isLt, hi⟩

/-- A successful sum is exactly the condition that every lane fits. This equation also
rules out other errors and nontermination when every lane fits. -/
theorem checkedAdd_ok_iff (a b : Zig.Vec (BitVec 32) 4) :
    checkedAdd a b = pure (Zig.Vec.map2 (· + ·) a b) ↔
      ∀ i (hi : i < 4), (a.lanes[i]'hi).toNat + (b.lanes[i]'hi).toNat < 2 ^ 32 := by
  constructor
  · intro result i hi
    apply Nat.lt_of_not_ge
    intro hov
    have overflow := checkedAdd_overflow a b ⟨i, hi, hov⟩
    rw [result] at overflow
    change (some (.ok (Zig.Vec.map2 (· + ·) a b)) :
      Option (Except Zig.Error (Zig.Vec (BitVec 32) 4))) = some (.error .overflow) at overflow
    cases overflow
  · exact checkedAdd_ok a b


/-! ## Non-vacuity witnesses -/

nonvacuity_witness checkedAdd_ok := ⟨Zig.Vec.splat 1, Zig.Vec.splat 2, by decide, trivial⟩
nonvacuity_witness Zig.Vec.map2M_pure :=
  ⟨Unit, Unit, Unit, 1, fun _ _ => (), Zig.Vec.splat (), Zig.Vec.splat (), trivial⟩

end Vectors
