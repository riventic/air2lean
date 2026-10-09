import Proofs.Variants.Gen
import ZigLean.Witness

/-!
# Proofs about `examples/variants/variants.zig`

`next` steps a traffic light, `advance` steps it `n` times. `lightOf`/`codeOf` convert a byte to
an enum: an unnamed value panics for the exhaustive `Light`, and is kept for the non-exhaustive
`Code`. `area`/`scale`/`radius` work on the tagged union `Shape`.
-/

namespace Variants

/-- The traffic-light cycle as a plain function. -/
def nextSpec : Light → Light
  | .red => .green
  | .green => .yellow
  | .yellow => .red

theorem next_spec (l : Light) : next l = pure (nextSpec l) := by
  cases l <;> rfl

/-- Three steps are the identity. -/
theorem nextSpec_three (l : Light) : nextSpec (nextSpec (nextSpec l)) = l := by
  cases l <;> rfl

/-- A named value converts back to its light. -/
theorem lightOf_toBits (l : Light) : lightOf l.toBits = pure l := by
  cases l <;> rfl

theorem Light.ofInt?_ge (v : Int) (h : 3 ≤ v) : Light.ofInt? v = none := by
  simp only [Light.ofInt?]
  split <;> (try split) <;> (try split) <;> first | rfl | omega

/-- Any other byte is the safety panic `invalidEnumValue`. -/
theorem lightOf_invalid (x : BitVec 8) (h : 3 ≤ x.toNat) : lightOf x = throw .panic := by
  unfold lightOf
  simp [zig_unfold, Zig.enumOf, Zig.val, Light.ofInt?_ge _ (by omega : (3 : Int) ≤ x.toNat)]

/-- A non-exhaustive enum keeps every value: `codeOf` never panics. -/
theorem codeOf_spec (x : BitVec 8) : codeOf x = pure ⟨x⟩ := by
  unfold codeOf
  have hx := x.isLt
  have hle : (x.toNat : Int) ≤ 255 := by omega
  simp [zig_unfold, Zig.enumOf, Code.ofInt?, Zig.val, hle]

/-- `severity` of the named codes is their value; of every other code, `2`. -/
theorem severity_spec (x : BitVec 8) :
    severity ⟨x⟩ = pure (if x = 0 then 0 else if x = 1 then 1 else 2) := by
  unfold severity
  have hbeq (a b : BitVec 8) : ((⟨a⟩ : Code) == ⟨b⟩) = decide (a = b) := by
    simp only [BEq.beq, Code.mk.injEq]
  by_cases h0 : x = 0
  · subst h0; rfl
  · by_cases h1 : x = 1
    · subst h1; rfl
    · simp only [BitVec.ofNat_eq_ofNat] at h0 h1
      simp [zig_unfold, Code.ok, Code.warn, hbeq, h0, h1]

theorem prioValue_spec (p : Prio) : prioValue p = pure p.toBits := by
  cases p <;> rfl

theorem isUrgent_spec (p : Prio) : isUrgent p = pure (p == .high) := by
  cases p <;> rfl

/-- A shape whose payload is defined: not one that a retag left undefined (`undef_*`, MM-13). -/
def Shape.Defined : Shape → Prop
  | .undef_circle .. | .undef_rect .. | .undef_square .. => False
  | _ => True

/-- The area of a shape as a natural number (`circle`: `3 * r * r`). -/
def areaNat : Shape → Nat
  | .circle r => 3 * r.toNat * r.toNat
  | .rect r => r.w.toNat * r.h.toNat
  | .square a => a.toNat * a.toNat
  | .empty | .undef_circle .. | .undef_rect .. | .undef_square .. => 0

/-- `area` is `areaNat` when it fits in `u64`. -/
theorem area_spec (s : Shape) (hs : s.Defined) (h : areaNat s < 2 ^ 64) :
    area s = pure (BitVec.ofNat 64 (areaNat s)) := by
  unfold area
  cases s with
  | circle r =>
    have hr := r.isLt
    simp only [areaNat] at h
    have h3 : 3 * r.toNat < 2 ^ 64 := by omega
    simp [zig_unfold, Shape.tag, Shape.get_circle, areaNat, Nat.mod_eq_of_lt h3,
      Nat.mod_eq_of_lt (show r.toNat < 2 ^ 64 by omega), Nat.not_le.mpr h3, Nat.not_le.mpr h]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt h3,
      Nat.mod_eq_of_lt (show r.toNat < 2 ^ 64 by omega)]
  | rect rc =>
    have hw := rc.w.isLt
    have hh := rc.h.isLt
    simp only [areaNat] at h
    simp [zig_unfold, Shape.tag, Shape.get_rect, areaNat,
      Nat.mod_eq_of_lt (show rc.w.toNat < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show rc.h.toNat < 2 ^ 64 by omega), Nat.not_le.mpr h]
    congr 2
  | square a =>
    have ha := a.isLt
    simp only [areaNat] at h
    simp [zig_unfold, Shape.tag, Shape.get_square, areaNat,
      Nat.mod_eq_of_lt (show a.toNat < 2 ^ 64 by omega), Nat.not_le.mpr h]
    congr 2
  | empty => rfl
  | undef_circle => cases hs
  | undef_rect => cases hs
  | undef_square => cases hs

/-- A shape whose payload a retag left undefined has no area: its read is `.unspecified`. -/
theorem area_undef (r : BitVec 32) (w : List String) :
    area (.undef_circle r w) = throw .unspecified := rfl

/-- `radius` is the payload of a circle, and panics (`inactiveUnionField`) otherwise; an
undefined circle payload is `.unspecified` (MM-13). -/
theorem radius_spec (s : Shape) :
    radius s = match s with
      | .circle r => pure r
      | .undef_circle _ _ => throw .unspecified
      | _ => throw .panic := by
  cases s <;> rfl

theorem isRound_spec (s : Shape) : isRound s = pure (s.tag == .circle) := by
  cases s <;> rfl

/-- `scale` multiplies every size by `k`, keeps the tag, and does not overflow when every
scaled size fits in `u32`. -/
def scaleSpec (s : Shape) (k : BitVec 32) : Shape :=
  match s with
  | .circle r => .circle (r * k)
  | .rect rc => .rect { w := rc.w * k, h := rc.h * k }
  | .square a => .square (a * k)
  | .empty => .empty
  | .undef_circle r w => .undef_circle r w
  | .undef_rect r w => .undef_rect r w
  | .undef_square r w => .undef_square r w

/-- Every size of `s`, times `k`, fits in `u32`. -/
def scaleFits (s : Shape) (k : BitVec 32) : Prop :=
  match s with
  | .circle r | .square r => r.toNat * k.toNat < 2 ^ 32
  | .rect rc => rc.w.toNat * k.toNat < 2 ^ 32 ∧ rc.h.toNat * k.toNat < 2 ^ 32
  | .empty => True
  | .undef_circle .. | .undef_rect .. | .undef_square .. => False

theorem scale_spec (s : Shape) (k : BitVec 32) (h : scaleFits s k) :
    scale s k = pure (scaleSpec s k) := by
  unfold scale
  -- The result local starts as `default`, the first field (`circle`) with payload 0.
  have hd : (default : scaleLocals).local2 = .circle 0 := rfl
  cases s with
  | circle r =>
    simp only [scaleFits] at h
    simp [zig_unfold, Shape.tag, Shape.get_circle, Shape.setTag_circle, Shape.set_circle, hd,
      scaleSpec, Nat.not_le.mpr h]
  | rect rc =>
    simp only [scaleFits] at h
    -- The retagged payload is undefined until both fields are written (MM-13).
    have hw : Shape.setField_rect "h" (fun x => { w := x.w, h := rc.h * k })
        (Shape.setField_rect "w" (fun x => { w := rc.w * k, h := x.h }) (Shape.undef_rect default []))
        = .rect { w := rc.w * k, h := rc.h * k } := by
      simp [Shape.setField_rect]
    simp [zig_unfold, Shape.tag, Shape.get_rect, Shape.setTag_rect, hd, hw, scaleSpec,
      Nat.not_le.mpr h.1, Nat.not_le.mpr h.2]
  | square a =>
    simp only [scaleFits] at h
    simp [zig_unfold, Shape.tag, Shape.get_square, Shape.setTag_square, Shape.set_square, hd,
      scaleSpec, Nat.not_le.mpr h]
  | empty => rfl
  | undef_circle => simp [scaleFits] at h
  | undef_rect => simp [scaleFits] at h
  | undef_square => simp [scaleFits] at h

/-- Scaling keeps the shape's tag. -/
theorem scaleSpec_tag (s : Shape) (k : BitVec 32) : (scaleSpec s k).tag = s.tag := by
  cases s <;> rfl

/-! ## `advance`: a loop over the enum -/

/-- `k` steps of the cycle. -/
def steps : Nat → Light → Light
  | 0, l => l
  | k + 1, l => nextSpec (steps k l)

theorem advance_loop_step (l : Light) (n : BitVec 32) (s : advanceLocals)
    (hle : s.i.toNat ≤ n.toNat) (hc : s.cur = steps s.i.toNat l) :
    ∃ e s', (advance.loop7 n).run s = pure (e, s') ∧
      (if advance.again7 e then
          (s'.i.toNat ≤ n.toNat ∧ s'.cur = steps s'.i.toNat l) ∧
            n.toNat - s'.i.toNat < n.toNat - s.i.toNat
        else e = .br6 ∧ s'.cur = steps n.toNat l) := by
  unfold advance.loop7
  by_cases hlt : s.i.toNat < n.toNat
  · have hn := n.isLt
    have hinc : ¬ 4294967295 ≤ s.i.toNat := by omega
    refine ⟨.rep7, { cur := nextSpec s.cur, i := s.i + 1 }, ?_, ?_⟩
    · simp [zig_unfold, next_spec, hlt, hinc]
    · have h1 : (s.i + 1).toNat = s.i.toNat + 1 := Zig.toNat_add_one _ (by omega)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [h1]; omega
      · rw [h1, steps, hc]
      · rw [h1]; omega
  · have heq : s.i.toNat = n.toNat := by omega
    refine ⟨.br6, s, ?_, ?_⟩
    · simp [zig_unfold, hlt]
    · simp only [advance.again7, Bool.false_eq_true, ↓reduceIte]
      exact ⟨trivial, heq ▸ hc⟩

/-- `advance l n` steps `l` exactly `n` times, and never panics. -/
theorem advance_spec (l : Light) (n : BitVec 32) : advance l n = pure (steps n.toNat l) := by
  obtain ⟨⟨e, s'⟩, hrun, he, hpost⟩ := Zig.loop_spec (advance.loop7 n) advance.again7
    (fun s => s.i.toNat ≤ n.toNat ∧ s.cur = steps s.i.toNat l)
    (fun s => n.toNat - s.i.toNat)
    (fun r => r.1 = .br6 ∧ r.2.cur = steps n.toNat l)
    (fun s hs => advance_loop_step l n s hs.1 hs.2)
    { cur := l, i := 0 } (by simp [steps])
  subst he
  unfold advance
  change Zig.loop (advance.loop7 n) advance.again7 { cur := l, i := 0 }
    = some (Except.ok (advanceExit.br6, s')) at hrun
  simp only [zig_unfold]
  rw [hrun]
  simp only [zig_unfold] at hpost ⊢
  simp [zig_unfold, hpost]

/-- The light repeats every 3 steps. -/
theorem steps_mod (l : Light) (k : Nat) : steps k l = steps (k % 3) l := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk : k < 3
    · rw [Nat.mod_eq_of_lt hk]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      rw [show steps (j + 3) l = nextSpec (nextSpec (nextSpec (steps j l))) from rfl,
        nextSpec_three, ih j (by omega), Nat.add_mod_right]

theorem advance_mod (l : Light) (n : BitVec 32) :
    advance l n = pure (steps (n.toNat % 3) l) := by
  rw [advance_spec, steps_mod]

/-! ## `totalArea`: a loop over a slice of unions -/

/-- The summed area of the first `k` shapes. -/
def areaSum (xs : Array Shape) (k : Nat) : Nat := ((xs.toList.take k).map areaNat).sum

theorem areaSum_le (xs : Array Shape) (k : Nat) :
    areaSum xs k ≤ (xs.toList.map areaNat).sum := by
  unfold areaSum
  conv => rhs; rw [← List.take_append_drop k xs.toList]
  rw [List.map_append, List.sum_append]
  omega

theorem totalArea_loop_step (xs : Array Shape) (hs : xs.size < 2 ^ 64)
    (hdef : ∀ x ∈ xs.toList, x.Defined) (hsum : (xs.toList.map areaNat).sum < 2 ^ 64) (s : totalAreaLocals)
    (hk : s.local3.toNat ≤ xs.size) (ht : s.total.toNat = areaSum xs s.local3.toNat) :
    ∃ e s', (totalArea.loop7 xs (Zig.len xs)).run s = pure (e, s') ∧
      (if totalArea.again7 e then
          (s'.local3.toNat ≤ xs.size ∧ s'.total.toNat = areaSum xs s'.local3.toNat) ∧
            xs.size - s'.local3.toNat < xs.size - s.local3.toNat
        else e = .br6 ∧ s'.total.toNat = areaSum xs xs.size) := by
  unfold totalArea.loop7
  have hm : xs.size % 18446744073709551616 = xs.size := Nat.mod_eq_of_lt (by omega)
  by_cases hlt : s.local3.toNat < xs.size
  · have hnext : areaSum xs (s.local3.toNat + 1) = areaSum xs s.local3.toNat +
        areaNat xs[s.local3.toNat] := by
      unfold areaSum
      rw [Zig.sum_take_succ _ _ _ (by simpa using hlt)]; simp
    have hle := areaSum_le xs (s.local3.toNat + 1)
    have harea : areaNat xs[s.local3.toNat] < 2 ^ 64 := by omega
    have hadd : ¬ 18446744073709551616 ≤ s.total.toNat + areaNat xs[s.local3.toNat] := by omega
    have hmod : areaNat xs[s.local3.toNat] % 18446744073709551616 = areaNat xs[s.local3.toNat] :=
      Nat.mod_eq_of_lt harea
    have hinc : ¬ 18446744073709551615 ≤ s.local3.toNat := by omega
    refine ⟨.rep7,
      { total := s.total + BitVec.ofNat 64 (areaNat xs[s.local3.toNat])
        local3 := s.local3 + 1 }, ?_, ?_⟩
    · simp [zig_unfold, Zig.len, Zig.index, hlt, hm, area_spec _ (hdef _ (Array.getElem_mem_toList hlt)) harea, hmod, hadd, hinc]
    · have h1 : (s.local3 + 1).toNat = s.local3.toNat + 1 := Zig.toNat_add_one _ (by omega)
      have htot : (s.total + BitVec.ofNat 64 (areaNat xs[s.local3.toNat])).toNat
          = s.total.toNat + areaNat xs[s.local3.toNat] := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, hmod]; omega
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [h1]; omega
      · rw [h1, htot, hnext, ht]
      · rw [h1]; omega
  · have heq : s.local3.toNat = xs.size := by omega
    refine ⟨.br6, s, ?_, ?_⟩
    · simp [zig_unfold, Zig.len, hlt, hm]
    · simp only [totalArea.again7, Bool.false_eq_true, ↓reduceIte]
      exact ⟨trivial, heq ▸ ht⟩

/-- `totalArea` returns the summed area of all shapes, and never panics, when the sum fits in
`u64`. -/
theorem totalArea_spec (xs : Array Shape) (hs : xs.size < 2 ^ 64)
    (hdef : ∀ x ∈ xs.toList, x.Defined) (hsum : (xs.toList.map areaNat).sum < 2 ^ 64) :
    ∃ r, totalArea xs = pure r ∧ r.toNat = (xs.toList.map areaNat).sum := by
  obtain ⟨⟨e, s'⟩, hrun, he, hpost⟩ := Zig.loop_spec (totalArea.loop7 xs (Zig.len xs))
    totalArea.again7
    (fun s => s.local3.toNat ≤ xs.size ∧ s.total.toNat = areaSum xs s.local3.toNat)
    (fun s => xs.size - s.local3.toNat)
    (fun r => r.1 = .br6 ∧ r.2.total.toNat = areaSum xs xs.size)
    (fun s h => totalArea_loop_step xs hs hdef hsum s h.1 h.2)
    { total := 0, local3 := 0 } (by simp [areaSum])
  subst he
  refine ⟨s'.total, ?_, ?_⟩
  · unfold totalArea
    change Zig.loop (totalArea.loop7 xs (Zig.len xs)) totalArea.again7 { total := 0, local3 := 0 }
      = some (Except.ok (totalAreaExit.br6, s')) at hrun
    simp only [zig_unfold]
    rw [hrun]
    simp [zig_unfold]
  · rw [hpost, areaSum, List.take_of_length_le (by simp)]


/-! ## Non-vacuity witnesses -/

nonvacuity_witness area_spec := ⟨.square 3, trivial, by decide, trivial⟩
nonvacuity_witness scale_spec := ⟨.square 3, 2, by unfold scaleFits; decide, trivial⟩
nonvacuity_witness Zig.enumOf.eq_1 := ⟨Unit, (), trivial⟩

end Variants
