import Nested.Gen
import ZigLean.Sep.LoopTemplate
import ZigLean.Range

/-!
# A translated nested loop proved with the loop template

`Nested/Gen.lean` is the committed translation of `nested.zig` (retained AIR in
`air/`, checked byte for byte by `check.sh`). `pairs(acc, n)` runs an inner
`while (j < i)` loop inside the body of an outer `while (i < n)` loop; both share the locals
`pairsLocals` and the inner loop is the separate def `pairs.loop14`, called from the outer body
`pairs.loop5` as `Zig.loop (pairs.loop14 p0) pairs.again14`.

* `inner_step` is the inner loop's template; `outer_step` is the outer loop's, and discharges
  the inner loop inside its body by `LoopTemplate.run` (no re-proof of the inner iterations).
* `pairs_total`: `pairs` returns and adds `0 + 1 + … + (n - 1)` to `*acc`, under the explicit
  premise that the total fits in `u64`. The proof uses `pts_load_run`/`pts_store_run` and
  `zig_range` lemmas; it does not unfold `Zig.load`, `Zig.store`, encodings or blocks.
* The `loop_template?` reports at the end show what inference suggests for both loops: the
  measures and bounds used by `outerInv`/`innerInv`, and what it leaves out.
-/

namespace Nested.Proof
open Zig Assn

/-- `cnt k = 0 + 1 + … + (k - 1)`: the pairs `j < i < k`. -/
def cnt : Nat → Nat
  | 0 => 0
  | k + 1 => k + cnt k

def acc (p : Ptr) (x : Nat) : Assn := pts p 8 (BitVec.ofNat 64 x)

/-- Inner loop: `j` counts up to the fixed `i0`; `*p = base + j`. -/
def innerInv (p : Ptr) (i0 : BitVec 32) (base : Nat) (s : pairsLocals) (k : Nat) : Assn :=
  ⌜k = i0.toNat - s.j.toNat ∧ s.i = i0 ∧ s.j.toNat ≤ i0.toNat ∧ base + i0.toNat < 2 ^ 64⌝ ∗
    acc p (base + s.j.toNat)

def innerPost (p : Ptr) (i0 : BitVec 32) (base : Nat) (e : pairsExit) (s : pairsLocals) : Assn :=
  ⌜e = .br13 ∧ s.i = i0⌝ ∗ acc p (base + i0.toNat)

theorem inner_step (p : Ptr) (i0 : BitVec 32) (base : Nat) :
    LoopTemplate (pairs.loop14 p) pairs.again14 (innerInv p i0 base) (innerPost p i0 base) := by
  constructor
  intro s k
  apply TotalTriple.of_run
  intro m h hF hd hm hi hs
  obtain ⟨⟨hk, hi0, hle, hfit⟩, hp⟩ := sep_lift.mp hi
  subst hi0
  by_cases hlt : s.j.toNat < s.i.toNat
  · obtain ⟨m₁, hl, hm₁, hs₁⟩ := pts_load_run hp hm (by decide) hs
    have hv : (BitVec.ofNat 64 (base + s.j.toNat)).toNat = base + s.j.toNat :=
      toNat_ofNat_of_lt (by omega)
    have hadd : Zig.add false (BitVec.ofNat 64 (base + s.j.toNat)) 1#64 =
        pure (BitVec.ofNat 64 (base + (s.j.toNat + 1))) := by
      rw [add_unsigned_of_lt (by rw [hv]; simp; omega)]
      congr 1; apply BitVec.eq_of_toNat_eq; simp [hv]; omega
    obtain ⟨m₂, hst, hs₂, h₂, hd₂, hm₂, hp₂⟩ :=
      pts_store_run hp hm₁ hd (by decide) hs₁ (BitVec.ofNat 64 (base + (s.j.toNat + 1)))
    have hj : Zig.add false s.j 1#32 = pure (s.j + 1#32) :=
      add_unsigned_of_lt (by simp; have := s.i.isLt; omega)
    have hj' : (s.j + 1#32).toNat = s.j.toNat + 1 := toNat_add_of_lt (by simp; have := s.i.isLt; omega)
    refine ⟨(.rep14, { s with j := s.j + 1#32 }), m₂, h₂, ?_, hd₂, hm₂, ?_, hs₂⟩
    · simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hl hst
      have hlt' : s.j.ult s.i = true := by simpa [BitVec.ult] using hlt
      simp [pairs.loop14, zig_unfold, Zig.lt, hlt', hl, -Zig.add_unsigned, hadd, hst, hj]
    · apply loopNext_repeat rfl (n' := s.i.toNat - (s.j.toNat + 1)) (by omega)
      exact sep_lift.mpr ⟨⟨by simp [hj'], rfl, by simp [hj']; omega, hfit⟩, by simpa [acc, hj'] using hp₂⟩
  · have hji : s.j = s.i := BitVec.eq_of_toNat_eq (by omega)
    refine ⟨(.br13, s), m, h, ?_, hd, hm, ?_, hs⟩
    · have hlt' : s.j.ult s.i = false := by simpa [BitVec.ult] using hlt
      simp [pairs.loop14, zig_unfold, Zig.lt, hlt']
    · apply loopNext_exit rfl
      exact sep_lift.mpr ⟨⟨rfl, rfl⟩, by simpa [hji] using hp⟩

/-- Outer loop: `i` counts up to `n`; `*p = v + cnt i`. -/
def outerInv (p : Ptr) (n : BitVec 32) (v : Nat) (s : pairsLocals) (k : Nat) : Assn :=
  ⌜k = n.toNat - s.i.toNat ∧ s.i.toNat ≤ n.toNat ∧ v + cnt n.toNat < 2 ^ 64⌝ ∗
    acc p (v + cnt s.i.toNat)

def outerPost (p : Ptr) (n : BitVec 32) (v : Nat) (e : pairsExit) (_ : pairsLocals) : Assn :=
  ⌜e = .br4⌝ ∗ acc p (v + cnt n.toNat)

theorem cnt_mono {a b : Nat} (h : a ≤ b) : cnt a ≤ cnt b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_add_left _ _)

theorem outer_step (p : Ptr) (n : BitVec 32) (v : Nat) :
    LoopTemplate (pairs.loop5 p n) pairs.again5 (outerInv p n v) (outerPost p n v) := by
  constructor
  intro s k
  apply TotalTriple.of_run
  intro m h hF hd hm hi hs
  obtain ⟨⟨hk, hle, hfit⟩, hp⟩ := sep_lift.mp hi
  by_cases hlt : s.i.toNat < n.toNat
  · -- The inner loop, from `j = 0`, by its own template.
    have hbound : v + cnt s.i.toNat + s.i.toNat < 2 ^ 64 := by
      have := cnt_mono (show s.i.toNat + 1 ≤ n.toNat by omega)
      simp only [cnt] at this; omega
    obtain ⟨e, s', m₁, h₁, hrun, hd₁, hm₁, hpost, hs₁⟩ :=
      (inner_step p s.i (v + cnt s.i.toNat)).run (s := { s with j := 0#32 })
        (n := s.i.toNat) hd hm (sep_lift.mpr ⟨⟨by simp, rfl, by simp, hbound⟩, by simpa using hp⟩) hs
    obtain ⟨⟨rfl, hi'⟩, hp₁⟩ := sep_lift.mp hpost
    have hadd : Zig.add false s'.i 1#32 = pure (s'.i + 1#32) :=
      add_unsigned_of_lt (by simp [hi']; have := n.isLt; omega)
    have hi1 : (s'.i + 1#32).toNat = s.i.toNat + 1 := by
      rw [toNat_add_of_lt (by simp [hi']; have := n.isLt; omega), hi']; simp
    refine ⟨(.rep5, { s' with i := s'.i + 1#32 }), m₁, h₁, ?_, hd₁, hm₁, ?_, hs₁⟩
    · simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hrun
      have hlt' : s.i.ult n = true := by simpa [BitVec.ult] using hlt
      simp [pairs.loop5, zig_unfold, Zig.lt, hlt', hrun, -Zig.add_unsigned, hadd]
    · apply loopNext_repeat rfl (n' := n.toNat - (s.i.toNat + 1)) (by omega)
      refine sep_lift.mpr ⟨⟨by simp [hi1], by simp [hi1]; omega, hfit⟩, ?_⟩
      have hc : v + cnt (s.i.toNat + 1) = v + cnt s.i.toNat + s.i.toNat := by simp only [cnt]; omega
      simpa only [hi1, hc] using hp₁
  · have hin : s.i = n := BitVec.eq_of_toNat_eq (by omega)
    refine ⟨(.br4, s), m, h, ?_, hd, hm, ?_, hs⟩
    · have hlt' : s.i.ult n = false := by simpa [BitVec.ult] using hlt
      simp [pairs.loop5, zig_unfold, Zig.lt, hlt']
    · apply loopNext_exit rfl
      exact sep_lift.mpr ⟨rfl, by simpa [hin] using hp⟩

/-- Both loops of the generated `pairs`, by the template: the outer `step` uses the inner
loop's template through `LoopTemplate.run`. -/
theorem pairs_loop_total (p : Ptr) (n : BitVec 32) (v : Nat) (hfit : v + cnt n.toNat < 2 ^ 64) :
    TotalTriple (acc p v) ((Zig.loop (pairs.loop5 p n) pairs.again5).run { (default : pairsLocals) with i := 0#32 })
      (fun r => outerPost p n v r.1 r.2) := by
  loop_template (outerInv p n v) (outerPost p n v)
  case step => exact outer_step p n v
  case entry => exact fun h hp => ⟨n.toNat, sep_lift.mpr ⟨⟨by simp, by simp, hfit⟩, by simpa [cnt] using hp⟩⟩

/-- `pairs` adds `n * (n - 1) / 2` to `*acc`, under the explicit premise that the sum fits. -/
theorem pairs_total (p : Ptr) (n : BitVec 32) (v : BitVec 64) (hfit : v.toNat + cnt n.toNat < 2 ^ 64) :
    TotalTriple (pts p 8 v) (pairs p n) (fun _ => acc p (v.toNat + cnt n.toNat)) := by
  apply TotalTriple.of_run
  intro m h hF hd hm hp hs
  obtain ⟨⟨e, s'⟩, m', h', hr, hd', hm', hpost, hs'⟩ :=
    pairs_loop_total p n v.toNat hfit m h hF hd hm (by simpa [acc] using hp) hs
  obtain ⟨rfl, hq⟩ := sep_lift.mp hpost
  refine ⟨(), m', h', ?_, hd', hm', hq, hs'⟩
  simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hr
  simp [pairs, zig_unfold, hr]

end Nested.Proof

namespace Nested.Proof
open Zig Assn

/-- info: loop_template remaining premises (2):
  step : LoopTemplate (pairs.loop14 p) pairs.again14 (innerInv p i0 base) (innerPost p i0 base)
  entry : ∀ (h : Heap), innerInv p i0 base s s.i.toNat h → ∃ n, innerInv p i0 base s n h -/
#guard_msgs in
-- The inner loop on its own: the template reduces it to the same named premises.
example (p : Ptr) (i0 : BitVec 32) (base : Nat) (s : pairsLocals) :
    TotalTriple (innerInv p i0 base s s.i.toNat) ((Zig.loop (pairs.loop14 p) pairs.again14).run s)
      (fun r => innerPost p i0 base r.1 r.2) := by
  loop_template? (innerInv p i0 base) (innerPost p i0 base)
  case step => exact inner_step p i0 base
  case entry => exact fun h hi => ⟨_, hi⟩

/-! ## Inference on the two loops -/

/-- info: loop_template? suggestions (unchecked, nothing is proved):
  loop-carried locals (written by the body): j
  unchanged locals: i
  measure candidate: fun s => s.i.toNat - s.j.toNat
  bound invariant candidate: fun s => s.j.toNat ≤ s.i.toNat
  not inferred: side premises (overflow and range bounds), the values of the other carried locals, memory shapes -/
#guard_msgs in
-- Inner loop: `j` steps up towards the unchanged `i`; `innerInv` uses this measure and bound
-- (with `s.i = i0`), plus the accumulator and the overflow premise, which are not inferred.
example (p : Ptr) (i0 : BitVec 32) (base : Nat) (s : pairsLocals) :
    TotalTriple (innerInv p i0 base s s.i.toNat) ((Zig.loop (pairs.loop14 p) pairs.again14).run s)
      (fun r => innerPost p i0 base r.1 r.2) := by
  loop_template?
  exact (inner_step p i0 base).total s |>.conseq (fun h hi => ⟨_, hi⟩) (fun _ _ hp => hp)

/-- info: loop_template? suggestions (unchecked, nothing is proved):
  loop-carried locals (written by the body): i, j
  unchanged locals: (none)
  measure candidate: fun s => n.toNat - s.i.toNat
  bound invariant candidate: fun s => s.i.toNat ≤ n.toNat
  postcondition with n replaced by i: fun e x => ⌜e = pairsExit.br4⌝ ∗ acc p (v + cnt x.i.toNat)
  nested loop pairs.loop14 p: not followed; give it its own template (LoopTemplate.run)
  not inferred: side premises (overflow and range bounds), the values of the other carried locals, memory shapes -/
#guard_msgs in
-- Outer loop: the suggested measure, bound and generalized postcondition are the parts of
-- `outerInv`; its overflow premise and the exit tag are not inferred. The inner loop is
-- reported, not analysed: it could write the counter, so the suggestion is unchecked.
example (p : Ptr) (n : BitVec 32) (v : Nat) (hfit : v + cnt n.toNat < 2 ^ 64) :
    TotalTriple (acc p v) ((Zig.loop (pairs.loop5 p n) pairs.again5).run
        { (default : pairsLocals) with i := 0#32 }) (fun r => outerPost p n v r.1 r.2) := by
  loop_template? _ (outerPost p n v)
  exact pairs_loop_total p n v hfit

end Nested.Proof

-- Only the standard axioms: no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`).
/-- info: 'Nested.Proof.pairs_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Nested.Proof.pairs_total
