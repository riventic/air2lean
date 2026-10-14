import Nested.Gen
import ZigLean.Sep.Full.Loop
import ZigLean.Sep.Full.Auto

/-!
# A translated nested loop in the full-state logic

`Nested/Gen.lean` is the committed translation of `nested.zig` (retained AIR in
`air/`, checked byte for byte by `check.sh`). `pairs(acc, n)` runs an inner
`while (j < i)` loop inside the body of an outer `while (i < n)` loop; both share the locals
`pairsLocals` and the inner loop is the separate def `pairs.loop14`, called from the outer body
`pairs.loop5` as `Zig.loop (pairs.loop14 p0) pairs.again14`.

* `inner_step`/`outer_step`: one run of each body, by `fsym`. The outer body's walk uses the
  inner loop's triple `inner_loop` as a rule (`fsym [inner_loop]`): the inner iterations are
  proved once.
* `inner_loop`/`outer_loop`: the loops by `FTotalTriple.loop_measure` (a measure on the locals).
* `pairs_total`: `pairs` returns and adds `0 + 1 + … + (n - 1)` to `*acc`, under the explicit
  premise that the total fits in `u64`.

Its strength log (the legacy total triple on every `Mem.FSeqPlain` memory, the strength check of
`docs/proof-framework.md`) is `tests/roadmap/strength-log/LoopTactics.lean`.
-/

namespace Nested.Proof
open Zig Zig.Full Zig.Full.FAssn Zig.Full.Auto

/-- `cnt k = 0 + 1 + … + (k - 1)`: the pairs `j < i < k`. -/
def cnt : Nat → Nat
  | 0 => 0
  | k + 1 => k + cnt k

/-- `*p` holds `x`. -/
def acc (p : Ptr) (x : Nat) : FAssn := FAssn.ex fun v : BitVec 64 => ⟪v.toNat = x⟫ ⋆ up (pts p 8 v)

/-- Inner loop from `j0` with `*p = w` at entry: `*p = w + (j - j0)`. -/
def innerI (p : Ptr) (w : BitVec 64) (j0 : Nat) (s : pairsLocals) : FAssn :=
  ⟪j0 ≤ s.j.toNat ∧ s.j.toNat ≤ s.i.toNat ∧ w.toNat + (s.i.toNat - j0) < 2 ^ 64⟫ ⋆
    acc p (w.toNat + (s.j.toNat - j0))

theorem inner_step (p : Ptr) (w : BitVec 64) (j0 : Nat) (i0 : BitVec 32) (s : pairsLocals) :
    FTotalTriple (⟪s.i = i0⟫ ⋆ innerI p w j0 s) ((pairs.loop14 p).run s)
      (fun r => if pairs.again14 r.1 then ⟪i0.toNat - r.2.j.toNat < i0.toNat - s.j.toNat⟫ ⋆ (⟪r.2.i = i0⟫ ⋆ innerI p w j0 r.2)
        else ⟪r.1 = .br13 ∧ r.2.i = i0⟫ ⋆ acc p (w.toNat + (i0.toNat - j0))) := by
  unfold pairs.loop14 innerI acc
  fsym

/-- The inner loop, as a rule for `fsym`: from `*p = w` it adds `i - j`. The loop's `MonoBind`
proof is a parameter, so the rule's command unifies with any elaboration of it. -/
theorem inner_loop {mb : Lean.Order.MonoBind (MM pairsLocals)} (p : Ptr) (w : BitVec 64)
    (s : pairsLocals) (hj : s.j.toNat ≤ s.i.toNat) (hfit : w.toNat + (s.i.toNat - s.j.toNat) < 2 ^ 64) :
    FTotalTriple (up (pts p 8 w))
      ((@Zig.loop (MM pairsLocals) _ _ mb _ (pairs.loop14 p) pairs.again14).run s)
      (fun r => FAssn.ex fun t : pairsLocals => ⟪r = (.br13, t) ∧ t.i = s.i⟫ ⋆
        FAssn.ex fun v : BitVec 64 => ⟪v.toNat = w.toNat + (s.i.toNat - s.j.toNat)⟫ ⋆ up (pts p 8 v)) :=
  (FTotalTriple.loop_measure (fun t => ⟪t.i = s.i⟫ ⋆ innerI p w s.j.toNat t) (fun t => s.i.toNat - t.j.toNat) _
    (inner_step p w s.j.toNat s.i) s).eupd (by unfold innerI acc; fsym_entail)
    |>.eupd_post fun ⟨e, t⟩ => EUpd.of_imp fun _ h => by
      obtain ⟨⟨he, hi⟩, h⟩ := sep_lift.mp h
      exact ⟨t, sep_lift.mpr ⟨⟨by simp only at he; rw [he], hi⟩, h⟩⟩

theorem cnt_mono {a b : Nat} (h : a ≤ b) : cnt a ≤ cnt b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- Outer loop: `i` counts up to `n`; `*p = v + cnt i`. -/
def outerI (p : Ptr) (n : BitVec 32) (v : Nat) (s : pairsLocals) : FAssn :=
  ⟪s.i.toNat ≤ n.toNat ∧ v + cnt n.toNat < 2 ^ 64⟫ ⋆ acc p (v + cnt s.i.toNat)

def outerPost (p : Ptr) (n : BitVec 32) (v : Nat) (r : pairsExit × pairsLocals) : FAssn :=
  ⟪r.1 = .br4⟫ ⋆ acc p (v + cnt n.toNat)

theorem outer_step (p : Ptr) (n : BitVec 32) (v : Nat) (s : pairsLocals) :
    FTotalTriple (outerI p n v s) ((pairs.loop5 p n).run s)
      (fun r => if pairs.again5 r.1 then ⟪n.toNat - r.2.i.toNat < n.toNat - s.i.toNat⟫ ⋆ outerI p n v r.2
        else outerPost p n v r) := by
  unfold pairs.loop5 outerI outerPost
  have hm : s.i.toNat < n.toNat → cnt s.i.toNat + s.i.toNat ≤ cnt n.toNat := fun h => by
    have := cnt_mono (show s.i.toNat + 1 ≤ n.toNat by omega); simpa only [cnt, Nat.add_comm] using this
  fsym [inner_loop]
  · -- the counter's step: `cnt (i + 1) = cnt i + i`
    rename_i hti _ hx
    rw [show x.toNat = s.i.toNat + 1 by rw [hx, hti]; rfl, cnt]
    have : (0#32).toNat = 0 := rfl
    omega
  · -- the exit: `i = n`
    have : s.i.toNat = n.toNat := by simp only [lt_false, decide_eq_true_eq] at hc; omega
    rw [← this]; omega

theorem outer_loop {mb : Lean.Order.MonoBind (MM pairsLocals)} (p : Ptr) (n : BitVec 32) (w : BitVec 64)
    (s : pairsLocals) (hi : s.i = 0) (hfit : w.toNat + cnt n.toNat < 2 ^ 64) :
    FTotalTriple (up (pts p 8 w))
      ((@Zig.loop (MM pairsLocals) _ _ mb _ (pairs.loop5 p n) pairs.again5).run s)
      (fun r => FAssn.ex fun t : pairsLocals => ⟪r = (.br4, t)⟫ ⋆
        FAssn.ex fun v : BitVec 64 => ⟪v.toNat = w.toNat + cnt n.toNat⟫ ⋆ up (pts p 8 v)) :=
  (FTotalTriple.loop_measure (outerI p n w.toNat) (fun t => n.toNat - t.i.toNat) _
    (outer_step p n w.toNat) s).eupd (by unfold outerI acc; simp only [hi]; fsym_entail)
    |>.eupd_post fun ⟨e, t⟩ => EUpd.of_imp fun _ h => by
      obtain ⟨he, h⟩ := sep_lift.mp h
      exact ⟨t, sep_lift.mpr ⟨by simp only at he; rw [he], h⟩⟩

/-- `pairs` adds `0 + 1 + … + (n - 1)` to `*acc`, under the premise that the sum fits. -/
theorem pairs_total (p : Ptr) (n : BitVec 32) (v : BitVec 64) (hfit : v.toNat + cnt n.toNat < 2 ^ 64) :
    FTotalTriple (up (pts p 8 v)) (pairs p n)
      (fun _ => up (pts p 8 (BitVec.ofNat 64 (v.toNat + cnt n.toNat)))) := by
  unfold pairs
  fsym [outer_loop]

end Nested.Proof

-- Only the standard axioms: no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`).
/-- info: 'Nested.Proof.pairs_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Nested.Proof.pairs_total
