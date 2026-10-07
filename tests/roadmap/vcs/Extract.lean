import ZigLean.VC
import Proofs.Basic.Gen
import Proofs.Pointers.Gen
import Proofs.Errors.Gen

/-!
Automatic VC extraction (P02) on committed generated code: `Proofs/Basic/Gen.lean`,
`Proofs/Pointers/Gen.lean` and `Proofs/Errors/Gen.lean`, generated from `examples/`.
Every program below is reflected from the generated body by `#vc_extract`/`vc_gen`; none is
written by hand. The source equalities are kernel-checked; they link the VC AST to those
translated functions only and do not prove Zig/AIR/compiler preservation.
-/

namespace VCExtract

open Zig Assn VC

/-! ## Extraction: `vc_f`, `vc_f_source`, `vc_f_sound` -/

/--
info: vc extraction for `Basic.tardiness`: added `Basic.vc_tardiness`, `Basic.vc_tardiness_source`, `Basic.vc_tardiness_sound`
-/
#guard_msgs in
#vc_extract Basic.tardiness

-- The extracted program is the generated body's control flow; `Zig.sub` became a checked
-- primitive contract whose precondition is a safety obligation.
example (a b : BitVec 32) : Basic.vc_tardiness a b =
    .branch (Zig.gt false a b)
      (.call "safety: Zig.sub [Zig.VC.Prim.sub_unsigned]" (Zig.sub false a b)
        (b.toNat ≤ a.toNat) (fun v => v = a - b) (Prim.sub_unsigned a b))
      (.ret 0) := rfl

-- The kernel-checked link to the committed generated function, and the transported soundness.
example (a b : BitVec 32) : (Basic.vc_tardiness a b).eval = Basic.tardiness a b :=
  Basic.vc_tardiness_source a b
example (a b : BitVec 32) (post : BitVec 32 → Prop) :
    (Basic.vc_tardiness a b).vc post → ∃ v, Basic.tardiness a b = pure v ∧ post v :=
  Basic.vc_tardiness_sound a b post

/-! ## A contracted loop-free function receives complete obligations

`vc_gen?` lists every obligation, by kind, with the path conditions it is under; the report is
pinned by `tests/roadmap/vcs/report.json` (`scripts/vc-report.py`). -/

theorem tardiness_contract (a b : BitVec 32) :
    ∃ v, Basic.tardiness a b = pure v ∧ v.toNat = a.toNat - b.toNat := by
  vc_gen?
  case safety_1 => simp at branch1; omega
  case result_1 => simp at branch1; subst summary2; rw [BitVec.toNat_sub]; omega
  case result_2 => simp at branch1; simp; omega

/-! ## A wrong contract leaves an unprovable obligation

The contract `v = a - b` forgets the saturation at zero. Extraction does not repair it: after
the provable obligations are closed, exactly the non-taken branch remains. -/

/--
error: unsolved goals
case result_2
a b : BitVec 32
branch1 : gt false a b = false
⊢ 0 = a - b
-/
#guard_msgs in
example (a b : BitVec 32) : ∃ v, Basic.tardiness a b = pure v ∧ v = a - b := by
  vc_gen
  case safety_1 => simp at branch1; omega
  case result_1 => exact summary2

-- That remaining obligation is false (a = 1, b = 2), so this contract has no proof at all.
theorem wrong_obligation_false :
    ¬ ∀ a b : BitVec 32, gt false a b = false → (0 : BitVec 32) = a - b := by
  intro h
  exact absurd (h 1 2 (by decide)) (by decide)

theorem wrong_contract_false :
    ¬ ∀ a b : BitVec 32, ∃ v, Basic.tardiness a b = pure v ∧ v = a - b := by
  intro h
  obtain ⟨v, hv, he⟩ := h 1 2
  have hrun : Basic.tardiness 1 2 = pure 0 := rfl
  rw [hrun] at hv
  cases hv
  exact absurd he (by decide)

/-! ## Compositional calls use proved contracts

A call to another generated function needs a `@[vc_contract]`; without one, extraction
refuses instead of assuming a summary. -/

/--
error: vc extraction for `Basic.weightedTardiness` refused: no VC rule or `@[vc_contract]` theorem for `Basic.tardiness`:
  Basic.tardiness x p0.due
-/
#guard_msgs in
#vc_extract Basic.weightedTardiness

attribute [vc_contract] tardiness_contract

/--
info: vc extraction for `Basic.weightedTardiness`: added `Basic.vc_weightedTardiness`, `Basic.vc_weightedTardiness_source`, `Basic.vc_weightedTardiness_sound`
-/
#guard_msgs in
#vc_extract Basic.weightedTardiness

-- The same statement as `Proofs/Basic/Proofs.lean`'s `weightedTardiness_ok`, from its VCs.
theorem weightedTardiness_contract (j : Basic.Job) (start : BitVec 32)
    (h1 : start.toNat + j.duration.toNat < 2 ^ 32)
    (h2 : (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat < 2 ^ 32) :
    ∃ r, Basic.weightedTardiness j start = pure r ∧
      r.toNat = (start.toNat + j.duration.toNat - j.due.toNat) * j.weight.toNat := by
  have hw := j.weight.isLt
  have hsum : (start + j.duration).toNat = start.toNat + j.duration.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h1
  have hw32 : j.weight.toNat % 2 ^ 32 = j.weight.toNat := Nat.mod_eq_of_lt (by omega)
  vc_gen
  case safety_1 => exact h1
  case safety_2 => trivial
  case safety_3 => decide
  case safety_4 =>
    simp only [BitVec.toNat_setWidth, hw32, summary1, hsum]
    exact h2
  case result_1 =>
    subst summary2
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, hw32, summary1, hsum]
    exact Nat.mod_eq_of_lt h2

/-! ## Error returns are a separate category -/

/--
info: vc extraction for `Errors.parseDigit`: added `Errors.vc_parseDigit`, `Errors.vc_parseDigit_source`, `Errors.vc_parseDigit_sound`
-/
#guard_msgs in
#vc_extract Errors.parseDigit

theorem parseDigit_contract (c : BitVec 8) :
    ∃ v, Errors.parseDigit c = pure v ∧
      v = if c.toNat < 48 ∨ 57 < c.toNat then .error "NotDigit" else .ok (c - 48) := by
  vc_gen?
  case result_1 =>
    subst summary3
    simp [Zig.lt, Zig.gt, BitVec.ult] at branch1 branch2
    have digit : ¬ (c.toNat < 48 ∨ 57 < c.toNat) := by omega
    simp [digit]
  all_goals simp [Zig.lt, Zig.gt, BitVec.ult] at * <;> omega

attribute [vc_contract] parseDigit_contract

-- `catch 0`: the callee's error return is consumed through the checked unwrap primitives.
theorem digitOrZero_contract (c : BitVec 8) :
    ∃ v, Errors.digitOrZero c = pure v ∧
      v = if c.toNat < 48 ∨ 57 < c.toNat then 0 else c - 48 := by
  vc_gen
  case safety_1 => trivial
  case safety_2 => exact branch2
  case safety_3 => simpa [Zig.isNonErr] using branch2
  case result_1 => by_cases h : c.toNat < 48 ∨ 57 < c.toNat <;> simp_all <;> omega
  case result_2 => by_cases h : c.toNat < 48 ∨ 57 < c.toNat <;> simp_all [Zig.isNonErr, Zig.isErr]

/-! ## Memory effects: generated loads and stores -/

theorem addTo_contract (p : Ptr) (delta : BitVec 32) (old : BitVec 64)
    (fits : old.toNat + (delta.setWidth 64).toNat < 2 ^ 64) :
    Triple (pts p 8 old) (Pointers.addTo p delta)
      (fun _ => pts p 8 (old + delta.setWidth 64)) := by
  vc_gen?
  case memory_1 => decide
  case safety_1 => decide
  case safety_2 => exact fits
  case memory_2 => decide
  case memory_4 => exact stored1

-- The unchanged frame rule preserves a separate client resource.
example (p : Ptr) (delta : BitVec 32) (old : BitVec 64) (R : Assn)
    (fits : old.toNat + (delta.setWidth 64).toNat < 2 ^ 64) :
    Triple (pts p 8 old ∗ R) (Pointers.addTo p delta)
      (fun _ => pts p 8 (old + delta.setWidth 64) ∗ R) :=
  (addTo_contract p delta old fits).frame

-- `ensures` separates a functional result from the heap effect.
theorem same_contract (p q : Ptr) :
    Triple emp (Pointers.same p q) (ensures (fun r => r = (p == q)) (fun _ => emp)) := by
  vc_gen
  case result_1 => rfl
  case memory_1 => exact pre

/-! ## Loops request explicit invariants and variants; recursion is refused -/

/--
error: vc extraction for `Basic.sum`:
  invariant + variant required for loop `Basic.sum.loop7` at AIR instruction %7
VC extraction does not guess invariants. For a memory loop, prove `(Zig.loop body again).run s` with `loop_template inv post` (goals `step`, `entry`, `exit`; `inv s n` carries the variant `n`) or `MemProgram.annotatedLoop`; for a `Result` loop use `Zig.loop_spec` (invariant `inv`, variant `m`). Register the proved function contract with `@[vc_contract]` so callers can use it.
vc-report {"function":"Basic.sum","requests":[{"instruction":7,"loop":"Basic.sum.loop7","request":"invariant + variant"}],"status":"loop-request"}
-/
#guard_msgs in
#vc_extract Basic.sum

/--
error: vc extraction for `Pointers.sumTo`:
  invariant + variant required for loop `Pointers.sumTo.loop6` at AIR instruction %6
VC extraction does not guess invariants. For a memory loop, prove `(Zig.loop body again).run s` with `loop_template inv post` (goals `step`, `entry`, `exit`; `inv s n` carries the variant `n`) or `MemProgram.annotatedLoop`; for a `Result` loop use `Zig.loop_spec` (invariant `inv`, variant `m`). Register the proved function contract with `@[vc_contract]` so callers can use it.
vc-report {"function":"Pointers.sumTo","requests":[{"instruction":6,"loop":"Pointers.sumTo.loop6","request":"invariant + variant"}],"status":"loop-request"}
-/
#guard_msgs in
#vc_extract Pointers.sumTo

-- `vc_gen` fails closed the same way: no goal is produced from a guessed invariant.
/--
error: vc extraction for `Basic.sum`:
  invariant + variant required for loop `Basic.sum.loop7` at AIR instruction %7
VC extraction does not guess invariants. For a memory loop, prove `(Zig.loop body again).run s` with `loop_template inv post` (goals `step`, `entry`, `exit`; `inv s n` carries the variant `n`) or `MemProgram.annotatedLoop`; for a `Result` loop use `Zig.loop_spec` (invariant `inv`, variant `m`). Register the proved function contract with `@[vc_contract]` so callers can use it.
vc-report {"function":"Basic.sum","requests":[{"instruction":7,"loop":"Basic.sum.loop7","request":"invariant + variant"}],"status":"loop-request"}
-/
#guard_msgs in
example (xs : Array (BitVec 32)) : ∃ v, Basic.sum xs = pure v ∧ True := by
  vc_gen

/--
error: vc extraction for `Pointers.addDown` refused: `Pointers.addDown` is recursive; a recursive call needs an explicit measure and a separately proved contract, so no VC is extracted
-/
#guard_msgs in
#vc_extract Pointers.addDown

end VCExtract
