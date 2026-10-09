import Proofs.Recursion.Gen
import Proofs.Pointers.Gen
import ZigLean.Sep.Total
import ZigLean.Range
import ZigLean.RecTemplate

/-!
# Recursive generated functions proved with `rec_template`

The functions are the committed translations of `examples/recursion/recursion.zig` and
`examples/pointers/pointers.zig` (`Proofs/Recursion/Gen.lean`, `Proofs/Pointers/Gen.lean`):
`partial_fixpoint` defs with no induction principle of their own.

* `gcd`: self-recursive; the second argument decreases by `a % b < b`, not by one.
* `isEven`/`isOdd`: a mutually recursive group, one `mutual` block; one conjunction, one
  measure, both members unfolded.
* `fact`: self-recursive with a checked multiply; the specification carries a range premise.
* `addDown`: a memory-backed recursive function (`Zig.callM`), proved as a `TotalTriple` through
  the separation interface (`pts_load_run`, `pts_store_run`) without unfolding `Zig.load`,
  `Zig.store`, byte encodings or blocks.

Each proof starts with `rec_template μ unfolding f`, which supplies the strong induction on
`μ` and the induction hypothesis `ih`; the proof discharges the measure decrease at the
recursive call when it applies `ih`.
-/

namespace RecTemplateTest
open Zig Assn

/-! ## Self-recursive: `gcd` -/

theorem rem_unsigned (a b : BitVec 32) :
    Zig.rem false a b = if b = 0 then throw .divByZero else pure (a % b) := rfl

/-- info: rec_template remaining premise (1):
  step : ∀ (a b : BitVec 32),
  (∀ (a b_1 : BitVec 32), b_1.toNat < b.toNat → Recursion.gcd a b_1 = pure (BitVec.ofNat 32 (a.toNat.gcd b_1.toNat))) →
    Recursion.gcd a b = pure (BitVec.ofNat 32 (a.toNat.gcd b.toNat))
  unfolded: Recursion.gcd -/
#guard_msgs in
theorem gcd_spec : ∀ a b : BitVec 32,
    Recursion.gcd a b = pure (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat)) := by
  rec_template? (fun (_ b : BitVec 32) => b.toNat) unfolding Recursion.gcd
  by_cases hb0 : b = 0#32
  · subst hb0
    simp [zig_unfold, BitVec.ofNat_toNat]
  · have hbne : b.toNat ≠ 0 := fun h0 => hb0 (BitVec.eq_of_toNat_eq (by simpa using h0))
    -- The recursive call `gcd b (a % b)`: the measure decreases because `a % b < b`.
    have hres := ih b (a % b) (by rw [BitVec.toNat_umod]; exact Nat.mod_lt _ (by omega))
    rw [BitVec.toNat_umod, Nat.gcd_comm b.toNat, ← Nat.gcd_rec, Nat.gcd_comm] at hres
    simp [zig_unfold, hb0, rem_unsigned, hres]

/-! ## Mutually recursive: `isEven` / `isOdd` -/

theorem succ_parity0 (k : Nat) : ((k + 1) % 2 == 0) = (k % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h, Nat.add_mod]

theorem succ_parity1 (k : Nat) : ((k + 1) % 2 == 1) = (k % 2 == 0) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h, Nat.add_mod]

/-- `n.toNat = (n - 1).toNat + 1` for `n ≠ 0`: the recursive argument is one smaller. -/
theorem toNat_pred (n : BitVec 32) (hn0 : n ≠ 0#32) : n.toNat = (n - 1#32).toNat + 1 := by
  rw [Zig.toNat_sub_one n hn0]
  have : n.toNat ≠ 0 := fun h => hn0 (BitVec.eq_of_toNat_eq (by simpa using h))
  omega

/-- info: rec_template remaining premise (1):
  step : ∀ (n : BitVec 32),
  (∀ (n_1 : BitVec 32),
      n_1.toNat < n.toNat →
        Recursion.isEven n_1 = pure (n_1.toNat % 2 == 0) ∧ Recursion.isOdd n_1 = pure (n_1.toNat % 2 == 1)) →
    Recursion.isEven n = pure (n.toNat % 2 == 0) ∧ Recursion.isOdd n = pure (n.toNat % 2 == 1)
  unfolded: Recursion.isEven, Recursion.isOdd -/
#guard_msgs in
theorem isEven_isOdd_spec : ∀ n : BitVec 32,
    Recursion.isEven n = pure (n.toNat % 2 == 0) ∧ Recursion.isOdd n = pure (n.toNat % 2 == 1) := by
  rec_template? (fun n : BitVec 32 => n.toNat) unfolding Recursion.isEven, Recursion.isOdd
  by_cases hn0 : n = 0#32
  · subst hn0; simp [zig_unfold]
  · have hn := toNat_pred n hn0
    -- Each member's call goes to the other member at `n - 1`.
    obtain ⟨he, ho⟩ := ih (n - 1#32) (by omega)
    generalize (n - 1#32).toNat = k at he ho hn
    simp [zig_unfold, hn0, he, ho, hn, succ_parity0, succ_parity1]

/-! ## A range premise in the specification: `fact` -/

def natFact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * natFact n

theorem natFact_mono {m n : Nat} (h : m ≤ n) : natFact m ≤ natFact n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    rename_i n' _
    exact Nat.le_trans ih (Nat.le_mul_of_pos_left (natFact n') (show 0 < n' + 1 by omega))

/-- The premise `n.toNat ≤ 12` stays in the goal, so `ih` asks for it at the call. -/
theorem fact_spec : ∀ n : BitVec 32, n.toNat ≤ 12 →
    Recursion.fact n = pure (BitVec.ofNat 32 (natFact n.toNat)) := by
  rec_template (fun n : BitVec 32 => n.toNat) unfolding Recursion.fact
  intro hb
  by_cases hn0 : n = 0#32
  · subst hn0; simp [zig_unfold, natFact]
  · have hn := toNat_pred n hn0
    have hres := ih (n - 1#32) (by omega) (by omega)
    generalize (n - 1#32).toNat = k at hres hn
    have hmod : natFact k % 4294967296 = natFact k := by
      have := natFact_mono (show k ≤ 12 by omega)
      have : natFact 12 = 479001600 := by decide
      omega
    have hnomul : ¬ (4294967296 ≤ (k + 1) * (natFact k % 4294967296)) := by
      rw [hmod]
      have := natFact_mono (show k + 1 ≤ 12 by omega)
      have : natFact 12 = 479001600 := by decide
      simp only [natFact] at *; omega
    have hmuleq : n * BitVec.ofNat 32 (natFact k) = BitVec.ofNat 32 (natFact (k + 1)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, hmod, BitVec.toNat_ofNat, hn]; rfl
    simp [zig_unfold, hn0, hres, hn, hnomul, hmuleq]

/-! ## Memory-backed recursion: `addDown` -/

/-- `tri k = k + (k - 1) + … + 1`. -/
def tri : Nat → Nat
  | 0 => 0
  | k + 1 => (k + 1) + tri k

/-- `addDown acc n` adds `n + (n - 1) + … + 1` to `*acc`, under the explicit premise that the
total fits in `u64` (otherwise the checked add panics). Total correctness: it returns. -/
theorem addDown_total (p : Ptr) : ∀ (n : BitVec 32) (v : BitVec 64), v.toNat + tri n.toNat < 2 ^ 64 →
    TotalTriple (pts p 8 v) (Pointers.addDown p n)
      (fun _ => pts p 8 (v + BitVec.ofNat 64 (tri n.toNat))) := by
  rec_template (fun (n : BitVec 32) (_ : BitVec 64) => n.toNat) unfolding Pointers.addDown
  intro hfit
  apply TotalTriple.of_run
  intro m h hF hd hm hp hs
  by_cases hn0 : n = 0#32
  · subst hn0
    refine ⟨(), m, h, ?_, hd, hm, by simpa [tri] using hp, hs⟩
    simp [zig_unfold]
  · have hk := toNat_pred n hn0
    simp only [hk, tri] at hfit
    obtain ⟨m₁, hl, hm₁, hs₁⟩ := pts_load_run hp hm (by decide) hs
    have hz : (n.setWidth 64).toNat = n.toNat := toNat_setWidth_of_le (by decide)
    have hadd : Zig.add false v (n.setWidth 64) = pure (v + n.setWidth 64) :=
      add_unsigned_of_lt (by omega)
    obtain ⟨m₂, hst, hs₂, h₂, hd₂, hm₂, hp₂⟩ :=
      pts_store_run hp hm₁ hd (by decide) hs₁ (v + n.setWidth 64)
    -- The recursive call `addDown acc (n - 1)` from the stored value, by `ih`.
    have hfit' : (v + n.setWidth 64).toNat + tri (n - 1#32).toNat < 2 ^ 64 := by
      rw [toNat_add_of_lt (by omega), hz]; omega
    obtain ⟨u, m₃, h₃, hrec, hd₃, hm₃, hp₃, hs₃⟩ :=
      ih (n - 1#32) (v + n.setWidth 64) (by omega) hfit' m₂ h₂ hF hd₂ hm₂ hp₂ hs₂
    refine ⟨(), m₃, h₃, ?_, hd₃, hm₃, ?_, hs₃⟩
    · simp only [StateT.run, pure, ExceptT.pure, ExceptT.mk] at hl hst hrec
      have hnz : n.toNat ≠ 0 := by omega
      simp [zig_unfold, hn0, hnz, hl, -Zig.add_unsigned, hadd, hst, hrec]
    · have heq : v + BitVec.ofNat 64 (tri n.toNat) =
          v + n.setWidth 64 + BitVec.ofNat 64 (tri (n - 1#32).toNat) := by
        rw [BitVec.add_assoc]; congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [hk, tri, BitVec.toNat_add, BitVec.toNat_ofNat, hz]
        omega
      rw [heq]; exact hp₃

/-! ## Rejections -/

/-- error: rec_template: the goal has fewer than 2 leading binders: ∀ (n : BitVec 32), Recursion.fact n = Recursion.fact n -/
#guard_msgs in
example : ∀ n : BitVec 32, Recursion.fact n = Recursion.fact n := by
  rec_template (fun (a b : BitVec 32) => a.toNat + b.toNat)

/-- error: rec_template: the measure does not fit the goal's binders -/
#guard_msgs in
example : ∀ n : Nat, n = n := by
  rec_template (fun n : BitVec 32 => n.toNat)

end RecTemplateTest

/-- info: 'RecTemplateTest.addDown_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecTemplateTest.addDown_total

/-- info: 'RecTemplateTest.isEven_isOdd_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RecTemplateTest.isEven_isOdd_spec
