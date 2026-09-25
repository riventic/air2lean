import Proofs.Recursion.Gen

/-!
# Proofs about `examples/recursion/recursion.zig`

Each theorem is about the generated code in `Gen.lean`, so it holds for the Zig function to the
extent the translation is faithful (see the differential tests in `tests/diff/`).

`isEven`/`isOdd`/`fact`/`gcd` are `partial_fixpoint`; their unfold equation is `<fn>.eq_1`. The
`isEven`/`isOdd`/`fact` proofs do induction on `n.toNat` (one less each call); the `gcd` proof
does strong induction on the second argument (`a % b < b`).
-/

open Recursion

/-! ## `isEven` / `isOdd` -/

/-- `(k+1) % 2 == 0` and `k % 2 == 1` agree, as `Bool`s: the parity flips each step. -/
theorem succ_parity0 (k : Nat) : ((k + 1) % 2 == 0) = (k % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h, Nat.add_mod]

theorem succ_parity1 (k : Nat) : ((k + 1) % 2 == 1) = (k % 2 == 0) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h, Nat.add_mod]

/-- `isEven`/`isOdd`, proved together by induction on the recursion depth `k = n.toNat`. -/
theorem isEven_isOdd_aux :
    ∀ k : Nat, ∀ n : BitVec 32, n.toNat = k →
      isEven n = pure (k % 2 == 0) ∧ isOdd n = pure (k % 2 == 1) := by
  intro k
  induction k with
  | zero =>
    intro n h
    have hn : n = 0#32 := by apply BitVec.eq_of_toNat_eq; simpa using h
    subst hn
    refine ⟨?_, ?_⟩
    · rw [isEven.eq_1]; simp [zig_unfold]
    · rw [isOdd.eq_1]; simp [zig_unfold]
  | succ k ih =>
    intro n h
    have hn0 : n ≠ 0#32 := by intro h0; rw [h0] at h; simp at h
    -- `n - 1` (a checked sub) does not overflow: `n.toNat = k + 1 ≥ 1`.
    have hn1 : (n - 1#32).toNat = k := by rw [Zig.toNat_sub_one n hn0]; omega
    have hres := ih (n - 1#32) hn1
    refine ⟨?_, ?_⟩
    · rw [isEven.eq_1]
      simp [zig_unfold, hn0, hres.2, h, succ_parity0]
    · rw [isOdd.eq_1]
      simp [zig_unfold, hn0, hres.1, h, succ_parity1]

theorem isEven_spec (n : BitVec 32) : isEven n = pure (n.toNat % 2 == 0) :=
  (isEven_isOdd_aux n.toNat n rfl).1

theorem isOdd_spec (n : BitVec 32) : isOdd n = pure (n.toNat % 2 == 1) :=
  (isEven_isOdd_aux n.toNat n rfl).2

/-! ## `fact` -/

/-- `Nat.factorial` is not in core Lean without Mathlib. -/
def natFact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * natFact n

theorem natFact_mono {m n : Nat} (h : m ≤ n) : natFact m ≤ natFact n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    rename_i n' _
    exact Nat.le_trans ih (Nat.le_mul_of_pos_left (natFact n') (show 0 < n' + 1 by omega))

/-- `fact`, proved by induction on the recursion depth `k = n.toNat`, for `k ≤ 12` (`12! < 2^32`,
`13!` overflows — see `fact_13_panics`). -/
theorem fact_ok_aux :
    ∀ k : Nat, ∀ n : BitVec 32, n.toNat = k → k ≤ 12 →
      fact n = pure (BitVec.ofNat 32 (natFact k)) := by
  intro k
  induction k with
  | zero =>
    intro n h _
    have hn : n = 0#32 := by apply BitVec.eq_of_toNat_eq; simpa using h
    subst hn
    rw [fact.eq_1]
    simp [zig_unfold, natFact]
  | succ k ih =>
    intro n h hb
    have hn0 : n ≠ 0#32 := by intro h0; rw [h0] at h; simp at h
    have hn1 : (n - 1#32).toNat = k := by rw [Zig.toNat_sub_one n hn0]; omega
    have hk12 : k ≤ 12 := by omega
    have hres := ih (n - 1#32) hn1 hk12
    have h12 : natFact 12 = 479001600 := by decide
    have hstep : natFact (k + 1) = (k + 1) * natFact k := rfl
    -- `12! = 479001600 < 2^32`, so `natFact k % 2^32` does not actually wrap.
    have hmod : natFact k % 4294967296 = natFact k := by
      have := natFact_mono hk12
      omega
    -- the checked multiply `n * fact (n - 1)` does not overflow: `(k+1)! ≤ 12! < 2^32`.
    have hnomul : ¬ (4294967296 ≤ (k + 1) * (natFact k % 4294967296)) := by
      rw [hmod]
      have := natFact_mono (show k + 1 ≤ 12 by omega)
      omega
    have hnf : (BitVec.ofNat 32 (natFact k)).toNat = natFact k := by
      rw [BitVec.toNat_ofNat, hmod]
    have hmuleq : n * (BitVec.ofNat 32 (natFact k)) = BitVec.ofNat 32 (natFact (k + 1)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_mul, hnf, BitVec.toNat_ofNat, h, hstep]
    rw [fact.eq_1]
    simp [zig_unfold, hn0, hres, h, hnomul, hmuleq]

theorem fact_ok (n : BitVec 32) (h : n.toNat ≤ 12) :
    fact n = pure (BitVec.ofNat 32 (natFact n.toNat)) :=
  fact_ok_aux n.toNat n rfl h

/-- `13! = 6227020800 ≥ 2^32`: the checked multiply `13 * fact 12` overflows. -/
theorem fact_13_panics : fact (13 : BitVec 32) = throw .overflow := by
  have h12 : fact (12#32 : BitVec 32) = pure (BitVec.ofNat 32 (natFact 12)) :=
    fact_ok 12#32 (by decide)
  have hval : natFact 12 = 479001600 := by decide
  rw [fact.eq_1]
  simp [zig_unfold, h12, hval]

/-! ## `gcd` -/

theorem rem_unsigned (a b : BitVec 32) :
    Zig.rem false a b = if b = 0 then throw .divByZero else pure (a % b) := rfl

/-- The Euclidean step, phrased via core's own `gcd` recursion (on the *first* argument) and
`gcd`'s commutativity, to match `gcd`'s recursion here (on the *second* argument). -/
theorem gcd_step (a b : Nat) : Nat.gcd a b = Nat.gcd b (a % b) := by
  rw [Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm (a % b) b]

/-- `gcd`, proved by strong induction on the recursion depth `b = bb.toNat` (the second argument
decreases via `a % bb < bb`, not by one, so plain induction does not apply here). The generated
code's `p1 != 0` / `Zig.rem`'s own `b = 0` guard (`.divByZero`) are both discharged by `hb0`: the
divisor is never zero on the recursive branch. -/
theorem gcd_spec_aux :
    ∀ b : Nat, ∀ a bb : BitVec 32, bb.toNat = b →
      gcd a bb = pure (BitVec.ofNat 32 (Nat.gcd a.toNat b)) := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a bb hbb
    by_cases hb0 : bb = 0#32
    · subst hb0
      simp only [BitVec.toNat_ofNat] at hbb
      subst hbb
      rw [gcd.eq_1]
      simp [zig_unfold, Nat.gcd_zero_right, BitVec.ofNat_toNat]
    · have hbne : bb.toNat ≠ 0 := by
        intro h0; apply hb0; apply BitVec.eq_of_toNat_eq; simpa using h0
      have hmodlt : (a % bb).toNat < b := by
        rw [BitVec.toNat_umod, ← hbb]; exact Nat.mod_lt _ (by omega)
      have hres := ih (a % bb).toNat hmodlt bb (a % bb) rfl
      have hgcdval : Nat.gcd bb.toNat (a % bb).toNat = Nat.gcd a.toNat b := by
        rw [BitVec.toNat_umod, ← hbb, ← gcd_step]
      rw [hgcdval] at hres
      rw [gcd.eq_1]
      simp [zig_unfold, hb0, rem_unsigned, hres]

theorem gcd_spec (a b : BitVec 32) : gcd a b = pure (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat)) :=
  gcd_spec_aux b.toNat a b rfl
