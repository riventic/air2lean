import Proofs.Recursion.Gen
import ZigLean.Witness
import ZigLean.Sep.Full.Auto
import ZigLean.Sep.Full.Init
import ZigLean.Sep.Full.Loop
import ZigLean.Sep.Full.Slice

/-!
# Proofs about `examples/recursion/recursion.zig`

Each theorem is about the generated code in `Gen.lean`, so it holds for the Zig function to the
extent the translation is faithful (see the differential tests in `tests/diff/`).

`isEven`/`isOdd`/`fact`/`gcd` are `partial_fixpoint`. All three groups have full-state
total contracts, proved by `FTotalTriple.rec_group` and one `fsym` step per group. Their public
equalities follow from total adequacy. The factorial contract retains its checked-overflow
bound `n.toNat ≤ 12`; the existing `13!` panic remains a separate boundary result.

**Stack premise.** These functions are pure (`Zig.Result`), so the model charges no frames:
each theorem holds for the native function only if the native stack holds the recursion it
states (premise STK-01, `docs/premises.md`). The recursion depth is `n.toNat + 1` for
`isEven`/`isOdd`/`fact` and at most `b.toNat + 1` for `gcd`, so a statement about large inputs
assumes a native stack of that many frames (MM-5, `docs/architecture-audit/memory-model.md`).
-/

open Recursion

/-! ## `isEven` / `isOdd` -/

/-- `(k+1) % 2 == 0` and `k % 2 == 1` agree, as `Bool`s: the parity flips each step. -/
theorem succ_parity0 (k : Nat) : ((k + 1) % 2 == 0) = (k % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h, Nat.add_mod]

theorem succ_parity1 (k : Nat) : ((k + 1) % 2 == 1) = (k % 2 == 0) := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h, Nat.add_mod]

private theorem parity_step0 (a b : Nat) (h : a + 1 = b) :
    (a % 2 == 1) = (b % 2 == 0) := by
  subst b
  exact (succ_parity0 a).symm

private theorem parity_step1 (a b : Nat) (h : a + 1 = b) :
    (a % 2 == 0) = (b % 2 == 1) := by
  subst b
  exact (succ_parity1 a).symm

open Zig Zig.Full Zig.Full.FAssn

/-- A tag selects the generated member; both members take every 32-bit unsigned input. -/
private abbrev ParityInvocation := Sum (BitVec 32) (BitVec 32)

private def parityCode (a : ParityInvocation) : MemM Bool :=
  StateT.lift (match a with | .inl n => isEven n | .inr n => isOdd n)

private def parityValue : ParityInvocation → Bool
  | .inl n => n.toNat % 2 == 0
  | .inr n => n.toNat % 2 == 1

private def parityRank : ParityInvocation → Nat
  | .inl n | .inr n => n.toNat

/-- The generated mutual group terminates with its parity result and preserves every frame.
The rank is a termination measure, not a model of the native stack (STK-01). -/
private theorem parity_total (a : ParityInvocation) :
    FTotalTriple emp (parityCode a) (fun v => ⟪v = parityValue a⟫) := by
  refine FTotalTriple.rec_group parityCode (fun _ => emp)
    (fun a v => ⟪v = parityValue a⟫) parityRank ?_ a
  intro a smaller
  fsym
  all_goals
    have hone : (1#32).toNat = 1 := rfl
    simp only [parityValue]
    first
    | apply parity_step0; omega
    | apply parity_step1; omega

theorem isEven_total (n : BitVec 32) :
    FTotalTriple emp (StateT.lift (isEven n) : MemM Bool)
      (fun v => ⟪v = (n.toNat % 2 == 0)⟫) :=
  parity_total (.inl n)

theorem isOdd_total (n : BitVec 32) :
    FTotalTriple emp (StateT.lift (isOdd n) : MemM Bool)
      (fun v => ⟪v = (n.toNat % 2 == 1)⟫) :=
  parity_total (.inr n)

theorem isEven_spec (n : BitVec 32) : isEven n = pure (n.toNat % 2 == 0) :=
  (isEven_total n).result_eq

theorem isOdd_spec (n : BitVec 32) : isOdd n = pure (n.toNat % 2 == 1) :=
  (isOdd_total n).result_eq

/-- Compatibility with the original simultaneous statement, now from the group contract. -/
theorem isEven_isOdd_aux :
    ∀ k : Nat, ∀ n : BitVec 32, n.toNat = k →
      isEven n = pure (k % 2 == 0) ∧ isOdd n = pure (k % 2 == 1) := by
  intro k n h
  simpa only [h] using And.intro (isEven_spec n) (isOdd_spec n)

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

private def factCode (n : BitVec 32) : MemM (BitVec 32) :=
  StateT.lift (fact n)

private def factValue (n : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (natFact n.toNat)

private theorem natFact_lt {k : Nat} (h : k ≤ 12) : natFact k < 2 ^ 32 := by
  have h12 : natFact 12 = 479001600 := by decide
  have := natFact_mono h
  omega

private theorem fact_product (n p : BitVec 32) (hb : n.toNat ≤ 12)
    (hp : p.toNat + 1 = n.toNat) : n.toNat * (factValue p).toNat = natFact n.toNat := by
  have hpl : p.toNat ≤ 12 := by omega
  rw [factValue, Zig.toNat_ofNat_of_lt (natFact_lt hpl), ← hp]
  rfl

private theorem fact_mul_bound (n p : BitVec 32) (hb : n.toNat ≤ 12)
    (hp : p.toNat + 1 = n.toNat) : n.toNat * (factValue p).toNat < 2 ^ 32 := by
  rw [fact_product n p hb hp]
  exact natFact_lt hb

private theorem fact_value_step (n p r : BitVec 32) (hb : n.toNat ≤ 12)
    (hp : p.toNat + 1 = n.toNat)
    (hr : r.toNat = n.toNat * (factValue p).toNat) : r = factValue n := by
  apply BitVec.eq_of_toNat_eq
  change r.toNat = (BitVec.ofNat 32 (natFact n.toNat)).toNat
  rw [hr, fact_product n p hb hp, Zig.toNat_ofNat_of_lt (natFact_lt hb)]

/-- The bounded factorial group uses the existing checked arithmetic rules. The native
interpretation still requires STK-01; a decreasing rank alone does not provide native frames. -/
private theorem fact_group_total (n : BitVec 32) :
    FTotalTriple ⟪n.toNat ≤ 12⟫ (factCode n) (fun v => ⟪v = factValue n⟫) := by
  refine FTotalTriple.rec_group factCode (fun n => ⟪n.toNat ≤ 12⟫)
    (fun n v => ⟪v = factValue n⟫) BitVec.toNat ?_ n
  intro n smaller
  fsym
  all_goals first
    | apply fact_mul_bound <;> first | assumption | omega
    | apply fact_value_step <;> first | assumption | omega
    | simp_all [factValue, natFact]

theorem fact_total (n : BitVec 32) (h : n.toNat ≤ 12) :
    FTotalTriple emp (StateT.lift (fact n) : MemM (BitVec 32))
      (fun v => ⟪v = BitVec.ofNat 32 (natFact n.toNat)⟫) :=
  (fact_group_total n).pre (fun _ hr => ⟨h, hr⟩)

/-- The original bounded auxiliary statement, now from the full-state group contract.
`12! < 2^32`; `13!` overflows — see `fact_13_panics`. -/
theorem fact_ok_aux :
    ∀ k : Nat, ∀ n : BitVec 32, n.toNat = k → k ≤ 12 →
      fact n = pure (BitVec.ofNat 32 (natFact k)) := by
  intro k n hn hb
  simpa only [hn] using (fact_total n (by simpa only [hn] using hb)).result_eq

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

/-- The Euclidean step, phrased via core's own `gcd` recursion (on the *first* argument) and
`gcd`'s commutativity, to match `gcd`'s recursion here (on the *second* argument). -/
theorem gcd_step (a b : Nat) : Nat.gcd a b = Nat.gcd b (a % b) := by
  rw [Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm (a % b) b]

private def gcdCode (a : BitVec 32 × BitVec 32) : MemM (BitVec 32) :=
  StateT.lift (gcd a.1 a.2)

private def gcdValue (a : BitVec 32 × BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (Nat.gcd a.1.toNat a.2.toNat)

private theorem gcd_zero (a : BitVec 32 × BitVec 32) (h : a.2 = 0#32) :
    a.1 = gcdValue a := by
  simp [gcdValue, h]

private theorem gcd_rank_step (a : BitVec 32 × BitVec 32) (r : BitVec 32)
    (h : a.2 ≠ 0#32) (hr : r.toNat = a.1.toNat % a.2.toNat) :
    (a.2, r).2.toNat < a.2.toNat := by
  change r.toNat < a.2.toNat
  rw [hr]
  have hne : a.2.toNat ≠ 0 := by
    intro h0
    apply h
    apply BitVec.eq_of_toNat_eq
    simpa using h0
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero hne)

private theorem gcd_value_step (a : BitVec 32 × BitVec 32) (r : BitVec 32)
    (hr : r.toNat = a.1.toNat % a.2.toNat) :
    gcdValue (a.2, r) = gcdValue a := by
  simp only [gcdValue]
  rw [hr, ← gcd_step]

/-- The generated Euclidean algorithm terminates for every pair, including a zero divisor.
Its own branch discharges both remainder guards; the smaller-call contract uses the second
argument's natural value as its rank. Native stack use retains STK-01. -/
private theorem gcd_pair_total (a : BitVec 32 × BitVec 32) :
    FTotalTriple emp (gcdCode a) (fun v => ⟪v = gcdValue a⟫) := by
  refine FTotalTriple.rec_group gcdCode (fun _ => emp)
    (fun a v => ⟪v = gcdValue a⟫) (fun a => a.2.toNat) ?_ a
  intro a smaller
  fsym
  all_goals first
    | apply gcd_zero; assumption
    | apply gcd_rank_step <;> assumption
    | apply gcd_value_step; assumption

theorem gcd_total (a b : BitVec 32) :
    FTotalTriple emp (StateT.lift (gcd a b) : MemM (BitVec 32))
      (fun v => ⟪v = BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat)⟫) :=
  gcd_pair_total (a, b)

theorem gcd_spec (a b : BitVec 32) : gcd a b = pure (BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat)) :=
  (gcd_total a b).result_eq

/-- The original auxiliary statement, as a consequence of the all-input group contract. -/
theorem gcd_spec_aux :
    ∀ b : Nat, ∀ a bb : BitVec 32, bb.toNat = b →
      gcd a bb = pure (BitVec.ofNat 32 (Nat.gcd a.toNat b)) := by
  intro b a bb hbb
  simpa only [hbb] using gcd_spec a bb

/-! ## Non-vacuity witnesses -/

nonvacuity_witness fact_ok := ⟨5, by decide, trivial⟩
nonvacuity_witness fact_ok_aux := ⟨5, 5, rfl, by decide, trivial⟩
nonvacuity_witness gcd_spec_aux := ⟨6, 4, 6, rfl, trivial⟩
