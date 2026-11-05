import ZigLean.Sep.Full.AutoPrim

/-!
# `Result` contracts as step rules of `fsym`

A `Result` operation inside generated memory code is a command `StateT.lift x`, executed by a
step rule of the symbolic executor `fsym` (`docs/proof-automation.md`). `result_step` makes a
`Result` contract (`pre → ∃ v, x = pure v ∧ post v`) such a rule: its precondition is the rule's
side condition, its summary a fact of the result. This file registers the primitive contracts
that the rule library of `ZigLean/Sep/Full/AutoRules.lean` lacks; a proved contract of a
generated function is given to the walk the same way (`docs/vcs.md`). The converse, a `Result`
contract from the total triple of the lifted program, is `FTotalTriple.result_spec`
(`ZigLean/Sep/Full/Init.lean`).

Every rule is an ordinary theorem; nothing here is trusted.
-/

namespace Zig.VC

open Full

/-- A `Result` contract as a step rule: the frame `P` is kept, the summary is a fact. -/
theorem result_step {α : Type} {P : FAssn} {x : Result α} {pre : Prop} {post : α → Prop}
    (contract : pre → ∃ v, x = pure v ∧ post v) (h : pre) :
    FTotalTriple P (StateT.lift x : MemM α) (fun v => ⟪post v⟫ ⋆ P) := by
  obtain ⟨v, rfl, hv⟩ := contract h
  exact (FTotalTriple.ret (Q := fun r => ⟪post r⟫ ⋆ P) v).pre fun _ hp => Full.sep_lift.mpr ⟨hv, hp⟩

/-! ## Primitive `Result` contracts

Each precondition is exactly the condition under which the operation returns. -/

namespace Prim

variable {n : Nat} {P : FAssn}

theorem mul_unsigned (a b : BitVec n) :
    a.toNat * b.toNat < 2 ^ n → ∃ v, Zig.mul false a b = pure v ∧ v = a * b := fun h =>
  ⟨a * b, by simp [Zig.mul_unsigned, Nat.not_le.mpr h], rfl⟩

theorem add_signed (a b : BitVec n) :
    a.saddOverflow b = false → ∃ v, Zig.add true a b = pure v ∧ v = a + b := fun h =>
  ⟨a + b, by simp [Zig.add, h], rfl⟩

theorem sub_signed (a b : BitVec n) :
    a.ssubOverflow b = false → ∃ v, Zig.sub true a b = pure v ∧ v = a - b := fun h =>
  ⟨a - b, by simp [Zig.sub, h], rfl⟩

theorem mul_signed (a b : BitVec n) :
    a.smulOverflow b = false → ∃ v, Zig.mul true a b = pure v ∧ v = a * b := fun h =>
  ⟨a * b, by simp [Zig.mul, h], rfl⟩

/-- The range condition of `@intCast`, as in its definition. -/
theorem intCast_range (s₁ s₂ : Bool) (m : Nat) (a : BitVec n) :
    (Zig.intLo s₂ m ≤ Zig.val s₁ a ∧ Zig.val s₁ a ≤ Zig.intHi s₂ m) →
    ∃ v, Zig.intCast s₁ s₂ m a = pure v ∧ v = BitVec.ofInt m (Zig.val s₁ a) := fun h =>
  ⟨_, by simp only [Zig.intCast, h, and_self, ↓reduceIte], rfl⟩

theorem index {α : Type} (a : Array α) (i : usize) :
    i.toNat < a.size → ∃ v, Zig.index a i = pure v ∧ ∃ h : i.toNat < a.size, v = a[i.toNat] :=
  fun h => ⟨a[i.toNat], Zig.index_lt a i h, h, rfl⟩

theorem unwrapPayload {α : Type} (e : Except ErrName α) :
    Zig.isNonErr e = true → ∃ v, Zig.unwrapPayload e = pure v ∧ e = .ok v := by
  intro h
  cases e with
  | error => cases h
  | ok v => exact ⟨v, rfl, rfl⟩

theorem unwrapErr {α : Type} (e : Except ErrName α) :
    Zig.isErr e = true → ∃ v, Zig.unwrapErr e = pure v ∧ e = .error v := by
  intro h
  cases e with
  | error v => exact ⟨v, rfl, rfl⟩
  | ok => cases h

/-! ## Their step rules -/

@[fsym] theorem mul_unsigned_step (a b : BitVec n) (h : a.toNat * b.toNat < 2 ^ n) :
    FTotalTriple P (StateT.lift (Zig.mul false a b) : MemM (BitVec n)) (fun v => ⟪v = a * b⟫ ⋆ P) :=
  result_step (mul_unsigned a b) h

@[fsym] theorem add_signed_step (a b : BitVec n) (h : a.saddOverflow b = false) :
    FTotalTriple P (StateT.lift (Zig.add true a b) : MemM (BitVec n)) (fun v => ⟪v = a + b⟫ ⋆ P) :=
  result_step (add_signed a b) h

@[fsym] theorem sub_signed_step (a b : BitVec n) (h : a.ssubOverflow b = false) :
    FTotalTriple P (StateT.lift (Zig.sub true a b) : MemM (BitVec n)) (fun v => ⟪v = a - b⟫ ⋆ P) :=
  result_step (sub_signed a b) h

@[fsym] theorem mul_signed_step (a b : BitVec n) (h : a.smulOverflow b = false) :
    FTotalTriple P (StateT.lift (Zig.mul true a b) : MemM (BitVec n)) (fun v => ⟪v = a * b⟫ ⋆ P) :=
  result_step (mul_signed a b) h

/-- `@intCast` in range (`Zig.Full.Auto.intCast_widen_step` covers unsigned widening). -/
@[fsym] theorem intCast_range_step (s₁ s₂ : Bool) (m : Nat) (a : BitVec n)
    (h : Zig.intLo s₂ m ≤ Zig.val s₁ a ∧ Zig.val s₁ a ≤ Zig.intHi s₂ m) :
    FTotalTriple P (StateT.lift (Zig.intCast s₁ s₂ m a) : MemM (BitVec m))
      (fun v => ⟪v = BitVec.ofInt m (Zig.val s₁ a)⟫ ⋆ P) :=
  result_step (intCast_range s₁ s₂ m a) h

-- The integer range bounds of a known signedness and width, for the side goals of
-- `intCast_range_step` (and `clamp`).
attribute [fsym_arith] Zig.intLo_unsigned Zig.intHi_unsigned Zig.intLo_signed_succ
  Zig.intHi_signed_succ Zig.intLo_zero Zig.intHi_zero

@[fsym] theorem index_step {α : Type} (a : Array α) (i : usize) (h : i.toNat < a.size) :
    FTotalTriple P (StateT.lift (Zig.index a i) : MemM α)
      (fun v => ⟪∃ h : i.toNat < a.size, v = a[i.toNat]⟫ ⋆ P) :=
  result_step (index a i) h

@[fsym] theorem unwrapPayload_step {α : Type} (e : Except ErrName α) (h : Zig.isNonErr e = true) :
    FTotalTriple P (StateT.lift (Zig.unwrapPayload e) : MemM α) (fun v => ⟪e = .ok v⟫ ⋆ P) :=
  result_step (unwrapPayload e) h

@[fsym] theorem unwrapErr_step {α : Type} (e : Except ErrName α) (h : Zig.isErr e = true) :
    FTotalTriple P (StateT.lift (Zig.unwrapErr e) : MemM ErrName) (fun v => ⟪e = .error v⟫ ⋆ P) :=
  result_step (unwrapErr e) h

end Prim

end Zig.VC
