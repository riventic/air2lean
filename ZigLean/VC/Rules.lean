import ZigLean.VC.Result
import ZigLean.VC.ContractAttr
import ZigLean.Sep.Full.AutoPrim

/-!
# Rules for automatic VC extraction

This file holds the kernel-checked pieces that `ZigLean.VC.Extract` combines:

* normalization lemmas that remove the generated `StateT` locals/exit plumbing;
* primitive `Result` contracts tagged `@[vc_contract]`, so an operation without an AST
  constructor becomes a checked modular call whose precondition is a safety obligation;
* `result_step`, which makes a `Result` contract a step rule of the symbolic executor `fsym`
  (`docs/proof-automation.md`), and from it the `@[fsym]` rules of the primitive contracts that
  the rule library lacks: memory VCs are `fsym`'s walk (`ZigLean/VC/Extract.lean`);
* introduction rules, one per `ResultProgram` constructor, that split a generated VC into
  separate goals;
* `ensures`, which separates a postcondition into a functional result and a heap effect.

Every rule is an ordinary theorem; nothing here is trusted by the extractor.
-/

namespace Zig.VC

open Full

/-! ## Normalization of generated bodies -/

theorem ite_bind {m : Type → Type} [Monad m] {α β : Type} (c : Prop) [Decidable c]
    (x y : m α) (k : α → m β) :
    (if c then x else y) >>= k = if c then x >>= k else y >>= k := by
  split <;> rfl

theorem map_ite {m : Type → Type} [Functor m] {α β : Type} (c : Prop) [Decidable c]
    (x y : m α) (f : α → β) :
    f <$> (if c then x else y) = if c then f <$> x else f <$> y := by
  split <;> rfl

theorem run_ite {σ : Type} {m : Type → Type} [Monad m] {α : Type} (c : Prop) [Decidable c]
    (x y : StateT σ m α) (s : σ) :
    (if c then x else y).run s = if c then x.run s else y.run s := by
  split <;> rfl

theorem run_throw_result {σ α : Type} (e : Error) (s : σ) :
    (throw e : StateT σ Result α).run s = (throw e : Result (α × σ)) := rfl

theorem run_throw_mem {σ α : Type} (e : Error) (s : σ) :
    (throw e : StateT σ MemM α).run s = (throw e : MemM (α × σ)) := rfl

/-! ## Primitive `Result` contracts

Each precondition is exactly the condition under which the operation returns. -/

namespace Prim

variable {n : Nat}

@[vc_contract] theorem sub_unsigned (a b : BitVec n) :
    b.toNat ≤ a.toNat → ∃ v, Zig.sub false a b = pure v ∧ v = a - b := fun h =>
  ⟨a - b, by simp [Zig.sub_unsigned, Nat.not_lt.mpr h], rfl⟩

@[vc_contract] theorem mul_unsigned (a b : BitVec n) :
    a.toNat * b.toNat < 2 ^ n → ∃ v, Zig.mul false a b = pure v ∧ v = a * b := fun h =>
  ⟨a * b, by simp [Zig.mul_unsigned, Nat.not_le.mpr h], rfl⟩

@[vc_contract] theorem add_signed (a b : BitVec n) :
    a.saddOverflow b = false → ∃ v, Zig.add true a b = pure v ∧ v = a + b := fun h =>
  ⟨a + b, by simp [Zig.add, h], rfl⟩

@[vc_contract] theorem sub_signed (a b : BitVec n) :
    a.ssubOverflow b = false → ∃ v, Zig.sub true a b = pure v ∧ v = a - b := fun h =>
  ⟨a - b, by simp [Zig.sub, h], rfl⟩

@[vc_contract] theorem mul_signed (a b : BitVec n) :
    a.smulOverflow b = false → ∃ v, Zig.mul true a b = pure v ∧ v = a * b := fun h =>
  ⟨a * b, by simp [Zig.mul, h], rfl⟩

@[vc_contract] theorem divTrunc_unsigned (a b : BitVec n) :
    b ≠ 0 → ∃ v, Zig.divTrunc false a b = pure v ∧ v = a.udiv b := fun h =>
  ⟨a.udiv b, by simp only [Zig.divTrunc, h, ↓reduceIte, Bool.false_eq_true], rfl⟩

/-- The range condition of `@intCast`, as in its definition. -/
@[vc_contract] theorem intCast_range (s₁ s₂ : Bool) (m : Nat) (a : BitVec n) :
    ((if s₂ then -(2 ^ (m - 1)) else 0 : Int) ≤ Zig.val s₁ a ∧
      Zig.val s₁ a ≤ (if s₂ then 2 ^ (m - 1) - 1 else 2 ^ m - 1 : Int)) →
    ∃ v, Zig.intCast s₁ s₂ m a = pure v ∧ v = BitVec.ofInt m (Zig.val s₁ a) := fun h =>
  ⟨_, by simp only [Zig.intCast, h, and_self, ↓reduceIte], rfl⟩

@[vc_contract] theorem index {α : Type} (a : Array α) (i : usize) :
    i.toNat < a.size → ∃ v, Zig.index a i = pure v ∧ ∃ h : i.toNat < a.size, v = a[i.toNat] :=
  fun h => ⟨a[i.toNat], Zig.index_lt a i h, h, rfl⟩

@[vc_contract] theorem optPayload {α : Type} (o : Option α) :
    o.isSome = true → ∃ v, Zig.optPayload o = pure v ∧ o = some v := by
  intro h
  cases o with
  | none => cases h
  | some v => exact ⟨v, rfl, rfl⟩

@[vc_contract] theorem unwrapPayload {α : Type} (e : Except ErrName α) :
    Zig.isNonErr e = true → ∃ v, Zig.unwrapPayload e = pure v ∧ e = .ok v := by
  intro h
  cases e with
  | error => cases h
  | ok v => exact ⟨v, rfl, rfl⟩

@[vc_contract] theorem unwrapErr {α : Type} (e : Except ErrName α) :
    Zig.isErr e = true → ∃ v, Zig.unwrapErr e = pure v ∧ e = .error v := by
  intro h
  cases e with
  | error v => exact ⟨v, rfl, rfl⟩
  | ok => cases h

end Prim

/-! ## Contracts as step rules of `fsym`

Memory VCs are the walk of the symbolic executor: a `Result` operation inside generated memory
code is a command `StateT.lift x`, executed by a step rule. `result_step` makes a `Result`
contract (`pre → ∃ v, x = pure v ∧ post v`) such a rule: its precondition is the rule's side
condition, its summary a fact of the result. The primitive contracts that the rule library of
`ZigLean/Sep/Full/AutoRules.lean` lacks are registered this way; `vc_gen` passes the other
`@[vc_contract]` contracts to the walk. -/

/-- A `Result` contract as a step rule: the frame `P` is kept, the summary is a fact. -/
theorem result_step {α : Type} {P : FAssn} {x : Result α} {pre : Prop} {post : α → Prop}
    (contract : pre → ∃ v, x = pure v ∧ post v) (h : pre) :
    FTotalTriple P (StateT.lift x : MemM α) (fun v => ⟪post v⟫ ⋆ P) := by
  obtain ⟨v, rfl, hv⟩ := contract h
  exact (FTotalTriple.ret (Q := fun r => ⟪post r⟫ ⋆ P) v).pre fun _ hp => Full.sep_lift.mpr ⟨hv, hp⟩

namespace Prim

variable {n : Nat} {P : FAssn}

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
    (h : (if s₂ then -(2 ^ (m - 1)) else 0 : Int) ≤ Zig.val s₁ a ∧
      Zig.val s₁ a ≤ (if s₂ then 2 ^ (m - 1) - 1 else 2 ^ m - 1 : Int)) :
    FTotalTriple P (StateT.lift (Zig.intCast s₁ s₂ m a) : MemM (BitVec m))
      (fun v => ⟪v = BitVec.ofInt m (Zig.val s₁ a)⟫ ⋆ P) :=
  result_step (intCast_range s₁ s₂ m a) h

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

/-! ## Contract postconditions -/

/-- A postcondition in two parts: the functional `result` (a fact) and the `heap` effect. `vc_gen`
unfolds it, so the result is a separate obligation from the heap's. -/
def ensures {α : Type} (result : α → Prop) (heap : α → FAssn) : α → FAssn :=
  fun value => ⟪result value⟫ ⋆ heap value

/-! ## Entry rules -/

theorem result_intro {α : Type} {program : ResultProgram α} {action : Result α}
    {post : α → Prop} (source : program.eval = action) (generated : program.vc post) :
    ∃ value, action = pure value ∧ post value :=
  source ▸ program.sound post generated

/-- The link theorem of an extracted `ResultProgram`: the existing soundness theorem,
transported along the kernel-checked source equality. -/
theorem ResultProgram.sound_of {α : Type} {program : ResultProgram α} {action : Result α}
    (source : program.eval = action) (post : α → Prop) (generated : program.vc post) :
    ∃ value, action = pure value ∧ post value :=
  result_intro source generated

/-! ## Splitting rules for `ResultProgram.vc` -/

namespace ResultProgram

theorem ret_intro {α : Type} {value : α} {post : α → Prop} (next : post value) :
    (ResultProgram.ret value).vc post := next

theorem add_intro {n : Nat} {left right : BitVec n} {post : BitVec n → Prop}
    (overflow : left.toNat + right.toNat < 2 ^ n) (next : post (left + right)) :
    (ResultProgram.add left right).vc post := ⟨overflow, next⟩

theorem widen_intro {n : Nat} {value : BitVec n} {width : Nat} {post : BitVec width → Prop}
    (widening : n ≤ width) (next : post (value.setWidth width)) :
    (ResultProgram.widen value width).vc post := ⟨widening, next⟩

theorem guard_intro {condition : Bool} {post : Unit → Prop}
    (guard : condition = true) (next : post ()) : (ResultProgram.guard condition).vc post :=
  ⟨guard, next⟩

theorem panic_intro {α : Type} {error : Error} {post : α → Prop}
    (unreachable : False) : (ResultProgram.panic error).vc post := unreachable

theorem call_intro {α : Type} {label : String} {action : Result α} {pre : Prop}
    {summary : α → Prop} {checked : pre → ∃ value, action = pure value ∧ summary value}
    {post : α → Prop} (precondition : pre) (next : ∀ value, summary value → post value) :
    (ResultProgram.call label action pre summary checked).vc post := ⟨precondition, next⟩

theorem bind_intro {α β : Type} {first : ResultProgram α} {next : α → ResultProgram β}
    {post : β → Prop} (generated : first.vc (fun value => (next value).vc post)) :
    (ResultProgram.bind first next).vc post := generated

theorem branch_intro {α : Type} {condition : Bool} {yes no : ResultProgram α}
    {post : α → Prop} (taken : condition = true → yes.vc post)
    (skipped : condition = false → no.vc post) :
    (ResultProgram.branch condition yes no).vc post := by
  cases condition with
  | false => exact skipped rfl
  | true => exact taken rfl

end ResultProgram

end Zig.VC
