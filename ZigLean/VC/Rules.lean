import ZigLean.VC.Mem
import ZigLean.VC.ContractAttr

/-!
# Rules for automatic VC extraction

This file holds the kernel-checked pieces that `ZigLean.VC.Extract` combines:

* normalization lemmas that remove the generated `StateT` locals/exit plumbing;
* primitive `Result` contracts tagged `@[vc_contract]`, so an operation without an AST
  constructor becomes a checked modular call whose precondition is a safety obligation;
* introduction rules, one per AST constructor, that split a generated VC into separate goals;
* `ensures`, which separates a memory postcondition into a functional result and a heap effect.

Every rule is an ordinary theorem; nothing here is trusted by the extractor.
-/

namespace Zig.VC

open Assn

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

/-! ## Pointer equality -/

/-- `==` on pointers compares addresses (`ptrEqAddr`, MM-4). For two pointers without a block
(from `@ptrFromInt`, or null) the addresses are the offsets; nothing is read or owned. -/
@[vc_contract] theorem ptrEqAddr_raw (p q : Ptr) :
    Triple ⌜p.block = none ∧ q.block = none⌝ (ptrEqAddr p q)
      (fun r => ⌜r = decide (p.off = q.off)⌝) :=
  Triple.of_run fun m _ hF _ hm hp hst => by
    obtain ⟨⟨hpb, hqb⟩, rfl⟩ := hp
    refine ⟨decide (p.off = q.off), m, Heap.empty, ?_, (Heap.disjoint_empty hF).symm,
      by rw [hm, Heap.empty_union], ⟨rfl, rfl⟩, hst⟩
    simp [ptrEqAddr, ptrAddr, hpb, hqb, zig_unfold]

/-! ## Pointer formation (MM-3) -/

/-- Owned bytes of `p` reaching `k` bytes past it (one past the end included): the block's bytes
`bs` with alignment `A`, size `S` and kind `K` (`bytesAt`). -/
def ownsOffset (p : Ptr) (k : Int) : Assn :=
  Assn.ex fun (x : Nat × Nat × BlockKind × Array Byte) =>
    ⌜0 ≤ k ∧ k ≤ x.2.2.2.size ∧ 0 < x.2.2.2.size⌝ ∗ bytesAt p x.1 x.2.1 x.2.2.1 x.2.2.2

/-- `&p.f`, `p + k` for a byte offset (`struct_field_ptr`, `ptr_add`): checked pointer
formation (`ptrProject`, `getelementptr inbounds`) needs base and result in bounds of the same
block. Owning `p`'s bytes up to `k` (`ownsOffset`) gives both; nothing is read or changed. -/
@[vc_contract] theorem ptrProject_bytes (p : Ptr) (k : Int) :
    Triple (ownsOffset p k) (ptrProject p (·.add k)) (fun q => ⌜q = p.add k⌝ ∗ ownsOffset p k) :=
  Triple.of_run fun m hP _ hd hm hown hs => by
    obtain ⟨⟨A, S, K, bs⟩, hx⟩ := hown
    obtain ⟨⟨h0, hk, hpos⟩, hb⟩ := sep_lift.mp hx
    have hrun := bytesAt_ptrProject_run hb hm (k := k.toNat) (by omega) hpos
    simp only [Int.toNat_of_nonneg h0] at hrun
    exact ⟨_, m, hP, hrun, hd, hm, sep_lift.mpr ⟨rfl, ⟨⟨A, S, K, bs⟩, hx⟩⟩, hs⟩

/-! ## Contract postconditions -/

/-- A memory postcondition in two parts: the functional `result` and the `heap` effect.
Extraction reports them as separate obligations. -/
def ensures {α : Type} (result : α → Prop) (heap : α → Assn) : α → Assn :=
  fun value h => result value ∧ heap value h

theorem ensures_intro {α : Type} {result : α → Prop} {heap : α → Assn} {value : α} {h : Heap}
    (result_ok : result value) (heap_ok : heap value h) : ensures result heap value h :=
  ⟨result_ok, heap_ok⟩

/-! ## Entry rules -/

theorem result_intro {α : Type} {program : ResultProgram α} {action : Result α}
    {post : α → Prop} (source : program.eval = action) (generated : program.vc post) :
    ∃ value, action = pure value ∧ post value :=
  source ▸ program.sound post generated

theorem triple_intro {α : Type} {program : MemProgram α} {action : MemM α} {pre : Assn}
    {post : α → Assn} (source : program.eval = action)
    (generated : MemProgram.obligation pre program post) : Triple pre action post :=
  source ▸ MemProgram.verify generated

/-- The link theorem of an extracted `ResultProgram`: the existing soundness theorem,
transported along the kernel-checked source equality. -/
theorem ResultProgram.sound_of {α : Type} {program : ResultProgram α} {action : Result α}
    (source : program.eval = action) (post : α → Prop) (generated : program.vc post) :
    ∃ value, action = pure value ∧ post value :=
  result_intro source generated

/-- The link theorem of an extracted `MemProgram`. -/
theorem MemProgram.sound_of {α : Type} {program : MemProgram α} {action : MemM α}
    (source : program.eval = action) (post : α → Assn) :
    Triple (program.vc post) action post :=
  source ▸ program.sound post

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

/-! ## Splitting rules for `MemProgram.vc` -/

namespace MemProgram

theorem ret_intro {α : Type} {value : α} {post : α → Assn} {h : Heap} (next : post value h) :
    (MemProgram.ret value).vc post h := next

theorem load_intro {T : Type} [Enc T] {pointer : Ptr} {alignment : Nat} {post : T → Assn}
    {h : Heap} {old : T} (owned : pts pointer alignment old h) (size : 0 < Enc.size T)
    (next : post old h) : (MemProgram.load (T := T) pointer alignment).vc post h :=
  ⟨size, old, owned, next⟩

theorem load_intro_any {T : Type} [Enc T] {pointer : Ptr} {alignment : Nat} {post : T → Assn}
    {h : Heap} (size : 0 < Enc.size T) (owned : ∃ old : T, pts pointer alignment old h ∧ post old h) :
    (MemProgram.load (T := T) pointer alignment).vc post h :=
  ⟨size, owned⟩

theorem store_intro {T : Type} [Enc T] [LawfulEnc T] {pointer : Ptr} {alignment : Nat}
    {value : T} {post : Unit → Assn} {h : Heap} (size : 0 < Enc.size T)
    (owned : ∃ old : T, pts pointer alignment old h)
    (next : ∀ h', pts pointer alignment value h' → post () h') :
    (MemProgram.store pointer alignment value).vc post h :=
  ⟨size, owned, next⟩

theorem read_intro {T : Type} [Enc T] {pointer : Ptr} {alignment : Nat} {old : T}
    {post : T → Assn} {h : Heap} (size : 0 < Enc.size T) (owned : pts pointer alignment old h)
    (next : post old h) : (MemProgram.read pointer alignment old).vc post h :=
  ⟨size, owned, next⟩

theorem write_intro {T : Type} [Enc T] [LawfulEnc T] {pointer : Ptr} {alignment : Nat}
    {old value : T} {post : Unit → Assn} {h : Heap} (size : 0 < Enc.size T)
    (owned : pts pointer alignment old h)
    (next : ∀ h', pts pointer alignment value h' → post () h') :
    (MemProgram.write pointer alignment old value).vc post h :=
  ⟨size, owned, next⟩

theorem lift_intro {α : Type} {program : ResultProgram α} {post : α → Assn} {h : Heap}
    (generated : program.vc (fun value => post value h)) :
    (MemProgram.lift program).vc post h := generated

theorem call_intro {α : Type} {label : String} {action : MemM α} {pre : Assn}
    {summary : α → Assn} {checked : Triple pre action summary} {post : α → Assn} {h : Heap}
    (precondition : pre h) (next : ∀ value h', summary value h' → post value h') :
    (MemProgram.call label action pre summary checked).vc post h := ⟨precondition, next⟩

theorem bind_intro {α β : Type} {first : MemProgram α} {next : α → MemProgram β}
    {post : β → Assn} {h : Heap} (generated : first.vc (fun value => (next value).vc post) h) :
    (MemProgram.bind first next).vc post h := generated

theorem branch_intro {α : Type} {condition : Bool} {yes no : MemProgram α}
    {post : α → Assn} {h : Heap} (taken : condition = true → yes.vc post h)
    (skipped : condition = false → no.vc post h) :
    (MemProgram.branch condition yes no).vc post h := by
  cases condition with
  | false => exact skipped rfl
  | true => exact taken rfl

end MemProgram

end Zig.VC
