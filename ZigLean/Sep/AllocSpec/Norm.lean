import ZigLean.Sep.Total

/-!
# Normalizing generated code to `MemM` programs

A generated function that uses memory runs its body in `MM σ ε` (its locals over `MemM`) and
returns through `.run'` and a `match` on the exit. The lemmas here push `StateT.run` through
`callM`/`callR`, lifts, `if`, `throw`, `get` and `modify`, so that `simp only [norm lemmas,
bind_assoc, pure_bind, …]` turns a generated body into the plain `MemM` program it denotes
(`alloc_norm`-style equalities in `tests/roadmap/alloc-fba`). Together with the facts about the
pure helpers of `std.mem` (`ctz_twoPow`), this is how a generated `std.mem.Allocator` wrapper is
shown to equal its `Wrap.*` step semantics (`ZigLean/Sep/AllocSpec/Wrappers.lean`).

Proof-only: not reachable from `ZigLean.lean`.
-/

namespace Zig

namespace Norm

variable {σ α β : Type}

theorem run_callM (x : MemM α) (s : σ) : (callM x : MM σ α).run s = x >>= fun a => pure (a, s) :=
  rfl

theorem run_callR (x : Result α) (s : σ) :
    (callR x : MM σ α).run s = (StateT.lift x : MemM α) >>= fun a => pure (a, s) := rfl

theorem run_liftM (x : MemM α) (s : σ) : (liftM x : MM σ α).run s = x >>= fun a => pure (a, s) :=
  rfl

theorem run_liftR (x : Result α) (s : σ) :
    (liftM x : MM σ α).run s = (StateT.lift x : MemM α) >>= fun a => pure (a, s) := rfl

theorem run_ite {c : Prop} [Decidable c] (x y : MM σ α) (s : σ) :
    (if c then x else y).run s = if c then x.run s else y.run s := by split <;> rfl

theorem ite_bind {m : Type → Type} [Monad m] {c : Prop} [Decidable c] (x y : m α)
    (f : α → m β) : ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl

theorem run_throw (e : Error) (s : σ) : (throw e : MM σ α).run s = throw e := rfl

theorem throw_bind (e : Error) (f : α → MemM β) : (throw e : MemM α) >>= f = throw e := rfl

theorem lift_pure (a : α) : (StateT.lift (pure a : Result α) : MemM α) = pure a := rfl

theorem lift_throw (e : Error) : (StateT.lift (throw e : Result α) : MemM α) = throw e := rfl

theorem run_get (s : σ) : (get : MM σ σ).run s = pure (s, s) := rfl

theorem run_modify (f : σ → σ) (s : σ) : (modify f : MM σ Unit).run s = pure ((), f s) := rfl

theorem elim_bind {m : Type → Type} [Monad m] [LawfulMonad m] (o : Option α) (a : m β)
    (f : α → m β) {γ : Type} (k : β → m γ) :
    (o.elim a f >>= k) = o.elim (a >>= k) (fun x => f x >>= k) := by
  cases o <;> rfl

/-- A generated `if o.isSome then … optPayload o … else …` is `Option.elim`. -/
theorem isSome_ite (o : Option α) (f : α → MemM β) (g : MemM β) :
    (if o.isSome = true then (StateT.lift (optPayload o) : MemM α) >>= f else g) = o.elim g f := by
  cases o <;> rfl

theorem sub_zero (x : BitVec 64) : Zig.sub false x 0 = pure x := by
  simp [Zig.sub, BitVec.usubOverflow]

theorem add_zero_ptr (p : Ptr) : p.add 0 = p := by simp [Ptr.add]

theorem elem_zero (p : Ptr) (size : Nat) : p.elem size 0 = p := by simp [Ptr.elem, Ptr.add]

theorem mulWithOverflow_one (x : BitVec 64) :
    Zig.mulWithOverflow false (1 : BitVec 64) x = (x, 0) := by
  simp [Zig.mulWithOverflow, BitVec.umulOverflow, x.isLt]

theorem beq_true_iff {α : Type} [BEq α] [LawfulBEq α] (a b : α) : ((a == b) = true) = (a = b) := by
  simp

end Norm

/-- Normalize a generated function that uses memory to its `MemM` program. -/
macro "gen_norm" : tactic => `(tactic| (
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, Norm.run_callM, Norm.run_callR,
    Norm.run_liftM, Norm.run_liftR, Norm.run_ite, Norm.ite_bind, Norm.run_throw,
    Norm.throw_bind, Norm.lift_pure, Norm.lift_throw, Norm.sub_zero, Norm.elem_zero,
    Norm.run_get, Norm.run_modify, Norm.add_zero_ptr,
    bind_assoc, pure_bind, map_pure, bind_map_left, map_bind, Norm.beq_true_iff, bind_pure_unit,
    Zig.isNonErr, Zig.isErr, Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true]
  try simp only [Norm.isSome_ite, Norm.elim_bind, bind_assoc, pure_bind, Norm.ite_bind,
    bind_pure_unit]))

/-- `@ctz` of a power of two below `2 ^ 64`: the exponent. (`decide` cannot evaluate `ctz` on a
64-bit literal: `clzAuxRec` recurses on the bit index.) -/
theorem ctz_twoPow {k : Nat} (hk : k < 64) :
    (BitVec.ofNat 64 (2 ^ k)).ctz = BitVec.ofNat 64 k := by
  have hx : BitVec.ofNat 64 (2 ^ k) ≠ 0#64 := by
    intro h
    have h2 : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2] at this
    exact absurd this (Nat.ne_of_gt (Nat.two_pow_pos k))
  have hb := BitVec.getLsbD_true_ctz_of_ne_zero hx
  simp only [BitVec.getLsbD_ofNat, Nat.testBit_two_pow] at hb
  apply BitVec.eq_of_toNat_eq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
  exact hb.2.symm

end Zig
