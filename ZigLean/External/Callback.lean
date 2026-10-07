import ZigLean.External

/-! # Callback and function-pointer contracts (E02)

A callback is the model `Ptr × Args → MemM Result`. Its first component is the context pointer
captured by the caller, and is always passed explicitly. A `CallbackContract` reuses the
external `Contract` over `(context, args)` and adds the following:

* a fixed footprint. The callback writes the context block and, only when it may re-enter its
  caller, the caller-owned blocks listed in `reentry`. It reads the `reads` blocks.
* a reentrancy flag. A `forbidden` callback lists no `reentry` blocks.
* a cancellation rule. `stop` marks the results that ask the caller to stop. A `never`
  callback returns no such result.
* ownership. The context is borrowed: a call never ends the lifetime of the context block.

Clients reason from `CallbackContract.Holds` alone, so the callback body need not be translated.
A call through a pointer that has neither a known target nor a contract is `dispatch []`: the
`throw .illegal` fallback of the emitted indirect call. It never succeeds, so no effects,
including empty ones, follow for it. -/
namespace Zig.External

inductive Reentrancy where
  | forbidden | allowed
  deriving BEq, DecidableEq, Repr

inductive Cancellation where
  | never | byResult
  deriving BEq, DecidableEq, Repr

/-- The pointer designates a live block of `m`. -/
def Live (m : Mem) (p : Ptr) : Prop :=
  ∃ b blk, p.block = some b ∧ m.blocks[b]? = some blk ∧ blk.live = true

structure CallbackContract (Args Result : Type) where
  /-- Pre/post/frame/access/failure/divergence over the context pointer and the arguments. -/
  contract : Contract (Ptr × Args) Result
  termination : Termination
  errors : List Error
  effects : Effects
  /-- Blocks other than the context that a call may read, but not write. -/
  reads : Ptr × Args → List (Option BlockId)
  reentrancy : Reentrancy
  /-- Caller-owned blocks that a re-entrant call may write. -/
  reentry : Ptr × Args → List (Option BlockId)
  cancellation : Cancellation
  /-- A result that asks the caller to stop, for example `false` or a returned Zig error. -/
  stop : Result → Bool

/-- An external contract read through an argument adapter, for example a callback that
forwards its context and argument to a contracted external function. -/
def Contract.comap {Args Args' Result : Type} (c : Contract Args Result) (g : Args' → Args) :
    Contract Args' Result where
  pre := fun a => c.pre (g a)
  post := fun a => c.post (g a)
  frame := fun a => c.frame (g a)
  access := fun a => c.access (g a)
  failure := fun a => c.failure (g a)
  divergence := fun a => c.divergence (g a)

theorem Contract.Holds.comap {Args Args' Result : Type} {c : Contract Args Result}
    {termination : Termination} {errors : List Error} {effects : Effects}
    {implementation : Args → MemM Result}
    (h : c.Holds termination errors effects implementation) (g : Args' → Args) :
    (c.comap g).Holds termination errors effects (implementation ∘ g) :=
  fun a before pre => h (g a) before pre

namespace CallbackContract

variable {Args Result : Type}

/-- The callback writes its context block and its re-entry blocks; nothing else. -/
def footprint (cc : CallbackContract Args Result) : Footprint (Ptr × Args) where
  reads := cc.reads
  writes := fun a => a.1.block :: cc.reentry a

/-- The implementation-independent rules of a callback contract. -/
structure WellFormed (cc : CallbackContract Args Result) : Prop where
  reentrancy : cc.reentrancy = .forbidden → ∀ a, cc.reentry a = []
  cancellation : cc.cancellation = .never →
    ∀ a before r after, cc.contract.pre a before → cc.contract.post a before r after →
      cc.stop r = false
  borrowed : ∀ a before after, cc.contract.pre a before → cc.contract.frame a before after →
    Live before a.1 → Live after a.1
  respects : cc.contract.Respects cc.footprint

/-- An implementation satisfies the callback contract. -/
def Holds (cc : CallbackContract Args Result) (impl : Ptr × Args → MemM Result) : Prop :=
  cc.WellFormed ∧ cc.contract.Holds cc.termination cc.errors cc.effects impl

variable {cc : CallbackContract Args Result} {impl : Ptr × Args → MemM Result}
  {ctx : Ptr} {args : Args} {before after : Mem} {r : Result}

/-- The client rule for one call: the postcondition holds, a live context stays live, and every
block outside the context and the re-entry blocks is unchanged. -/
theorem call (h : cc.Holds impl) (pre : cc.contract.pre (ctx, args) before)
    (run : impl (ctx, args) before = some (.ok (r, after))) :
    cc.contract.post (ctx, args) before r after ∧ (Live before ctx → Live after ctx) ∧
      ∀ b, some b ≠ ctx.block → some b ∉ cc.reentry (ctx, args) →
        after.blocks[b]? = before.blocks[b]? := by
  have hh := h.2 _ before pre
  rw [run] at hh
  refine ⟨hh.1, h.1.borrowed _ before after pre hh.2.1, fun b hctx hre => ?_⟩
  apply h.1.respects.2 _ before after pre hh.2.1 b
  simp only [footprint, List.mem_cons, not_or]
  exact ⟨hctx, hre⟩

/-- A callback that may not re-enter its caller writes only its context block. -/
theorem call_forbidden (h : cc.Holds impl) (forbidden : cc.reentrancy = .forbidden)
    (pre : cc.contract.pre (ctx, args) before)
    (run : impl (ctx, args) before = some (.ok (r, after))) {b : BlockId}
    (outside : some b ≠ ctx.block) : after.blocks[b]? = before.blocks[b]? :=
  (call h pre run).2.2 b outside (by simp [h.1.reentrancy forbidden])

/-- A callback that never cancels returns no stop result. -/
theorem call_continues (h : cc.Holds impl) (never : cc.cancellation = .never)
    (pre : cc.contract.pre (ctx, args) before)
    (run : impl (ctx, args) before = some (.ok (r, after))) : cc.stop r = false :=
  h.1.cancellation never _ before r after pre (call h pre run).1

end CallbackContract

/-! ## Calls through a function pointer -/

/-- The emitted indirect call: each known target's block is compared with the pointer, in
order, and any other pointer throws `.illegal`. -/
def dispatch {Args Result : Type} : List (Ptr × (Args → MemM Result)) → Ptr → Args → MemM Result
  | [], _, _ => throw .illegal
  | (q, f) :: rest, p, a => if p = q then f a else dispatch rest p a

/-- A successful indirect call ran a known target. Without such a target the call has no
success, so no effects are assumed for it. -/
theorem dispatch_ok {Args Result : Type} {targets : List (Ptr × (Args → MemM Result))}
    {p : Ptr} {a : Args} {m m' : Mem} {r : Result}
    (run : dispatch targets p a m = some (.ok (r, m'))) :
    ∃ f, (p, f) ∈ targets ∧ f a m = some (.ok (r, m')) := by
  induction targets with
  | nil => cases run
  | cons t rest ih =>
    obtain ⟨q, f⟩ := t
    by_cases hp : p = q
    · subst hp
      simp only [dispatch, ↓reduceIte] at run
      exact ⟨f, List.mem_cons_self .., run⟩
    · simp only [dispatch, hp, ↓reduceIte] at run
      obtain ⟨g, mem, hg⟩ := ih run
      exact ⟨g, List.mem_cons_of_mem _ mem, hg⟩

/-- An unknown callback, with no target and no contract, has no successful call. -/
theorem dispatch_unknown {Args Result : Type} (p : Ptr) (a : Args) (m : Mem) :
    dispatch ([] : List (Ptr × (Args → MemM Result))) p a m = some (.error .illegal) := rfl

end Zig.External
