import ZigLean.External.Callback
import Proofs.Asm.Effects

/-! # The foreign callback `ext_visit` (E02)

`callbacks.zig` declares `extern fn ext_visit(ctx: *u32, x: u32) callconv(.c) bool` and takes
its address (`&ext_visit`, the vtable `ext_ops`). Its body is outside the program, so
`registry-<version>.json` binds the symbol `extern:ext_visit` to this module: an opaque
implementation with the contract `contract` (`trust: "assumed"`, premise EXT-03 for the symbol,
EXT-02 for the assumed evidence). The emitted indirect call dispatches a pointer to
`ext_visit`'s function block to that model (`Emit.lean`, L11 table).

Two contracts:

* `contract` (registered, assumed for `ext_visit`) is what the foreign function guarantees.
  Given a context that holds a writable `u32` (`CtxOk`), a call that returns gives `true` and
  its memory is a `u32` store to the context, up to the access log (`StoresU32`); it fails
  only with a stack overflow. Given any other context, it may fail with `.illegal` (the model
  is conservative there: native code may do anything) and changes no block but the context's.
  It may not return (partial). Every access it records is to the context's block.
* `visitCallback` is the callback contract that every target of the callback type meets, the
  unknown-address arm of the dispatch included (`.illegal`): a non-re-entrant,
  never-cancelling callback that borrows its context. A call that returns gives `true`, keeps
  the context live and changes no block other than the context's; it may fail with any error.
  `contract_weaker` derives it from `contract`.

`visit_satisfiable` is a kernel-checked witness that `contract` has an implementation, so the
assumed evidence is not vacuous. -/
namespace CallbackModel
open Zig Zig.External

/-- Every `Zig.Error`: the callback may fail in any way, and the caller propagates it. -/
def allErrors : List Error :=
  [.overflow, .outOfBounds, .divByZero, .unreachable, .panic, .unspecified, .illegal, .deadlock,
   .unsupportedTimer, .trap, .stackOverflow]

theorem mem_allErrors (e : Error) : e ∈ allErrors := by cases e <;> simp [allErrors]

/-- The registered errors of `ext_visit` (`registry-<version>.json`). -/
def errors : List Error := [.illegal, .stackOverflow]

/-- The foreign implementation: unknown to the model. -/
opaque visit : Ptr × BitVec 32 → MemM Bool := fun _ => pure true

/-- `ctx` designates a writable `u32`: a store of a `u32` there succeeds. -/
def CtxOk (ctx : Ptr) (m : Mem) : Prop :=
  ∃ m₁, (store 4 ctx (0 : BitVec 32)).run m = pure ((), m₁)

/-- `after` is a `u32` store to `ctx` from `before`, up to the access log: the same blocks and
atomic layout, and a single-threaded memory stays single-threaded. -/
def StoresU32 (ctx : Ptr) (before after : Mem) : Prop :=
  ∃ (w : BitVec 32) (m₁ : Mem), (store 4 ctx w).run before = pure ((), m₁) ∧
    after.blocks = m₁.blocks ∧ after.atomics = m₁.atomics ∧
    (before.SingleThread → after.SingleThread)

/-- The frame of every callback of the type: no block but the context's changes, and a live
context stays live. -/
def Kept (a : Ptr × BitVec 32) (before after : Mem) : Prop :=
  (∀ b, some b ≠ a.1.block → after.blocks[b]? = before.blocks[b]?) ∧
    (Live before a.1 → Live after a.1)

/-- The registry's `contract`: what the foreign `ext_visit` guarantees (module doc). -/
def contract : Contract (Ptr × BitVec 32) Bool where
  pre := fun _ _ => True
  post := fun _ _ r _ => r = true
  frame := fun a before after =>
    Kept a before after ∧ (CtxOk a.1 before → StoresU32 a.1 before after)
  access := fun a _ entry => some entry.block = a.1.block
  failure := fun a before e => e = .stackOverflow ∨ (e = .illegal ∧ ¬ CtxOk a.1 before)
  divergence := fun _ _ => True

def visitCallback : CallbackContract (BitVec 32) Bool where
  contract := {
    pre := fun _ _ => True
    post := fun _ _ r _ => r = true
    frame := Kept
    access := fun a _ entry => some entry.block = a.1.block
    failure := fun _ _ _ => True
    divergence := fun _ _ => True }
  termination := .«partial»
  errors := allErrors
  effects := .tracked
  reads := fun _ => []
  reentrancy := .forbidden
  reentry := fun _ => []
  cancellation := .never
  stop := fun r => !r

theorem wellFormed : visitCallback.WellFormed where
  reentrancy := fun _ _ => rfl
  cancellation := fun _ _ _ r _ _ post => by
    change r = true at post
    simp [visitCallback, post]
  borrowed := fun _ _ _ _ frame live => frame.2 live
  respects := by
    refine ⟨fun _ _ entry h => .inl ?_, ?_⟩
    · change some entry.block = _ at h
      simp [CallbackContract.footprint, visitCallback, h]
    intro a before after _ frame b outside
    exact frame.1 b fun h => outside (by simp [CallbackContract.footprint, h])

/-- **The registered contract gives the callback contract** (`errors ⊆ allErrors`, and its
frame and failures are stronger). -/
theorem contract_weaker {impl : Ptr × BitVec 32 → MemM Bool}
    (h : contract.Holds .«partial» errors .tracked impl) : visitCallback.Holds impl :=
  ⟨wellFormed, h.weaken (fun _ _ _ => trivial) (fun e _ => mem_allErrors e)
    (fun _ _ _ _ _ h => h) (fun _ _ _ _ h => h.1) (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)⟩

/-- A `u32` store to the context keeps every other block, keeps the context live, records one
write access to the context's block, and keeps a single-threaded memory single-threaded. -/
theorem store_effects {ctx : Ptr} {w : BitVec 32} {x : BitVec 32} {before after : Mem}
    (h : (store 4 ctx w).run before = pure ((), after)) :
    Kept (ctx, x) before after ∧
      (∃ delta : Array FootprintEntry, after.footprint = before.footprint ++ delta ∧
        ∀ entry, entry ∈ delta.toList → some entry.block = ctx.block) ∧
      (before.SingleThread → after.SingleThread) := by
  obtain ⟨b, blk, o, hacc, rfl⟩ := Asm.storeBytes_inv h
  obtain ⟨hb, hblk, hlive, -, -, -, -⟩ := access_eq (Asm.access_of_accessW hacc)
  have hlt : b < before.blocks.size := (Array.getElem?_eq_some_iff.mp hblk).1
  refine ⟨⟨fun c hc => ?_, fun _ => ?_⟩, ⟨#[⟨before.current,
    VClock.bump (before.clocks[before.current]!) before.current, b, o, (Enc.encode w).size,
    .write⟩], ?_, ?_⟩, fun hs => ?_⟩
  · have hne : b ≠ c := fun e => hc (e ▸ hb.symm)
    simp [Mem.write, Mem.recordAt, Array.getElem?_setIfInBounds_ne hne]
  · refine ⟨b, { blk with bytes := writeBytes blk.bytes o (Enc.encode w) }, hb, ?_, hlive⟩
    simp only [Mem.write, Mem.recordAt, Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt hlt
  · simp only [Mem.write, Mem.recordAt, Array.push_eq_append]
  · intro entry hentry
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
    subst hentry
    exact hb.symm
  · exact singleThread_write (singleThread_recordAt hs _ _ _ _) _ _ _ _

open Classical in
/-- An implementation of the registered contract: it stores `0` to a writable context and
returns `true`, and throws `.illegal` for any other context. -/
noncomputable def witness : Ptr × BitVec 32 → MemM Bool := fun a m =>
  if CtxOk a.1 m then (store 4 a.1 (0 : BitVec 32) *> pure true).run m
  else (throw .illegal : MemM Bool).run m

/-- The registered contract has an implementation, so the assumed evidence is not vacuous. -/
theorem visit_satisfiable : contract.Holds .«partial» errors .tracked witness := by
  intro a before _
  by_cases hc : CtxOk a.1 before
  · obtain ⟨m₁, hrun⟩ := hc
    have hw : witness a before = some (.ok (true, m₁)) := by
      have e : witness a before = (store 4 a.1 (0 : BitVec 32) *> pure true).run before :=
        ite_eq_left ⟨m₁, hrun⟩
      rw [e]
      show (store 4 a.1 (0 : BitVec 32) >>= fun _ => pure true).run before = _
      rw [StateT.run_bind, hrun]
      rfl
    obtain ⟨hk, hfp, hst⟩ := store_effects (x := a.2) hrun
    rw [hw]
    exact ⟨rfl, ⟨hk, fun _ => ⟨0, m₁, hrun, rfl, rfl, hst⟩⟩, hfp, fun h => nomatch h⟩
  · have hw : witness a before = some (.error .illegal) := ite_eq_right hc
    rw [hw]
    exact ⟨by simp [errors], .inr ⟨rfl, hc⟩⟩

end CallbackModel
