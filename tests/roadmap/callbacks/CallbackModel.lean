import ZigLean.External.Callback

/-! # The foreign callback `ext_visit` (E02)

`callbacks.zig` declares `extern fn ext_visit(ctx: *u32, x: u32) callconv(.c) bool` and takes
its address (`&ext_visit`, the vtable `ext_ops`). Its body is outside the program, so
`registry-<version>.json` binds the symbol `extern:ext_visit` to this module: an opaque
implementation with the callback contract `visitCallback` (`trust: "assumed"`, premise EXT-03
for the symbol, EXT-02 for the assumed evidence). The emitted indirect call dispatches a
pointer to `ext_visit`'s function block to that model (`Emit.lean`, L11 table).

`visitCallback` is a non-re-entrant, never-cancelling callback that borrows its context: a call
that returns gives `true`, keeps the context live, changes no block other than the context's and
records accesses to the context's block only. It may fail with any error or not return
(partial): the caller propagates either.
`visit_satisfiable` is a kernel-checked witness that the contract has an implementation, so
the assumed evidence is not vacuous. -/
namespace CallbackModel
open Zig Zig.External

/-- Every `Zig.Error`: the callback may fail in any way, and the caller propagates it. -/
def allErrors : List Error :=
  [.overflow, .outOfBounds, .divByZero, .unreachable, .panic, .unspecified, .illegal, .deadlock,
   .unsupportedTimer, .trap, .stackOverflow]

theorem mem_allErrors (e : Error) : e ∈ allErrors := by cases e <;> simp [allErrors]

/-- The foreign implementation: unknown to the model. -/
opaque visit : Ptr × BitVec 32 → MemM Bool := fun _ => pure true

def visitCallback : CallbackContract (BitVec 32) Bool where
  contract := {
    pre := fun _ _ => True
    post := fun _ _ r _ => r = true
    frame := fun a before after =>
      (∀ b, some b ≠ a.1.block → after.blocks[b]? = before.blocks[b]?) ∧
        (Live before a.1 → Live after a.1)
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

/-- The registry's `contract`. -/
def contract : Contract (Ptr × BitVec 32) Bool := visitCallback.contract

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

/-- A witness: the effect-free callback that always continues satisfies the contract. -/
theorem visit_satisfiable :
    visitCallback.Holds (fun _ => (pure true : MemM Bool)) := by
  refine ⟨wellFormed, fun a before _ => ?_⟩
  refine ⟨rfl, ⟨fun _ _ => rfl, id⟩, ⟨#[], by simp, by simp⟩, fun _ => rfl⟩

end CallbackModel
