import ZigLean.Mem.Basic

/-! Typed contracts for selected sequential external models. Safety errors, returned Zig
errors, and divergence are distinct. StateT erases memory on failure, so failure predicates
cannot assert a final memory state. No binary/environment correspondence is supplied. -/
namespace Zig.External

inductive Termination where
  | total | partial
  deriving BEq, Repr

inductive Effects where
  | preserves | tracked
  deriving BEq, Repr

structure Contract (Args Result : Type) where
  pre : Args → Mem → Prop
  post : Args → Mem → Result → Mem → Prop
  /-- Must cover all observable state changes, including allocation/lifetime bookkeeping. -/
  frame : Args → Mem → Mem → Prop
  /-- Allowed new accesses, including their ranges, thread and read/write kind. -/
  access : Args → Mem → FootprintEntry → Prop
  failure : Args → Mem → Error → Prop
  divergence : Args → Mem → Prop

/-- A manifest-qualified obligation. `post` also constrains returned `Except ErrName` values.
Every success preserves the old access log and declares each newly recorded access. -/
def Contract.Holds {Args Result : Type} (c : Contract Args Result)
    (termination : Termination) (errors : List Error) (effects : Effects)
    (implementation : Args → MemM Result) : Prop :=
  ∀ args before, c.pre args before →
    match implementation args before with
    | none => termination = .partial ∧ c.divergence args before
    | some (.error error) => error ∈ errors ∧ c.failure args before error
    | some (.ok (result, after)) =>
      c.post args before result after ∧ c.frame args before after ∧
      (∃ delta : Array FootprintEntry, after.footprint = before.footprint ++ delta ∧
        ∀ entry, entry ∈ delta.toList → c.access args before entry) ∧
      (effects = .preserves → after = before)

/-- The reusable client rule is conditional on the declared precondition and evidence. -/
theorem Contract.success {Args Result : Type} (c : Contract Args Result)
    {termination errors effects implementation}
    (evidence : c.Holds termination errors effects implementation)
    {args before result after} (pre : c.pre args before)
    (run : implementation args before = some (.ok (result, after))) :
    c.post args before result after := by
  have h := evidence args before pre
  rw [run] at h
  exact h.1

/-- A total contract rules out divergence within its precondition. -/
theorem Contract.terminates {Args Result : Type} (c : Contract Args Result)
    {errors effects implementation} (evidence : c.Holds .total errors effects implementation)
    {args before} (pre : c.pre args before) : implementation args before ≠ none := by
  intro run
  have h := evidence args before pre
  rw [run] at h
  cases h.1

end Zig.External
