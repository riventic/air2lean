import ZigLean.Mem.Basic

/-! Typed contracts for selected sequential external models. Safety errors, returned Zig
errors, and divergence are distinct. StateT erases memory on failure, so failure predicates
cannot assert a final memory state. No binary/environment correspondence is supplied. -/
namespace Zig.External

inductive Termination where
  | total | «partial»
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
    | none => termination = .«partial» ∧ c.divergence args before
    | some (.error error) => error ∈ errors ∧ c.failure args before error
    | some (.ok (result, after)) =>
      c.post args before result after ∧ c.frame args before after ∧
      (∃ delta : Array FootprintEntry, after.footprint = before.footprint ++ delta ∧
        ∀ entry, entry ∈ delta.toList → c.access args before entry) ∧
      (effects = .preserves → after = before)

/-- The reusable client rule is conditional on the declared precondition and evidence. -/
theorem Contract.success {Args Result : Type} (c : Contract Args Result)
    {termination : Termination} {errors : List Error} {effects : Effects}
    {implementation : Args → MemM Result}
    (evidence : c.Holds termination errors effects implementation)
    {args before result after} (pre : c.pre args before)
    (run : implementation args before = some (.ok (result, after))) :
    c.post args before result after := by
  have h := evidence args before pre
  rw [run] at h
  exact h.1

/-- A total contract rules out divergence within its precondition. -/
theorem Contract.terminates {Args Result : Type} (c : Contract Args Result)
    {errors : List Error} {effects : Effects} {implementation : Args → MemM Result}
    (evidence : c.Holds .total errors effects implementation)
    {args before} (pre : c.pre args before) : implementation args before ≠ none := by
  intro run
  have h := evidence args before pre
  rw [run] at h
  cases h.1

/-! ## Declared memory footprints

A footprint names the argument regions (blocks of pointer/slice arguments) that one call may
read and write. `Respects` ties it to a contract: every newly recorded access is covered, and
the frame leaves every block outside the written regions unchanged. A footprint excludes
allocation/free of other blocks; such models declare no footprint. -/

/-- The block an argument designates; `none` for a pointer without a block. -/
class Region (α : Type) where
  block : α → Option BlockId

instance : Region Ptr := ⟨Ptr.block⟩
instance : Region Slice := ⟨fun s => s.ptr.block⟩

structure Footprint (Args : Type) where
  reads : Args → List (Option BlockId)
  writes : Args → List (Option BlockId)

/-- An access is covered by a written region, or is a non-writing access of a read region. -/
def Footprint.Covers {Args : Type} (fp : Footprint Args) (args : Args) (entry : FootprintEntry) :
    Prop :=
  some entry.block ∈ fp.writes args ∨
    (some entry.block ∈ fp.reads args ∧ entry.kind.isWrite = false)

def Contract.Respects {Args Result : Type} (c : Contract Args Result) (fp : Footprint Args) :
    Prop :=
  (∀ args before entry, c.access args before entry → fp.Covers args entry) ∧
  (∀ args before after, c.pre args before → c.frame args before after →
    ∀ b, some b ∉ fp.writes args → after.blocks[b]? = before.blocks[b]?)

/-- Client frame rule: a successful call leaves every block outside its written regions
unchanged. -/
theorem Contract.frame_outside {Args Result : Type} (c : Contract Args Result)
    {termination : Termination} {errors : List Error} {effects : Effects}
    {implementation : Args → MemM Result} {fp : Footprint Args}
    (evidence : c.Holds termination errors effects implementation) (respects : c.Respects fp)
    {args before result after} (pre : c.pre args before)
    (run : implementation args before = some (.ok (result, after)))
    {b : BlockId} (outside : some b ∉ fp.writes args) : after.blocks[b]? = before.blocks[b]? := by
  have h := evidence args before pre
  rw [run] at h
  exact respects.2 args before after pre h.2.1 b outside

/-- Every access a successful call records is covered by the declared footprint. -/
theorem Contract.accesses_within {Args Result : Type} (c : Contract Args Result)
    {termination : Termination} {errors : List Error} {effects : Effects}
    {implementation : Args → MemM Result} {fp : Footprint Args}
    (evidence : c.Holds termination errors effects implementation) (respects : c.Respects fp)
    {args before result after} (pre : c.pre args before)
    (run : implementation args before = some (.ok (result, after))) :
    ∃ delta : Array FootprintEntry, after.footprint = before.footprint ++ delta ∧
      ∀ entry, entry ∈ delta.toList → fp.Covers args entry := by
  have h := evidence args before pre
  rw [run] at h
  obtain ⟨delta, hlog, hcov⟩ := h.2.2.1
  exact ⟨delta, hlog, fun entry mem => respects.1 args before entry (hcov entry mem)⟩

end Zig.External
