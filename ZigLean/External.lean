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

/-! ## Calls from concurrent programs (E02, premise EXT-04)

A registry model runs as one step of the scheduler: its accesses are not interleaved with other
threads'. That matches a native run only when no other thread accesses the model's memory
without synchronization, which is a race and so `.illegal` in the model. A model need not record
its own accesses, so in a concurrent program the generated call first claims the whole block of
each declared footprint parameter (`claim`): one recorded access of the block, read or write,
checked against every concurrent access (`recordAccess`). A conflicting unsynchronized access by
another thread then throws `.illegal`, before or after the call. -/

/-- Record one access to the whole block of `r` (none for a pointer without a block: the
model's own access then throws, as the contract allows). A `const` global is never written: a
write claim of one throws `.illegal`, and a read claim records nothing (`recordAccessIn`). The
write claim is conservative: a model that declares a write but does not write would not fault
natively. -/
def claim {α : Type} [Region α] (r : α) (kind : AccessKind) : MemM Unit := fun m =>
  match Region.block r with
  | none => pure ((), m)
  | some b => match m.blocks[b]? with
    | some blk => (recordAccessIn b blk 0 blk.bytes.size kind).run m
    | none => pure ((), m)

/-- A recorded access changes no block. -/
theorem recordAccess_blocks {b o n : Nat} {kind : AccessKind} {m m' : Mem}
    (h : (recordAccess b o n kind).run m = pure ((), m')) : m'.blocks = m.blocks := by
  simp only [recordAccess, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, ExceptT.bind, ExceptT.mk, pure, ExceptT.pure, Option.bind_some, ExceptT.bindCont,
    set, StateT.set, MonadStateOf.set, throw, throwThe, MonadExceptOf.throw] at h
  generalize hr : raceCheck m (VClock.bump (m.clocks[m.current]!) m.current) b o n kind = r at h
  match r, hr, h with
  | some _, _, h => cases h
  | none, _, h =>
    simp only [ExceptT.bindCont, Option.bind_some] at h
    obtain ⟨-, rfl⟩ := h
    rfl

/-- `recordAccessIn` changes no block. -/
theorem recordAccessIn_blocks {b : BlockId} {blk : Block} {o n : Nat} {kind : AccessKind}
    {m m' : Mem} (h : (recordAccessIn b blk o n kind).run m = pure ((), m')) :
    m'.blocks = m.blocks := by
  unfold recordAccessIn at h
  split at h
  · split at h
    · cases h
    · cases h; rfl
  · exact recordAccess_blocks h

/-- A claim changes no block: only the access log and the clocks. -/
theorem claim_blocks {α : Type} [Region α] {r : α} {kind : AccessKind} {m m' : Mem}
    (h : (claim r kind).run m = pure ((), m')) : m'.blocks = m.blocks := by
  have pure_eq : ∀ {m₁ : Mem}, (pure ((), m₁) : Result (Unit × Mem)) = pure ((), m') → m' = m₁ :=
    fun h => by
      have h : some (Except.ok ((), _)) = some (Except.ok ((), m')) := h
      simp only [Option.some.injEq, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2.symm
  change (match Region.block r with
    | none => pure ((), m)
    | some b => match m.blocks[b]? with
      | some blk => (recordAccessIn b blk 0 blk.bytes.size kind).run m
      | none => pure ((), m)) = _ at h
  split at h
  · rw [pure_eq h]
  · split at h
    · exact recordAccessIn_blocks h
    · rw [pure_eq h]

end Zig.External
