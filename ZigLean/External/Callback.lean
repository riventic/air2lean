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
A call through a pointer that has neither a known target nor a contract is `dispatch []`, which
mirrors the `throw .illegal` fallback of the emitted indirect call. It never succeeds, so no effects,
including empty ones, follow for it. -/
namespace Zig.External

inductive Reentrancy where
  | forbidden | allowed
  deriving DecidableEq, Repr

inductive Cancellation where
  | never | byResult
  deriving DecidableEq, Repr

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

/-! ## The callable-address table (L11)

Every function-pointer value of a translated program, whatever its origin (a constant, a
global initializer, a struct field, a parameter or memory), is called through one table: the
address-taken functions, each a function block's address with its signature (`fnRefs` in
`Air2Lean/Memory.lean`). A call through a pointer of signature `s` dispatches over exactly the
table's entries of signature `s`, in table order (`resolve`). The emitted indirect call is
`dispatchIn` over those entries: an `if p == q then call else …` chain ending in
`throw .illegal`.

The theorems below state the rules of that table: every declared target of the signature is
reachable (`resolve_complete`), a pointer to a target of another signature is rejected
(`resolve_incompatible`), and so is a pointer that is not a table address (`resolve_unknown`).
Distinct entries need distinct addresses (`Nodup`): function blocks are distinct global
blocks. -/

/-- The emitted form of an indirect call, in any monad that can throw: each known target's
block is compared with the pointer, in order, and any other pointer throws `.illegal`. -/
def dispatchIn {M : Type → Type} [MonadExceptOf Error M] {β : Type} :
    List (Ptr × M β) → Ptr → M β
  | [], _ => throw .illegal
  | (q, c) :: rest, p => if p == q then c else dispatchIn rest p

/-- `dispatch` is `dispatchIn` with the arguments applied. -/
theorem dispatch_eq_dispatchIn {Args Result : Type}
    (targets : List (Ptr × (Args → MemM Result))) (p : Ptr) (a : Args) :
    dispatch targets p a = dispatchIn (targets.map fun t => (t.1, t.2 a)) p := by
  induction targets with
  | nil => rfl
  | cons t rest ih =>
    obtain ⟨q, f⟩ := t
    simp only [dispatch, dispatchIn, List.map, beq_iff_eq, ih]

/-- A pointer that is no target's address is rejected. -/
theorem dispatchIn_not_mem {M : Type → Type} [MonadExceptOf Error M] {β : Type}
    {targets : List (Ptr × M β)} {p : Ptr} (h : p ∉ targets.map (·.1)) :
    dispatchIn targets p = throw .illegal := by
  induction targets with
  | nil => rfl
  | cons t rest ih =>
    simp only [List.map, List.mem_cons, not_or] at h
    simp only [dispatchIn, beq_iff_eq, h.1, ↓reduceIte, ih h.2]

/-- With distinct addresses, the pointer of a target runs exactly that target. -/
theorem dispatchIn_mem {M : Type → Type} [MonadExceptOf Error M] {β : Type}
    {targets : List (Ptr × M β)} {q : Ptr} {c : M β} (mem : (q, c) ∈ targets)
    (nodup : (targets.map (·.1)).Nodup) : dispatchIn targets q = c := by
  induction targets with
  | nil => cases mem
  | cons t rest ih =>
    obtain ⟨q', c'⟩ := t
    simp only [List.map, List.nodup_cons] at nodup
    rcases List.mem_cons.mp mem with h | h
    · cases h
      simp [dispatchIn]
    · have hq : q ≠ q' := fun e => nodup.1 (e ▸ List.mem_map_of_mem (f := (·.1)) h)
      simp only [dispatchIn, beq_iff_eq, hq, ↓reduceIte, ih h nodup.2]

theorem dispatch_not_mem {Args Result : Type} {targets : List (Ptr × (Args → MemM Result))}
    {p : Ptr} (h : p ∉ targets.map (·.1)) (a : Args) :
    dispatch targets p a = throw .illegal := by
  rw [dispatch_eq_dispatchIn]
  exact dispatchIn_not_mem (by simpa [List.map_map] using h)

theorem dispatch_mem {Args Result : Type} {targets : List (Ptr × (Args → MemM Result))}
    {q : Ptr} {f : Args → MemM Result} (mem : (q, f) ∈ targets)
    (nodup : (targets.map (·.1)).Nodup) (a : Args) : dispatch targets q a = f a := by
  rw [dispatch_eq_dispatchIn]
  exact dispatchIn_mem (List.mem_map_of_mem (f := fun t => (t.1, t.2 a)) mem)
    (by simpa [List.map_map, Function.comp_def] using nodup)

/-- The targets of a call through a pointer of signature `s`: the table's entries of that
signature, in order, each with its implementation at `s`. -/
def resolve {Sig β : Type} [DecidableEq Sig] (table : List (Sig × Ptr)) (s : Sig)
    (impl : Ptr → β) : List (Ptr × β) :=
  table.filterMap fun e => if e.1 = s then some (e.2, impl e.2) else none

theorem resolve_addresses {Sig β : Type} [DecidableEq Sig] (table : List (Sig × Ptr))
    (s : Sig) (impl : Ptr → β) :
    (resolve table s impl).map (·.1) = (table.filter (·.1 = s)).map (·.2) := by
  induction table with
  | nil => rfl
  | cons e rest ih =>
    simp only [resolve] at ih ⊢
    by_cases h : e.1 = s <;> simp [h, ih]

theorem mem_resolve_addresses {Sig β : Type} [DecidableEq Sig] {table : List (Sig × Ptr)}
    {s : Sig} {impl : Ptr → β} {p : Ptr} :
    p ∈ (resolve table s impl).map (·.1) ↔ (s, p) ∈ table := by
  rw [resolve_addresses]
  constructor
  · intro h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
    have := List.mem_filter.mp he
    have hs : e.1 = s := by simpa using this.2
    exact hs ▸ this.1
  · intro h
    exact List.mem_map.mpr ⟨(s, p), List.mem_filter.mpr ⟨h, by simp⟩, rfl⟩

theorem resolve_nodup {Sig β : Type} [DecidableEq Sig] {table : List (Sig × Ptr)}
    (nodup : (table.map (·.2)).Nodup) (s : Sig) (impl : Ptr → β) :
    ((resolve table s impl).map (·.1)).Nodup := by
  rw [resolve_addresses]
  exact (List.filter_sublist.map _).nodup nodup

/-- Dispatch completeness: every declared target of the call's signature is reachable, and
its address runs its own implementation. -/
theorem resolve_complete {Sig : Type} [DecidableEq Sig] {M : Type → Type}
    [MonadExceptOf Error M] {β : Type} {table : List (Sig × Ptr)} {s : Sig}
    {impl : Ptr → M β} {q : Ptr} (mem : (s, q) ∈ table) (nodup : (table.map (·.2)).Nodup) :
    dispatchIn (resolve table s impl) q = impl q := by
  apply dispatchIn_mem _ (resolve_nodup nodup s impl)
  induction table with
  | nil => cases mem
  | cons e rest ih =>
    simp only [List.map, List.nodup_cons] at nodup
    rcases List.mem_cons.mp mem with h | h
    · subst h; simp [resolve]
    · have := ih h nodup.2
      by_cases he : e.1 = s <;> simp_all [resolve]

/-- A pointer to a declared target of another signature is rejected: with distinct
addresses it is no address of the call's signature. -/
theorem resolve_incompatible {Sig : Type} [DecidableEq Sig] {M : Type → Type}
    [MonadExceptOf Error M] {β : Type} {table : List (Sig × Ptr)} {s t : Sig}
    {impl : Ptr → M β} {q : Ptr} (mem : (t, q) ∈ table) (ne : t ≠ s)
    (nodup : (table.map (·.2)).Nodup) :
    dispatchIn (resolve table s impl) q = throw .illegal := by
  apply dispatchIn_not_mem
  rw [mem_resolve_addresses]
  intro hs
  induction table with
  | nil => cases mem
  | cons e rest ih =>
    simp only [List.map, List.nodup_cons] at nodup
    rcases List.mem_cons.mp mem with h | h <;> rcases List.mem_cons.mp hs with h' | h'
    · exact ne (by rw [← h] at h'; exact (Prod.mk.inj h').1.symm)
    · exact nodup.1 (h ▸ List.mem_map_of_mem (f := (·.2)) h')
    · exact nodup.1 (h' ▸ List.mem_map_of_mem (f := (·.2)) h)
    · exact ih h nodup.2 h'

/-- An unknown executable address, which is no table entry, is rejected. -/
theorem resolve_unknown {Sig : Type} [DecidableEq Sig] {M : Type → Type}
    [MonadExceptOf Error M] {β : Type} {table : List (Sig × Ptr)} {s : Sig}
    {impl : Ptr → M β} {p : Ptr} (h : p ∉ table.map (·.2)) :
    dispatchIn (resolve table s impl) p = throw .illegal := by
  apply dispatchIn_not_mem
  rw [mem_resolve_addresses]
  exact fun hs => h (List.mem_map_of_mem (f := (·.2)) hs)

/-- A successful indirect call ran a declared target of the call's signature. -/
theorem resolve_ok {Sig Args Result : Type} [DecidableEq Sig] {table : List (Sig × Ptr)}
    {s : Sig} {impl : Ptr → Args → MemM Result} {p : Ptr} {a : Args} {m m' : Mem} {r : Result}
    (run : dispatch (resolve table s impl) p a m = some (.ok (r, m'))) :
    (s, p) ∈ table ∧ impl p a m = some (.ok (r, m')) := by
  obtain ⟨f, mem, hf⟩ := dispatch_ok run
  have hp : p ∈ (resolve table s impl).map (·.1) := List.mem_map_of_mem (f := (·.1)) mem
  refine ⟨mem_resolve_addresses.mp hp, ?_⟩
  obtain ⟨e, _, he⟩ := List.mem_filterMap.mp mem
  by_cases hs : e.1 = s
  · simp only [hs, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at he
    rw [← he.2, he.1] at hf
    exact hf
  · simp [hs] at he

end Zig.External
