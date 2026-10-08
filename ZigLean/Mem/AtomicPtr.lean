import ZigLean.Mem.Thread

/-!
# Pointer atomics

AIR atomic ops whose pointee is a pointer: `*T` (`Zig.Ptr`) or `?*T` (`Option Zig.Ptr`)
(`docs/std-models.md` §Thread model, C09). The RC11 rules are those of the integer ops
(`ZigLean/Mem/Thread.lean`): the same preparation (`loadPrep`, `storePrep`, `casReadPrep`), the
same options of the oracle and the same clocks. Only the value differs:

- **Provenance.** A message holds the pointer's own bytes (`Enc.encode`: eight `Byte.ptrFrag`
  bytes, or eight zero bytes for `null`), so a pointer that one thread publishes is read back by
  another with its block and offset. A load decodes with `Enc.decode`; bytes that are not one
  whole pointer (an integer, `undefined`) throw `.unspecified`, as for a plain pointer load.
- **Compare** (`ptrValEq`). `cmpxchg` compares pointer identities, not bare integers. Two pointers
  with the same block and offset are equal. Two pointers with different identities are unequal
  when their addresses differ. Different identities at the same address (a pointer past its
  block that reaches another one, an address without a block, a `null` against a pointer at
  address 0) or a pointer whose block is not in the memory throw `.unspecified`: the hardware
  compares addresses, and the model neither claims that outcome nor drops it. So two pointers to
  different blocks never compare equal.
- **RMW.** Zig allows only `.Xchg` on a pointer (`atomicXchgPtrAt`); `Air2Lean/Check.lean` rejects
  the other operations.

A `usize` from `@intFromPtr` stays an integer atomic. Float atomics are outside the subset
(`Air2Lean/Check.lean`).
-/

namespace Zig

/-- The address of `p` in `m` (`ptrAddr` without the monad): `none` if its block is not in
`m`. -/
def Mem.ptrAddr? (m : Mem) (p : Ptr) : Option Int :=
  match p.block with
  | none => some p.off
  | some b => m.blocks[b]?.map fun blk => blk.addr + p.off

/-- A pointer value of an atomic op: `*T` or `?*T`. `addr`: its address in a memory (`null`: 0). -/
class AtomicPtrVal (α : Type) where
  addr : Mem → α → Option Int

instance : AtomicPtrVal Ptr where
  addr m p := m.ptrAddr? p

instance : AtomicPtrVal (Option Ptr) where
  addr m
    | none => some 0
    | some p => m.ptrAddr? p

section
variable {α : Type} [Enc α] [DecidableEq α] [AtomicPtrVal α]

/-- The compare of a pointer `cmpxchg` (module doc): identity; `.unspecified` when identity and
address disagree or an address is unknown. -/
def ptrValEq (m : Mem) (a b : α) : Result Bool :=
  if a = b then pure true else
  match AtomicPtrVal.addr m a, AtomicPtrVal.addr m b with
  | some x, some y => if x = y then throw .unspecified else pure false
  | _, _ => throw .unspecified

/-- Message `pos` of location `li` holds a pointer equal to `expected` (`ptrValEq`). -/
def ptrMsgEq (m : Mem) (li pos : Nat) (expected : α) : Bool :=
  match (do ptrValEq m (← (Enc.decode (m.atomics[li]!).msgs[pos]!.bytes : Result α)) expected).run with
  | some (.ok true) => true
  | _ => false

/-- `atomic_load` of a pointer: option `c` of `loadCount 64`. -/
def atomicLoadPtrAt (α : Type) [Enc α] (c : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) :
    MemM α := do
  let (li, opts) ← loadPrep 64 ord align p false
  let some pos := opts[c]? | throw .illegal
  let msg := (← get).atomics[li]!.msgs[pos]!
  observe li msg.id
  if ord.isAcq then acquireClock msg.relClock
  StateT.lift (Enc.decode msg.bytes)

/-- `atomic_store_*` of a pointer: place `c` of `storeCount 64`. The message holds the pointer's
bytes. -/
def atomicStorePtrAt (c : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) (v : α) :
    MemM Unit := do
  let (li, slots) ← storePrep 64 ord align p
  let some slot := slots[c]? | throw .illegal
  let m ← get
  let cl := m.clocks[m.current]!
  let id := m.nextMsg
  insertMsg li slot
    { id, bytes := Enc.encode v, clock := cl, relClock := (if ord.isRel then cl else #[]) }
  observe li id

/-- `rmwWrite` with the bytes of the new value. -/
def rmwWriteBytes (li pos : Nat) (ord : AtomicOrder) (rd : Msg) (bytes : Array Byte) : MemM Unit := do
  if ord.isAcq then acquireClock rd.relClock
  let m ← get
  let cl := m.clocks[m.current]!
  let id := m.nextMsg
  insertMsg li (pos + 1)
    { id, bytes, clock := cl,
      relClock := (if ord.isRel then VClock.merge rd.relClock cl else rd.relClock), rmwOf := some rd.id }
  observe li id

/-- `atomic_rmw .Xchg` of a pointer: option `c` of `rmwCount 64`. Returns the old pointer. -/
def atomicXchgPtrAt (c : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) (v : α) : MemM α := do
  let (li, opts) ← loadPrep 64 ord align p true
  let some pos := opts[c]? | throw .illegal
  let rd := (← get).atomics[li]!.msgs[pos]!
  let old : α ← StateT.lift (Enc.decode rd.bytes)
  rmwWriteBytes li pos ord rd (Enc.encode v)
  pure old

/-- The strong choices of a pointer `cmpxchg` (`casStrongOpts` with `ptrMsgEq`). -/
def casPtrStrongOpts (m : Mem) (li : Nat) (expected : α) (readable : Array Nat) : Array Nat :=
  readable.filter fun pos => !((m.atomics[li]!).hasRmwAfter pos && ptrMsgEq m li pos expected)

def casPtrPrep (align : Nat) (p : Ptr) (expected : α) : MemM (Nat × Array Nat) := do
  let (li, readable) ← casReadPrep 64 align p
  pure (li, casPtrStrongOpts (← get) li expected readable)

def casPtrCount (align : Nat) (p : Ptr) (expected : α) : Mem → Nat :=
  optCount ((·.2) <$> casPtrPrep align p expected)

/-- The success or failure of a pointer `cmpxchg` that read `rd` (`cmpxchgAt`'s tail). -/
def casPtrFinish (succ fail : AtomicOrder) (align : Nat) (p : Ptr) (li pos : Nat) (rd : Msg)
    (old new : α) (ok : Bool) : MemM (Option α) := do
  if ok then
    casMarkWrite 64 align p
    rmwWriteBytes li pos succ rd (Enc.encode new)
    pure none
  else
    observe li rd.id
    if fail.isAcq then acquireClock rd.relClock
    pure (some old)

/-- `cmpxchg_strong` of a pointer: option `c` of `casPtrCount`. `none` on success, `some` of the
pointer read on failure. -/
def cmpxchgPtrAt (c : Nat) (succ fail : AtomicOrder) (align : Nat) (p : Ptr) (expected new : α) :
    MemM (Option α) := do
  let (li, opts) ← casPtrPrep align p expected
  let some pos := opts[c]? | throw .illegal
  let rd := (← get).atomics[li]!.msgs[pos]!
  let old : α ← StateT.lift (Enc.decode rd.bytes)
  let eq ← StateT.lift (ptrValEq (← get) old expected)
  casPtrFinish succ fail align p li pos rd old new eq

/-- The weak choices (`weakCasOpts` with `ptrMsgEq`): the strong ones, then a forced failure for
each readable message equal to `expected`. -/
def weakCasPtrPrep (align : Nat) (p : Ptr) (expected : α) : MemM (Nat × Array (Nat × Bool)) := do
  let (li, readable) ← casReadPrep 64 align p
  let m ← get
  pure (li, (casPtrStrongOpts m li expected readable).map (·, false) ++
    (readable.filter fun pos => ptrMsgEq m li pos expected).map (·, true))

def weakCasPtrCount (align : Nat) (p : Ptr) (expected : α) : Mem → Nat :=
  optCount ((·.2) <$> weakCasPtrPrep align p expected)

/-- `cmpxchg_weak` of a pointer: option `c` of `weakCasPtrCount`; a forced failure is a permitted
spurious failure (`cmpxchgWeakAt`). -/
def cmpxchgWeakPtrAt (c : Nat) (succ fail : AtomicOrder) (align : Nat) (p : Ptr)
    (expected new : α) : MemM (Option α) := do
  let (li, opts) ← weakCasPtrPrep align p expected
  let some (pos, spurious) := opts[c]? | throw .illegal
  let rd := (← get).atomics[li]!.msgs[pos]!
  let old : α ← StateT.lift (Enc.decode rd.bytes)
  let eq ← StateT.lift (ptrValEq (← get) old expected)
  casPtrFinish succ fail align p li pos rd old new (eq && !spurious)

end

/-! ## The compare keeps block identity -/

/-- Equal pointers compare equal. -/
theorem ptrValEq_self {α : Type} [Enc α] [DecidableEq α] [AtomicPtrVal α] (m : Mem) (a : α) :
    ptrValEq m a a = pure true := by
  simp [ptrValEq]

/-- **No compare of different pointers succeeds**: `ptrValEq` of two different pointers is
`false` or `.unspecified`, never `true`, whatever their addresses. -/
theorem ptrValEq_ne {α : Type} [Enc α] [DecidableEq α] [AtomicPtrVal α] {m : Mem} {a b : α}
    (h : a ≠ b) : (ptrValEq m a b).run ≠ some (.ok true) := by
  unfold ptrValEq
  simp only [h, ↓reduceIte]
  split
  · split <;> simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.run, pure, ExceptT.pure]
  · simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.run]

/-- Pointers to two different blocks never compare equal, also at the same address. -/
theorem ptrValEq_blocks {m : Mem} {b b' : BlockId} {o o' : Int} (h : b ≠ b') :
    (ptrValEq m (⟨some b, o⟩ : Ptr) ⟨some b', o'⟩).run ≠ some (.ok true) :=
  ptrValEq_ne (by simp [h])

end Zig
