import ZigLean.Mem.Basic

/-!
# Thread-local storage

A `threadlocal var` (`docs/generated-code.md` §Thread-local storage) has one instance per
thread. Its **key** is the block of the main thread's instance in `mem0`; `Emit.lean` lists every
`threadlocal` global of the program with its key, initial bytes and alignment (`tlsInit`).

- **Instances.** `ThreadRec.tls` maps each key to the thread's instance block. The main thread's
  instances are the key blocks of `mem0` (`Mem.mainTls`). A spawned thread makes its own
  instances when it starts (`tlsEnter`, the first step of the generated dispatcher): one new
  block per key, which the thread writes with the initial bytes. So the same name in two threads
  is two blocks, and a block is the instance of at most one thread
  (`ZigLean/Conc/TlsLemmas.lean`).
- **Address.** `runtime_nav_ptr` is `tlsPtr key`: a pointer to the current thread's instance,
  at offset 0. It reads only the thread's record, so it is no memory access. The pointer is an
  ordinary `Ptr` to the instance's block: it can be stored, passed to another thread and
  compared, and every access through it is an ordinary access of that block (race check,
  liveness, bounds, alignment).
- **Lifetime.** A spawned thread's instances die when the thread ends (`tlsExit`, the last step
  of the dispatcher, before the scheduler's end-of-thread check): they are freed, so an access
  through a pointer that escaped to another thread throws `.illegal` afterwards. The main
  thread's instances live until the run ends.
- **Ownership.** An instance is a block of its thread. Passing its pointer to another thread
  hands over nothing by itself: as for any pointer (`ZigLean/Conc/Transfer.lean`), a
  concurrent access without a happens-before edge is a data race (`.illegal`), and a proof
  transfers the cells explicitly.

`tlsPtr` throws `.illegal` for a key the thread has no instance of (a malformed program, or a
direct call on a thread that did not run `tlsEnter`); generated code never does that.
-/

namespace Zig

/-- The TLS instances of thread `t`, as `(key, instance block)`. -/
def Mem.tlsOf (m : Mem) (t : ThreadId) : Array (BlockId × BlockId) :=
  ((m.threads[t]?).map (·.tls)).getD #[]

/-- `m` where thread `t`'s TLS instances are `ids`. -/
def Mem.setTls (m : Mem) (t : ThreadId) (ids : Array (BlockId × BlockId)) : Mem :=
  { m with threads := m.threads.modify t fun r => { r with tls := ids } }

/-- Program start: the main thread's instance of each key is the key block itself. -/
def Mem.mainTls (m : Mem) (keys : Array BlockId) : Mem := m.setTls 0 (keys.map fun k => (k, k))

/-- Thread `t`'s instance of `key`. -/
def Mem.tlsInstance (m : Mem) (t : ThreadId) (key : BlockId) : Option BlockId :=
  ((m.tlsOf t).find? (·.1 == key)).map (·.2)

/-- `runtime_nav_ptr` of the `threadlocal` global with the key `key`: the current thread's
instance, at offset 0. -/
def tlsPtr (key : BlockId) : MemM Ptr := do
  let m ← get
  match m.tlsInstance m.current key with
  | some b => pure ⟨some b, 0⟩
  | none => throw .illegal

/-- One new instance: a writable block of `bs.size` bytes, which the current thread writes with
the initial bytes `bs`. -/
def tlsAlloc (bs : Array Byte) (align : Nat) : MemM Ptr := do
  let p ← alloc .global bs.size align
  storeBytes p align bs
  pure p

/-- The new instances, in the order of `inits`. -/
def tlsAllocs : List (BlockId × Array Byte × Nat) → MemM (Array (BlockId × BlockId))
  | [] => pure #[]
  | (key, bs, a) :: rest => do
    let p ← tlsAlloc bs a
    let ids ← tlsAllocs rest
    pure (#[(key, p.block.getD 0)] ++ ids)

/-- Thread start: the current thread's instance of every `threadlocal` global, from its key,
initial bytes and alignment (`inits`). -/
def tlsEnter (inits : List (BlockId × Array Byte × Nat)) : MemM Unit := do
  let ids ← tlsAllocs inits
  modify fun m => m.setTls m.current ids

/-- Free the blocks `bs`, in order. -/
def freeBlocks : List BlockId → MemM Unit
  | [] => pure ()
  | b :: bs => do free ⟨some b, 0⟩; freeBlocks bs

/-- Thread end: every instance of the current thread dies. -/
def tlsExit : MemM Unit := do
  let m ← get
  freeBlocks ((m.tlsOf m.current).toList.map (·.2))

end Zig
