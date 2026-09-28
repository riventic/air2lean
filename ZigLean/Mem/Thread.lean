import ZigLean.Mem.Enc

/-!
# Atomics and threads

The model of `std.Thread.spawn`/`.join` (`docs/std-models.md` §Thread model), and of the AIR
atomic ops (`atomic_load`, `atomic_store_*`, `atomic_rmw`, `cmpxchg_weak`/`cmpxchg_strong`).
Fork-join only: `Thread.detach`, `.yield`, `.spinLoopHint`, `Futex`, `Mutex` and `Condition` are
outside the subset (`Air2Lean.Memory.lean`'s `rejectedThreadFn?`).

Every atomic op and RMW is sequentially consistent within one thread: the model does not weaken
`unordered`/`monotonic`/`acquire`/`release`/`acq_rel` orderings, it only checks the ordering
argument decodes (`Air2Lean.Air.Normalize.lean`'s `parseOrder`).

The subset restricts an atomic op's pointee to an integer type (`Air2Lean.Check.lean`'s
`atomicIntChild`): no float, `bool`, enum or pointer atomic.

`Thread.spawn` runs the spawned function's body eagerly, inside `spawn` itself, not deferred to
`join` — `Mem` cannot store a closure of type `MemM Unit` (strict positivity), and `Emit.lean`
knows the concrete callee and its arguments at the call site, so it emits the already-applied
call directly. Running it eagerly does not change which accesses are concurrent: that is a
property of the vector clocks (`ZigLean.Mem.Basic`'s `VClock`), not of physical execution order.

**Known limit**: a spin-wait on a flag that no thread the model has run yet has set does not
terminate — the model's `loop` recursion (`ZigLean/Basic.lean`) returns `none` for it, the same
as any other loop whose condition never becomes true (`docs/std-models.md` §Thread model).
-/

namespace Zig

/-- `std.Thread`: an opaque 8-byte handle (matching the real ABI size, `Air2Lean.Ty.thread`'s
`modelLayout`), encoded like a `BitVec 64` — the handle never reaches real memory bytes, since
`Thread.spawn`/`.join` only ever compare/store the model's own `ThreadId`, never a real OS handle. -/
instance : Enc ThreadId where
  size := 8
  align := 8
  encode tid := Enc.encode (BitVec.ofNat 64 tid)
  decode bs := do pure (← (Enc.decode bs : Result (BitVec 64))).toNat

/-! ## Atomics -/

/-- `atomic_load`: `.atomicRead`. -/
def atomicLoad {n : Nat} (align : Nat) (p : Ptr) : MemM (BitVec n) := do
  intOfBytes n (← loadBytes p (intSize n) align .atomicRead)

/-- `atomic_store_*`: a plain atomic store is `.atomicWrite none` — the model does not detect
that two stores of the identical value commute (`docs/std-models.md` §Thread model, a documented
limit). -/
def atomicStore {n : Nat} (align : Nat) (p : Ptr) (v : BitVec n) : MemM Unit :=
  storeBytes p align (padTo (intSize n) (intBytes v)) (.atomicWrite none)

/-- `std.builtin.AtomicRmwOp`, restricted to the integer subset (`docs/std-models.md` §Thread
model: no float or `bool` RMW). -/
inductive RmwOp where
  | xchg | add | sub | and | nand | or | xor | max | min
  deriving BEq, Repr, Inhabited

/-- The commuting group of `op` (`RmwGroup`, `ZigLean/Mem/Basic.lean`'s `racePair`): `none` when
the RMW's own result is used (`unused = false`) or `op` never commutes (`Xchg`, `Nand`).
`signed`: the operand's signedness (`Min`/`Max` only, as in `RmwOp.apply`). -/
def RmwOp.group (op : RmwOp) (signed unused : Bool) : Option RmwGroup :=
  if !unused then none else
  match op with
  | .add | .sub => some .addSub
  | .or => some .or
  | .and => some .and
  | .xor => some .xor
  | .min => some (.min signed)
  | .max => some (.max signed)
  | .xchg | .nand => none

/-- The value at the pointee after `op` on the old value `old` with operand `v`: integers of `n`
bits, signedness `signed` (`Min`/`Max` only — the model already wraps plain `+`/`-` on
`BitVec n`, which is what an integer RMW `Add`/`Sub` needs). -/
def RmwOp.apply (op : RmwOp) (signed : Bool) {n : Nat} (old v : BitVec n) : BitVec n :=
  match op with
  | .xchg => v
  | .add => old + v
  | .sub => old - v
  | .and => old &&& v
  | .nand => ~~~(old &&& v)
  | .or => old ||| v
  | .xor => old ^^^ v
  | .max => Zig.max signed old v
  | .min => Zig.min signed old v

/-- `atomic_rmw`: one indivisible read-modify-write, as a single footprint entry covering both
the read and the write (real hardware makes the whole op atomic, so a concurrent access races
with it as a whole, not with a separate read-phase and write-phase). Returns the value before
the op. `commute`: `RmwOp.group`. -/
def atomicRmw {n : Nat} (op : RmwOp) (signed : Bool) (align : Nat) (p : Ptr) (v : BitVec n)
    (commute : Option RmwGroup) : MemM (BitVec n) := do
  let (b, blk, o) ← (← get).access p (intSize n) align
  let old ← intOfBytes n (blk.bytes.extract o (o + intSize n))
  recordAccess b o (intSize n) (.atomicWrite commute)
  let m ← get
  let new := op.apply signed old v
  set { m with blocks := m.blocks.set! b { blk with bytes := writeBytes blk.bytes o (padTo (intSize n) (intBytes new)) } }
  pure old

/-- `cmpxchg_weak`/`cmpxchg_strong`: the model never fails spuriously, so both compile to this
(`Air2Lean.Op.cmpxchg`'s `weak` flag makes no difference here). Zig's convention: `none` on
success (the store happened), `some` of the current value on failure. A successful cmpxchg is
`.atomicWrite none` (the model does not attempt a cmpxchg commuting group); a failing one only
reads, `.atomicRead`. -/
def cmpxchg {n : Nat} (align : Nat) (p : Ptr) (expected new : BitVec n) :
    MemM (Option (BitVec n)) := do
  let (b, blk, o) ← (← get).access p (intSize n) align
  let old ← intOfBytes n (blk.bytes.extract o (o + intSize n))
  if old = expected then
    recordAccess b o (intSize n) (.atomicWrite none)
    let m ← get
    set { m with blocks :=
      m.blocks.set! b { blk with bytes := writeBytes blk.bytes o (padTo (intSize n) (intBytes new)) } }
    pure none
  else
    recordAccess b o (intSize n) .atomicRead
    pure (some old)

/-! ## Fork-join threads -/

namespace Thread

/-- `.illegal`: thread `t` finished without joining every thread that `t` itself spawned.
`spawn` checks it for each spawned thread; for the main thread (`t = 0`), the caller of the
top-level function checks it (`tests/diff/Diff.lean`'s `renderThread`, `docs/std-models.md`
§Thread model). -/
def checkJoinedByChild (t : ThreadId) : MemM Unit := do
  let m ← get
  if m.threads.any (fun r => r.spawner == t && !r.joined) then throw .illegal

/-- `std.Thread.spawn(config, f, args)`: `Emit.lean` emits the already-applied call `f args` as
`body` (both are static at the call site), and runs it eagerly as a new thread forked from the
current one. Never fails: `SpawnConfig`'s stack size and allocator have no observable effect in
the model, so the result is always `.ok`. -/
def spawn (body : MemM Unit) : MemM (Except ErrName ThreadId) := do
  let m ← get
  let parent := m.current
  let parentClock := VClock.bump (m.clocks[parent]!) parent
  let child := m.threads.size
  set { m with
    clocks := (m.clocks.set! parent parentClock).push parentClock
    threads := m.threads.push { spawner := parent, joined := false }
    current := child }
  body
  checkJoinedByChild child
  let m2 ← get
  set { m2 with current := parent }
  pure (.ok child)

/-- `std.Thread.join`: `tid` must have been spawned by the thread running this join, and not
already joined — a handle joined by anyone else, or joined twice, throws `.illegal`. Merges the
joined thread's clock into the caller's (the join edge of the happens-before order) and bumps
the caller's own clock. -/
def join (tid : ThreadId) : MemM Unit := do
  let m ← get
  let some rec := m.threads[tid]?
    | throw .illegal
  if rec.spawner != m.current || rec.joined then throw .illegal
  let callerClock := VClock.bump (m.clocks[m.current]!) m.current
  let merged := VClock.merge callerClock (m.clocks[tid]!)
  set { m with
    clocks := m.clocks.set! m.current merged
    threads := m.threads.set! tid { rec with joined := true } }

end Thread
end Zig
