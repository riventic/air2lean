import ZigLean.Mem.Enc

/-!
# Atomics and threads

The `MemM` part of the thread model (`docs/std-models.md` §Thread model): the AIR atomic ops
(`atomic_load`, `atomic_store_*`, `atomic_rmw`, `cmpxchg_weak`/`cmpxchg_strong`), and the
bookkeeping of a spawn and a join (`Thread.fork`, `Thread.join`, `checkJoinedByChild`). The
scheduler (`ZigLean/Conc/Sched.lean`) calls the bookkeeping at a sync op; a concurrent function
calls an atomic op after a `yield` (`ZigLean/Conc/Call.lean`).

Every atomic op is sequentially consistent: the ordering argument decodes
(`Air2Lean.Air.Normalize.lean`'s `parseOrder`), and every atomic write releases and every atomic
read acquires. The subset restricts an atomic op's pointee to an integer type
(`Air2Lean.Check.lean`'s `atomicIntChild`).
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

/-! ## Atomics

An atomic access never races with another atomic access (`racePair`): the scheduler orders them.
Happens-before across threads through atomics: an atomic write releases, an atomic read acquires.
The location's release clock (`Mem.relClocks`) is the clock of its last atomic store, joined
with the clock of each RMW after it (the release sequence); a read merges it into the reader's
clock. So a plain access before the write and a plain access after the read do not race.
-/

/-- The current thread adopts the release clock of the atomic location `(b, o)`. -/
def acquireAt (b : BlockId) (o : Nat) : MemM Unit := modify fun m =>
  match m.relClocks.find? (fun e => e.1 == b && e.2.1 == o) with
  | some (_, _, c) => { m with clocks := m.clocks.set! m.current (VClock.merge (m.clocks[m.current]!) c) }
  | none => m

/-- The atomic location `(b, o)` gets the current thread's clock: it replaces the release clock
(a store), or joins it (an RMW: the release sequence goes on). -/
def releaseAt (b : BlockId) (o : Nat) (rmw : Bool) : MemM Unit := modify fun m =>
  let own := m.clocks[m.current]!
  let old := (m.relClocks.find? (fun e => e.1 == b && e.2.1 == o)).map (·.2.2)
  let c := if rmw then VClock.merge (old.getD #[]) own else own
  { m with relClocks := (m.relClocks.filter (fun e => !(e.1 == b && e.2.1 == o))).push (b, o, c) }

/-- `atomic_load`: `.atomicRead`, then acquire. -/
def atomicLoad {n : Nat} (align : Nat) (p : Ptr) : MemM (BitVec n) := do
  let (b, _, o) ← (← get).access p (intSize n) align
  let v ← intOfBytes n (← loadBytes p (intSize n) align .atomicRead)
  acquireAt b o
  pure v

/-- `atomic_store_*`: `.atomicWrite`, then release. -/
def atomicStore {n : Nat} (align : Nat) (p : Ptr) (v : BitVec n) : MemM Unit := do
  let (b, _, o) ← (← get).accessW p (intSize n) align
  storeBytes p align (padTo (intSize n) (intBytes v)) .atomicWrite
  releaseAt b o false

/-- `std.builtin.AtomicRmwOp`, restricted to the integer subset (`docs/std-models.md` §Thread
model: no float or `bool` RMW). -/
inductive RmwOp where
  | xchg | add | sub | and | nand | or | xor | max | min
  deriving BEq, Repr, Inhabited

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
the read and the write. Acquires, then releases into the release sequence. Returns the value
before the op. -/
def atomicRmw {n : Nat} (op : RmwOp) (signed : Bool) (align : Nat) (p : Ptr) (v : BitVec n) :
    MemM (BitVec n) := do
  let (b, blk, o) ← (← get).accessW p (intSize n) align
  let old ← intOfBytes n (blk.bytes.extract o (o + intSize n))
  recordAccess b o (intSize n) .atomicWrite
  acquireAt b o
  let m ← get
  let new := op.apply signed old v
  set { m with blocks := m.blocks.set! b { blk with bytes := writeBytes blk.bytes o (padTo (intSize n) (intBytes new)) } }
  releaseAt b o true
  pure old

/-- `cmpxchg_weak`/`cmpxchg_strong`: the model never fails spuriously, so both compile to this
(`Air2Lean.Op.cmpxchg`'s `weak` flag makes no difference here). Zig's convention: `none` on
success (the store happened), `some` of the current value on failure. A success is an RMW; a
failure only reads. -/
def cmpxchg {n : Nat} (align : Nat) (p : Ptr) (expected new : BitVec n) :
    MemM (Option (BitVec n)) := do
  let (b, blk, o) ← (← get).accessW p (intSize n) align
  let old ← intOfBytes n (blk.bytes.extract o (o + intSize n))
  if old = expected then
    recordAccess b o (intSize n) .atomicWrite
    acquireAt b o
    let m ← get
    set { m with blocks :=
      m.blocks.set! b { blk with bytes := writeBytes blk.bytes o (padTo (intSize n) (intBytes new)) } }
    releaseAt b o true
    pure none
  else
    recordAccess b o (intSize n) .atomicRead
    acquireAt b o
    pure (some old)

/-! ## Fork-join threads -/

namespace Thread

/-- `.illegal`: thread `t` finished without joining every thread that `t` itself spawned.
`spawn` checks it for each spawned thread; for the main thread (`t = 0`), the caller of the
top-level function checks it when the main thread ends (`ZigLean/Conc/Sched.lean`, `docs/std-models.md`
§Thread model). -/
def checkJoinedByChild (t : ThreadId) : MemM Unit := do
  let m ← get
  if m.threads.any (fun r => r.spawner == t && !r.joined) then throw .illegal

/-- The bookkeeping of a spawn: a new thread, spawned by the current one, whose clock is the
spawner's clock after a bump (the fork edge of the happens-before order). The current thread
does not change. -/
def fork : MemM ThreadId := do
  let m ← get
  let parent := m.current
  let parentClock := VClock.bump (m.clocks[parent]!) parent
  let child := m.threads.size
  set { m with
    clocks := (m.clocks.set! parent parentClock).push parentClock
    threads := m.threads.push { spawner := parent, joined := false } }
  pure child

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
