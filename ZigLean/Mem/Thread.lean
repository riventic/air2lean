import ZigLean.Mem.Enc
import ZigLean.Packed

/-!
# Atomics and threads

The `MemM` part of the thread model (`docs/std-models.md` §Thread model): the AIR atomic ops
(`atomic_load`, `atomic_store_*`, `atomic_rmw`, `cmpxchg_weak`/`cmpxchg_strong`), and the
bookkeeping of a spawn and a join (`Thread.fork`, `Thread.join`, `checkJoinedByChild`). The
scheduler (`ZigLean/Conc/Sched.lean`) calls the bookkeeping at a sync op; a concurrent function
calls an atomic op after a `pick` (`ZigLean/Conc/Call.lean`).

The ordering argument decodes through `parseOrder` (`Air2Lean/Air/Normalize.lean`): relaxed
operations do not synchronize; release writes publish their clocks and acquire reads adopt
them. There is no global sequentially consistent order. Integer, enum, bool and packed-struct
pointees use integer operations on their bits (`Air2Lean/Check.lean`, `Zig.Packed`).
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

/-! ## Atomics (RC11)

The memory model approximates RC11's operational form without promises. Its missing SC order
and read-view transfer can permit extra outcomes
(`docs/std-models.md` §Thread model). An atomic location (`ALoc`) keeps its writes (`Msg`) in
modification order; the block's
bytes are those of the last one. At each atomic op the oracle picks (`SyncOp.pick`, the options
from `*Count`):

- A read reads any message that is not older than a message that happened before it (its clock
  is `≤` the reader's) and not older than a message the thread read or wrote before
  (`Mem.seen`). Option 0 is the newest.
- A write goes to any place after those messages, but not between an RMW and the message it
  read. Option 0 is the end.
- An RMW reads a message that has no RMW after it yet, and goes right after it.
- A `seq_cst` op has the rule of `acq_rel`: the model has no global SC order. So it allows more
  results than RC11 (a proof never depends on a result that RC11 forbids), but a proof that needs
  the SC order (store buffering, Dekker) does not go through.
- An acquire read adopts the message's release clock (`Msg.relClock`): the writer's clock for a
  release write, joined along the RMWs after it. That is the only happens-before edge of atomics.

Modification order holds write events, not values: every atomic write is a new message with a
fresh id, so repeated equal values stay distinct messages with their own clocks, release clocks
and RMW edges. A plain write to an atomic location (the value before the first atomic op, or a
write after a join) becomes a message at the next atomic op (`locIdx`) whenever it did not happen
before the newest message (`plainSince`), even if it wrote the bytes the location already had; a
race with it is `.illegal`, so it happened before that op. Two atomic accesses never race
(`racePair`).

**Mixed-size policy**: an atomic location is one `(block, offset, size)`. An atomic access that
overlaps an existing atomic location with another offset or size is rejected with
`.unspecified`, before any message is read or written (`locIdx`). Plain accesses of any size are
unaffected; a plain write that overlaps the location becomes a message as above.

**Trusted assumption** (`docs/std-models.md` §Thread model, premise ORD-02): the compiled code
has no load buffering (RC11); LLVM does not promise that for relaxed atomics. The translator
rejects the straight-line load-buffering shape (a relaxed read, then a relaxed write to another
address) unless `--assume-no-lb` (`checkLoadBuffering`,
`Air2Lean/Check.lean`).
-/

/-- The footprint entry `e` is a plain write to a byte of `o..o+len` of block `b`. -/
def plainHit (b : BlockId) (o len : Nat) (e : FootprintEntry) : Bool :=
  e.block == b && e.kind == .write && o < e.off + e.len && e.off < o + len

/-- The join of the clocks of the plain writes to the bytes `o..o+len` of block `b` (`#[]`: none,
the value from before every thread). Without a race these writes are ordered, so it is the clock
of the last one. -/
def plainClock (m : Mem) (b : BlockId) (o len : Nat) : VClock :=
  (m.footprint.filter (plainHit b o len)).foldl (fun c e => VClock.merge c e.clock) #[]

/-- A plain write to the bytes `o..o+len` of block `b` did not happen before the clock `c` (of
the newest message): it is a write event after that message. -/
def plainSince (m : Mem) (b : BlockId) (o len : Nat) (c : VClock) : Bool :=
  m.footprint.any fun e => plainHit b o len e && !VClock.le e.clock c

/-- The clock of the newest message of `l`. -/
def ALoc.lastClock (l : ALoc) : VClock := (l.msgs.back?.map (·.clock)).getD #[]

/-- The atomic location at `(b, o)` of `len` bytes: created at the first atomic op, with the
bytes as its first message; a plain write since the last message (a write event, whatever its
value) becomes a message. An overlapping location of another offset or size is `.unspecified`
(the mixed-size policy). -/
def locIdx (b : BlockId) (o len : Nat) : MemM Nat := do
  let m ← get
  let cur := ((m.blocks[b]?.map (·.bytes)).getD #[]).extract o (o + len)
  match m.atomics.findIdx? (fun l => l.block == b && l.off == o) with
  | some i =>
    let l := m.atomics[i]!
    if l.len != len then throw .unspecified
    let last := (l.msgs.back?.map (·.bytes)).getD #[]
    let (msgs, next) := if last == cur && !plainSince m b o len l.lastClock then (l.msgs, m.nextMsg) else
      (l.msgs.push { id := m.nextMsg, bytes := cur, clock := plainClock m b o len, relClock := #[] },
       m.nextMsg + 1)
    set { m with atomics := m.atomics.set! i { l with msgs }, nextMsg := next }
    pure i
  | none =>
    if m.atomics.any (fun l => l.block == b && o < l.off + l.len && l.off < o + len) then
      throw .unspecified
    let first : Msg := { id := m.nextMsg, bytes := cur, clock := plainClock m b o len, relClock := #[] }
    set { m with atomics := m.atomics.push { block := b, off := o, len, msgs := #[first] },
                 nextMsg := m.nextMsg + 1 }
    pure m.atomics.size

/-- The position of message `id` of `l`. -/
def ALoc.pos (l : ALoc) (id : Nat) : Option Nat := l.msgs.findIdx? (·.id == id)

/-- Message `p` of `l` has an RMW right after it that read it. -/
def ALoc.hasRmwAfter (l : ALoc) (p : Nat) : Bool :=
  match l.msgs[p + 1]?, l.msgs[p]? with
  | some x, some y => x.rmwOf == some y.id
  | _, _ => false

/-- The oldest position that the current thread can read at location `li`: the newest message
that happened before it, or that it read or wrote before. -/
def floorPos (m : Mem) (li : Nat) : Nat :=
  let l := m.atomics[li]!
  let c := m.clocks[m.current]!
  let hb := l.msgs.zipIdx.foldl (fun a (x, i) => if VClock.le x.clock c then Nat.max a i else a) 0
  let own := match m.seen.find? (fun (t, j, _) => t == m.current && j == li) with
    | some (_, _, id) => (l.pos id).getD 0
    | none => 0
  Nat.max hb own

/-- The positions that a read can read, newest first. `rmw`: only a message without an RMW after
it. -/
def readOpts (m : Mem) (li : Nat) (rmw : Bool) : Array Nat :=
  let l := m.atomics[li]!
  let n := l.msgs.size
  let f := floorPos m li
  ((Array.range (n - f)).map fun k => n - 1 - k).filter fun p => !rmw || !l.hasRmwAfter p

/-- The places (the index of the new message) that a write can take, the end first. -/
def writeSlots (m : Mem) (li : Nat) : Array Nat :=
  let l := m.atomics[li]!
  let n := l.msgs.size
  let f := floorPos m li
  ((Array.range (n - f)).map fun k => n - k).filter fun p => p == n || !l.hasRmwAfter (p - 1)

/-- The current thread has read or written message `id` of location `li`. -/
def observe (li id : Nat) : MemM Unit := modify fun m =>
  { m with seen := (m.seen.filter fun (t, j, _) => !(t == m.current && j == li)).push (m.current, li, id) }

/-- An acquire: the current thread adopts the clock `c`. -/
def acquireClock (c : VClock) : MemM Unit := modify fun m =>
  { m with clocks := m.clocks.set! m.current (VClock.merge (m.clocks[m.current]!) c) }

/-- Put `msg` at place `p` of location `li`; at the end it is also the block's bytes. -/
def insertMsg (li p : Nat) (msg : Msg) : MemM Unit := modify fun m =>
  let l := m.atomics[li]!
  let m := { m with atomics := m.atomics.set! li { l with msgs := l.msgs.insertIdxIfInBounds p msg },
                    nextMsg := m.nextMsg + 1 }
  if p == l.msgs.size then
    match m.blocks[l.block]? with
    | some blk => { m with blocks := m.blocks.set! l.block { blk with bytes := writeBytes blk.bytes l.off msg.bytes } }
    | none => m
  else m

/-- The options of an op at `p` (`MemM` run on a copy): `1` if the op throws first. -/
def optCount {α : Type} (x : MemM (Array α)) (m : Mem) : Nat :=
  match (x.run m).run with
  | some (.ok (a, _)) => a.size
  | _ => 1

/-- An atomic read of `n` bits at `p`: the access, the race record, the location, the options. -/
def loadPrep (n : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) (rmw : Bool) :
    MemM (Nat × Array Nat) := do
  let m ← get
  let (b, _, o) ← (if rmw then m.accessW p (intSize n) align else m.access p (intSize n) align)
  recordAccess b o (intSize n) (if rmw then .atomicWrite else .atomicRead)
  let li ← locIdx b o (intSize n)
  pure (li, readOpts (← get) li rmw)

def loadCount (n : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) : Mem → Nat :=
  optCount ((·.2) <$> loadPrep n ord align p false)

/-- `atomic_load`: option `c` of `loadCount`. -/
def atomicLoadAt {n : Nat} (c : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) :
    MemM (BitVec n) := do
  let (li, opts) ← loadPrep n ord align p false
  let some pos := opts[c]? | throw .illegal
  let msg := (← get).atomics[li]!.msgs[pos]!
  observe li msg.id
  if ord.isAcq then acquireClock msg.relClock
  intOfBytes n msg.bytes

def storePrep (n : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) : MemM (Nat × Array Nat) := do
  let (b, _, o) ← (← get).accessW p (intSize n) align
  recordAccess b o (intSize n) .atomicWrite
  let li ← locIdx b o (intSize n)
  pure (li, writeSlots (← get) li)

def storeCount (n : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) : Mem → Nat :=
  optCount ((·.2) <$> storePrep n ord align p)

/-- `atomic_store_*`: place `c` of `storeCount`. -/
def atomicStoreAt {n : Nat} (c : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) (v : BitVec n) :
    MemM Unit := do
  let (li, slots) ← storePrep n ord align p
  let some slot := slots[c]? | throw .illegal
  let m ← get
  let cl := m.clocks[m.current]!
  let id := m.nextMsg
  let msg : Msg :=
    { id := id, bytes := padTo (intSize n) (intBytes v), clock := cl,
      relClock := (if ord.isRel then cl else #[]), writer := some m.current }
  insertMsg li slot msg
  observe li id

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

def rmwCount (n : Nat) (ord : AtomicOrder) (align : Nat) (p : Ptr) : Mem → Nat :=
  optCount ((·.2) <$> loadPrep n ord align p true)

/-- An RMW that read message `pos` of location `li`: the new message right after it, in the
release sequence of the message it read. -/
def rmwWrite {n : Nat} (li pos : Nat) (ord : AtomicOrder) (rd : Msg) (new : BitVec n) : MemM Unit := do
  if ord.isAcq then acquireClock rd.relClock
  let m ← get
  let cl := m.clocks[m.current]!
  let id := m.nextMsg
  let msg : Msg :=
    { id := id, bytes := padTo (intSize n) (intBytes new), clock := cl,
      relClock := (if ord.isRel then VClock.merge rd.relClock cl else rd.relClock), rmwOf := some rd.id,
      writer := some m.current }
  insertMsg li (pos + 1) msg
  observe li id

/-- `atomic_rmw`: option `c` of `rmwCount`. Returns the value before the op. -/
def atomicRmwAt {n : Nat} (c : Nat) (op : RmwOp) (signed : Bool) (ord : AtomicOrder) (align : Nat)
    (p : Ptr) (v : BitVec n) : MemM (BitVec n) := do
  let (li, opts) ← loadPrep n ord align p true
  let some pos := opts[c]? | throw .illegal
  let rd := (← get).atomics[li]!.msgs[pos]!
  let old ← intOfBytes n rd.bytes
  rmwWrite li pos ord rd (op.apply signed old v)
  pure old

/-- Shared CAS preparation: writable access, exactly one atomic-read footprint, the location,
and its complete readable positions. Strong and weak operations filter this same array. -/
def casReadPrep (n align : Nat) (p : Ptr) : MemM (Nat × Array Nat) := do
  let (b, _, o) ← (← get).accessW p (intSize n) align
  recordAccess b o (intSize n) .atomicRead
  let li ← locIdx b o (intSize n)
  pure (li, readOpts (← get) li false)

/-- Success-capable strong choices from a prepared readable array. -/
def casStrongOpts {n : Nat} (m : Mem) (li : Nat) (expected : BitVec n)
    (readable : Array Nat) : Array Nat :=
  readable.filter fun pos =>
    !((m.atomics[li]!).hasRmwAfter pos &&
      match (intOfBytes n (m.atomics[li]!).msgs[pos]!.bytes).run with
      | some (.ok v) => v == expected
      | _ => false)

/-- A strong `cmpxchg` reads a message; one with the value `expected` must be one without an RMW
after it (the write goes right after it). -/
def casPrep (n : Nat) (align : Nat) (p : Ptr) (expected : BitVec n) :
    MemM (Nat × Array Nat) := do
  let (li, readable) ← casReadPrep n align p
  pure (li, casStrongOpts (← get) li expected readable)

/-- A successful CAS also writes. The scheduler cannot run another thread between its read
preparation and this write access; both footprints belong to the same atomic operation. -/
def casMarkWrite (n align : Nat) (p : Ptr) : MemM Unit := do
  let (b, _, o) ← (← get).accessW p (intSize n) align
  recordAccess b o (intSize n) .atomicWrite

def casCount (n : Nat) (succ : AtomicOrder) (align : Nat) (p : Ptr) (expected : BitVec n) : Mem → Nat :=
  optCount ((·.2) <$> casPrep n align p expected)

/-- `cmpxchg_strong`: option `c` of `casCount`. It never fails
spuriously. `none` on success (the store happened), `some` of the value read on failure. -/
def cmpxchgAt {n : Nat} (c : Nat) (succ fail : AtomicOrder) (align : Nat) (p : Ptr)
    (expected new : BitVec n) : MemM (Option (BitVec n)) := do
  let (li, opts) ← casPrep n align p expected
  let some pos := opts[c]? | throw .illegal
  let rd := (← get).atomics[li]!.msgs[pos]!
  let old ← intOfBytes n rd.bytes
  if old = expected then
    casMarkWrite n align p
    rmwWrite li pos succ rd new
    pure none
  else
    observe li rd.id
    if fail.isAcq then acquireClock rd.relClock
    pure (some old)

/-- Internal builder. The operation supplies the array returned by `casReadPrep` on this same
prepared memory; arbitrary caller-supplied positions are not a model operation. -/
private def weakCasOptsFromReads {n : Nat} (m : Mem) (li : Nat) (expected : BitVec n)
    (strong readable : Array Nat) : Array (Nat × Bool) :=
  strong.map (fun pos => (pos, false)) ++
    (readable.filter fun pos =>
      match (intOfBytes n m.atomics[li]!.msgs[pos]!.bytes).run with
      | some (.ok v) => v == expected
      | _ => false).map (fun pos => (pos, true))

/-- Weak choices keep the strong choices first, then add a forced failure for every
readable message equal to `expected`. A failed read may observe a predecessor already consumed
by an RMW: the restriction on successful RMW insertion does not apply to that read. -/
def weakCasOpts {n : Nat} (m : Mem) (li : Nat) (expected : BitVec n)
    (strong : Array Nat) : Array (Nat × Bool) :=
  weakCasOptsFromReads m li expected strong (readOpts m li false)

theorem weakCasOpts_eq {n : Nat} (m : Mem) (li : Nat) (expected : BitVec n)
    (strong : Array Nat) :
    weakCasOpts m li expected strong = strong.map (fun pos => (pos, false)) ++
      ((readOpts m li false).filter fun pos =>
        match (intOfBytes n m.atomics[li]!.msgs[pos]!.bytes).run with
        | some (.ok v) => v == expected
        | _ => false).map (fun pos => (pos, true)) := rfl

/-- Prepare exactly one atomic-read footprint. Reuse every prepared readable position for
both the ordinary strong choices and the additional forced read-only matching failures. -/
def weakCasPrep (n align : Nat) (p : Ptr) (expected : BitVec n) :
    MemM (Nat × Array (Nat × Bool)) := do
  let (li, readable) ← casReadPrep n align p
  let m ← get
  pure (li, weakCasOptsFromReads m li expected (casStrongOpts m li expected readable) readable)

def weakCasCount (n : Nat) (succ : AtomicOrder) (align : Nat) (p : Ptr)
    (expected : BitVec n) : Mem → Nat :=
  optCount ((·.2) <$> weakCasPrep n align p expected)

/-- `cmpxchg_weak`: `some expected` is a permitted spurious failure. Failure observes the
read message using only `fail`, without an atomic-write footprint, new message or RMW edge.
The oracle may always choose failure: no fairness or eventual-success claim is made. -/
def cmpxchgWeakAt {n : Nat} (c : Nat) (succ fail : AtomicOrder) (align : Nat) (p : Ptr)
    (expected new : BitVec n) : MemM (Option (BitVec n)) := do
  let (li, opts) ← weakCasPrep n align p expected
  let some (pos, spurious) := opts[c]? | throw .illegal
  let rd := (← get).atomics[li]!.msgs[pos]!
  let old ← intOfBytes n rd.bytes
  if old = expected ∧ spurious = false then
    casMarkWrite n align p
    rmwWrite li pos succ rd new
    pure none
  else
    observe li rd.id
    if fail.isAcq then acquireClock rd.relClock
    pure (some old)

/-! ### Atomics on an enum or a `bool`

The integer op on the value's bits (`Zig.Packed`: an enum is its tag integer). A load decodes
with `Packed.ofBits?`: a tag value without a name of an exhaustive enum is `.illegal`, as for any
enum load. Zig allows only `Xchg` of the RMW ops on these types. -/

def atomicLoadAs (α : Type) {n : Nat} [Packed α n] (c : Nat) (ord : AtomicOrder) (align : Nat)
    (p : Ptr) : MemM α := do
  let b ← atomicLoadAt (n := n) c ord align p
  StateT.lift (Packed.ofBits? b)

def atomicStoreAs {α : Type} {n : Nat} [Packed α n] (c : Nat) (ord : AtomicOrder) (align : Nat)
    (p : Ptr) (v : α) : MemM Unit :=
  atomicStoreAt c ord align p (Packed.toBits v)

def atomicRmwAs {α : Type} {n : Nat} [Packed α n] (c : Nat) (op : RmwOp) (ord : AtomicOrder)
    (align : Nat) (p : Ptr) (v : α) : MemM α := do
  let b ← atomicRmwAt c op false ord align p (Packed.toBits v)
  StateT.lift (Packed.ofBits? b)

def cmpxchgAs {α : Type} {n : Nat} [Packed α n] (c : Nat) (succ fail : AtomicOrder) (align : Nat)
    (p : Ptr) (expected new : α) : MemM (Option α) := do
  match ← cmpxchgAt c succ fail align p (Packed.toBits expected) (Packed.toBits new) with
  | none => pure none
  | some b => some <$> StateT.lift (Packed.ofBits? b)

def cmpxchgWeakAs {α : Type} {n : Nat} [Packed α n] (c : Nat) (succ fail : AtomicOrder)
    (align : Nat) (p : Ptr) (expected new : α) : MemM (Option α) := do
  match ← cmpxchgWeakAt c succ fail align p (Packed.toBits expected) (Packed.toBits new) with
  | none => pure none
  | some b => some <$> StateT.lift (Packed.ofBits? b)

/-! ## Fork-join threads -/

namespace Thread

/-- `.illegal`: thread `t` finished without consuming (joining or detaching) every handle that
it owns: every thread that `t` itself spawned, or whose handle was transferred to it.
`spawn` checks it for each spawned thread; for the main thread (`t = 0`), the caller of the
top-level function checks it when the main thread ends (`ZigLean/Conc/Sched.lean`, `docs/std-models.md`
§Thread model). -/
def checkJoinedByChild (t : ThreadId) : MemM Unit := do
  let m ← get
  if m.threads.any (fun r => r.spawner == t && !r.joined) then throw .illegal

/-- The bookkeeping of a spawn: a new thread, spawned by the current one, whose clock is the
spawner's clock after a bump (the fork edge of the happens-before order). The current thread
does not change. `gated`: the record of a deferred task (`forkGated`). -/
def forkWith (gated : Bool) : MemM ThreadId := do
  let m ← get
  let parent := m.current
  let parentClock := VClock.bump (m.clocks[parent]!) parent
  let child := m.threads.size
  set { m with
    clocks := (m.clocks.set! parent parentClock).push parentClock
    threads := m.threads.push { spawner := parent, joined := false, gated } }
  pure child

/-- `Thread.spawn`'s bookkeeping (`forkWith`). -/
def fork : MemM ThreadId := forkWith false

/-- A spawn whose thread does not start yet (`SyncOp.spawnGated`, a deferred `Io.Group.async`
task): `fork`, with a gated record. Once its group records it, it waits until the group's
`groupTake` (`Mem.isGated`). -/
def forkGated : MemM ThreadId := forkWith true

/-- A join handle exists, was spawned by the caller, has not already been joined and is not a
deferred task that its group has not released (`Mem.isGated`). The scheduler uses the same
validation to reject invalid handles before waiting. -/
def joinValid (m : Mem) (caller tid : ThreadId) : Bool :=
  match m.threads[tid]? with
  | some rec => rec.spawner == caller && !rec.joined && !m.isGated tid
  | none => false

/-- `std.Thread.join`: the thread running this join must own the handle `tid` (its spawner, or
the thread it was transferred to, `transferHandle`), and the handle must not be consumed yet — a
handle joined by anyone else, joined twice or joined after `detach` throws `.illegal`. Merges the
joined thread's clock into the caller's (the join edge of the happens-before order) and bumps
the caller's own clock. -/
def join (tid : ThreadId) : MemM Unit := do
  let m ← get
  let some rec := m.threads[tid]?
    | throw .illegal
  if rec.spawner != m.current || rec.joined || m.isGated tid then throw .illegal
  let callerClock := VClock.bump (m.clocks[m.current]!) m.current
  let merged := VClock.merge callerClock (m.clocks[tid]!)
  set { m with
    clocks := m.clocks.set! m.current merged
    threads := m.threads.set! tid { rec with joined := true } }

/-- `std.Thread.detach` (C07): the owner of the handle `tid` releases its obligation to join
it. The thread goes on running independently of its parent; the parent may end, and its stack
frame die, while the thread runs (`ZigLean/Conc/Detach.lean`). The handle is consumed: the record
is marked `joined` (so `checkJoinedByChild` no longer asks for a join), and a later `join` or
`detach` of it throws `.illegal`, as `std` makes it undefined behavior ("Once called, this
consumes the Thread object"). No happens-before edge: the clocks do not change. A detach by a
thread that does not own the handle, or of a consumed, unknown or gated (`Mem.isGated`) handle,
throws `.illegal` (`joinValid`). -/
def detach (tid : ThreadId) : MemM Unit := do
  let m ← get
  let some rec := m.threads[tid]?
    | throw .illegal
  if rec.spawner != m.current || rec.joined || m.isGated tid then throw .illegal
  set { m with threads := m.threads.set! tid { rec with joined := true } }

/-- An explicit transfer of the join handle `tid` to the thread `owner` (C07): a model step that
a proof or a hand-written client inserts where a handle is passed to another thread (a spawn
argument or a store). `std.Thread` has no such call; the translator does not emit it, so a
translated thread that joins a handle it did not spawn is `.illegal` (conservative). The caller
must own the unconsumed handle; `owner` must be an existing thread other than `tid` itself.
Afterwards exactly `owner` may join or detach `tid`, and `owner` must do so before it ends
(`checkJoinedByChild owner`); the caller lost the right. No happens-before edge. Known limit:
the model does not know whether `owner` has already ended; a transfer to a thread that ended
leaves the handle with an owner that never consumes it, and no end check reports that (the
handle's thread is then neither joined nor waited for; no memory access is affected). -/
def transferHandle (tid owner : ThreadId) : MemM Unit := do
  let m ← get
  let some rec := m.threads[tid]?
    | throw .illegal
  if rec.spawner != m.current || rec.joined || m.isGated tid || owner == tid ||
      m.threads.size ≤ owner then
    throw .illegal
  set { m with threads := m.threads.set! tid { rec with spawner := owner } }

/-- The newest message of the atomic location at `(b, o)` is the current thread's and is not `0`
(`unfairOwnerCheck`). -/
def _root_.Zig.Mem.unfairHeld (m : Mem) (b o : Nat) : Bool :=
  match m.atomics.findIdx? (fun l => l.block == b && l.off == o) with
  | none => false
  | some i =>
    match m.atomics[i]?.bind (·.msgs.back?) with
    | none => false
    | some msg =>
      msg.writer == some m.current &&
        match (intOfBytes 32 msg.bytes).run with
        | some (.ok v) => v != 0
        | _ => false

/-- The owner check of `os_unfair_lock_unlock` at the lock word `p` (macOS terminates the process
on an unlock by a thread that does not hold the lock): the word's newest message is the current
thread's (`Msg.writer`) and is not `0`. While a thread holds an `os_unfair_lock`, the newest
message is its successful acquire (`cmpxchg 0 → 1`): the other threads only read the word, so a
waiter never makes the holder's unlock fail. Else `.illegal`: an unlock by another thread, a
double unlock, an unlock of a lock that was never locked. It changes nothing. -/
def unfairOwnerCheck (p : Ptr) : MemM Unit := do
  let m ← get
  let (b, _, o) ← m.access p 4 4
  if m.unfairHeld b o then pure () else throw .illegal

/-- `Io.Group`: the task `tid` belongs to the group at `g`. -/
def groupAdd (g : Ptr) (tid : ThreadId) : MemM Unit := modify fun m =>
  { m with groups := m.groups.push (g, tid) }

/-- `Io.Group`: the tasks of the group at `g`, in the order of their spawn; they leave the group,
which releases its deferred tasks (`forkGated`, `Mem.isGated`): they can start now. -/
def groupTake (g : Ptr) : MemM (Array ThreadId) := do
  let m ← get
  set { m with groups := m.groups.filter (·.1 != g) }
  pure ((m.groups.filter (·.1 == g)).map (·.2))

/-! ## Cancelation (`Io.Group.cancel`, 0.16.0; `docs/std-models.md` §Cancelation)

A cancelation request of an `Io` task stays in `Mem.cancels` until a cancelation point of the task
delivers it (`error.Canceled`). Thread 0 (`main`) is not an `Io` task: std's threaded `Io`
cancels only its worker threads (`Thread.current` is null elsewhere, `Io/Threaded.zig:1348`), so a
request is never pending for it. -/

/-- The current thread is an `Io` task (not `main`), so it can be canceled. -/
def isTask : MemM Bool := do
  pure ((← get).current != 0)

/-- The current thread has a cancelation request that no cancelation point delivered. -/
def cancelPending : MemM Bool := do
  let m ← get
  pure (m.current != 0 && m.cancels.contains m.current)

/-- A cancelation point delivers the current thread's request: `error.Canceled`. -/
def takeCancel : MemM Unit := modify fun m => { m with cancels := m.cancels.erase m.current }

/-- `Io.Group.cancel`: a cancelation request for each task in `tids`. A task that sleeps at a
futex wakes: a cancelable wait is interrupted (std signals the blocked syscall); for an
uncancelable wait this is a spurious return, which the futex API permits. -/
def requestCancel (tids : Array ThreadId) : MemM Unit := modify fun m =>
  { m with cancels := m.cancels ++ tids.filter (· != 0),
           waiters := m.waiters.filter (fun w => !tids.contains w.1),
           woken := m.woken ++ (m.waiters.filter (fun w => tids.contains w.1)).map (·.1) }

/-- The requests of the joined tasks `tids` end with them. -/
def dropCancels (tids : Array ThreadId) : MemM Unit := modify fun m =>
  { m with cancels := m.cancels.filter (fun u => !tids.contains u) }

/-! ## Futex (the kernel's part of `Io.futexWait`/`futexWake`)

The scheduler (`ZigLean/Conc/Sched.lean`) calls these at a `wait`/`wake` sync op. The queue is in
`Mem` (`Mem.waiters`, `Mem.woken`), as the thread table is: so the invariant of a proof over all
schedules (`ZigLean/Conc/Logic.lean`) can name it. -/

/-- A futex wait of the current thread at `p` for the value `e`: `true` if the thread sleeps
(it is added to `waiters`). A woken thread goes on. Else the kernel compares the `u32` at `p`,
the newest write (the block's bytes): the thread sleeps if it is `e`, else it goes on. The
kernel's compare is an atomic read of the word (`recordAccess … .atomicRead`): a plain write
that races with it is `.illegal`. -/
def futexWait (p : Ptr) (e : BitVec 32) : MemM Bool := do
  let m ← get
  if m.woken.contains m.current then
    set { m with woken := m.woken.erase m.current }
    pure false
  else
    let (b, blk, o) ← m.access p 4 4
    recordAccess b o 4 .atomicRead
    let m ← get
    let v ← intOfBytes 32 (blk.bytes.extract o (o + 4))
    if v = e then
      set { m with waiters := m.waiters.push (m.current, p) }
      pure true
    else pure false

/-- `n` of the threads `ws` (the waiters at one futex, in queue order) that a wake wakes: each
choice of `cs` picks one of those not picked yet (`c % count`; a missing choice picks the first).
No order is promised by Linux or darwin, so the choices are the oracle's (`Sched`). -/
def wakePick : Nat → List ThreadId → List Nat → List ThreadId
  | 0, _, _ => []
  | _, [], _ => []
  | n + 1, w :: ws, cs =>
    let i := cs.headD 0 % (ws.length + 1)
    (w :: ws)[i]'(Nat.mod_lt _ (Nat.succ_pos _)) :: wakePick n ((w :: ws).eraseIdx i) cs.tail

/-- The waiters that a wake of up to `n` waiters at `p` wakes, picked by the choices `cs`. -/
def wakeSet (ws : Array (ThreadId × Ptr)) (p : Ptr) (n : Nat) (cs : List Nat) : Array ThreadId :=
  (wakePick n ((ws.filter (·.2 == p)).toList.map (·.1)) cs).toArray

/-- A futex wake at `p`: up to `n` of the waiters at `p` are woken, the ones that the choices
`cs` pick (`wakeSet`; the scheduler takes them from the oracle). No happens-before edge (the std
code reads the value again with an acquire). -/
def futexWake (p : Ptr) (n : Nat) (cs : List Nat) : MemM Unit := modify fun m =>
  let woke := wakeSet m.waiters p n cs
  { m with waiters := m.waiters.filter (fun w => !woke.contains w.1), woken := m.woken ++ woke }

/-- The number of waiters at `p`. -/
def waitersAt (ws : Array (ThreadId × Ptr)) (p : Ptr) : Nat := (ws.filter (·.2 == p)).size

theorem wakePick_mem : ∀ {n : Nat} {l : List ThreadId} {cs : List Nat} {u : ThreadId},
    u ∈ wakePick n l cs → u ∈ l
  | 0, _, _, _, h => by simp [wakePick] at h
  | _ + 1, [], _, _, h => by simp [wakePick] at h
  | n + 1, w :: ws, cs, u, h => by
    simp only [wakePick, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.getElem_mem _
    · exact List.mem_of_mem_eraseIdx (wakePick_mem h)

theorem wakePick_ne_nil {n : Nat} {l : List ThreadId} {cs : List Nat} (hn : 0 < n)
    (hl : l ≠ []) : wakePick n l cs ≠ [] := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  obtain ⟨w, ws, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp [wakePick]

/-- A woken thread waited at `p`. -/
theorem mem_wakeSet {ws : Array (ThreadId × Ptr)} {p : Ptr} {n : Nat} {cs : List Nat}
    {u : ThreadId} (h : u ∈ wakeSet ws p n cs) : ∃ w ∈ ws, w.2 = p ∧ w.1 = u := by
  unfold wakeSet at h
  have := wakePick_mem (List.mem_toArray.mp h)
  simp only [List.mem_map, Array.mem_toList_iff, Array.mem_filter, beq_iff_eq] at this
  obtain ⟨w, ⟨hw, hp⟩, rfl⟩ := this
  exact ⟨w, hw, hp, rfl⟩

/-- A wake of at least one waiter at `p`, where one waits, wakes one. -/
theorem wakeSet_nonempty {ws : Array (ThreadId × Ptr)} {p : Ptr} {n : Nat} {cs : List Nat}
    (hn : 0 < n) (hw : ∃ w ∈ ws, w.2 = p) : ∃ u, u ∈ wakeSet ws p n cs := by
  have hl : (ws.filter (·.2 == p)).toList.map (·.1) ≠ [] := by
    obtain ⟨w, hw, hp⟩ := hw
    intro h
    have : w.1 ∈ (ws.filter (·.2 == p)).toList.map (·.1) :=
      List.mem_map.mpr ⟨w, by simp [hw, hp], rfl⟩
    rw [h] at this; cases this
  obtain ⟨u, us, he⟩ := List.exists_cons_of_ne_nil (wakePick_ne_nil (cs := cs) hn hl)
  exact ⟨u, by unfold wakeSet; rw [he]; simp⟩

/-- A wake of at least one waiter at `p`, where every waiter at `p` is thread `u` and one waits,
wakes `u`. -/
theorem mem_wakeSet_of_all {ws : Array (ThreadId × Ptr)} {p : Ptr} {n : Nat} {cs : List Nat}
    {u : ThreadId} (hn : 0 < n) (hw : ∃ w ∈ ws, w.2 = p) (hall : ∀ w ∈ ws, w.2 = p → w.1 = u) :
    u ∈ wakeSet ws p n cs := by
  obtain ⟨v, hv⟩ := wakeSet_nonempty (cs := cs) hn hw
  obtain ⟨w, hw', hp, rfl⟩ := mem_wakeSet hv
  rw [← hall w hw' hp]; exact hv

end Thread
end Zig
