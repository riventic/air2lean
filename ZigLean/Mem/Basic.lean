import ZigLean.Basic

/-!
# Byte-level memory

A CompCert-style memory: a list of blocks, each an array of bytes. A pointer is a block and a
byte offset, so a pointer stored in memory keeps its block (`Byte.ptrFrag`). Blocks are never
removed: `free` marks a block dead, and every later access to it throws `.illegal`.

A function that uses memory (`docs/generated-code.md` §Memory) returns `Zig.MemM α`, and its
body runs in `Zig.MM σ ε`. A pure function keeps `Zig.Result α` and `Zig.M σ ε`.

Each block gets an address when it is allocated: the next free address, rounded up to the
block's alignment, with at least 1 byte between two blocks, so one past the end of a block is
never the start of the next one. The alignment check of an access uses this address.
-/

namespace Zig

abbrev BlockId := Nat

/-- A pointer: a block and a byte offset into it. `block = none`: a pointer without a block;
every access through it throws `.illegal`. -/
structure Ptr where
  block : Option BlockId
  off : Int
  deriving DecidableEq, Repr, Inhabited

/-- The pointer `n` bytes after `p` (`struct_field_ptr`). -/
@[inline] def Ptr.add (p : Ptr) (n : Int) : Ptr := { p with off := p.off + n }

/-- The pointer to item `i` after `p`, for items of `size` bytes (`ptr_add`, `ptr_elem_ptr`). -/
@[inline] def Ptr.elem (p : Ptr) (size : Nat) (i : BitVec 64) : Ptr := p.add (size * i.toNat)

/-- The pointer to item `i` before `p` (`ptr_sub`). -/
@[inline] def Ptr.elemSub (p : Ptr) (size : Nat) (i : BitVec 64) : Ptr := p.add (-(size * i.toNat))

/-- A slice `[]T`: the pointer to item 0, and the item count. -/
structure Slice where
  ptr : Ptr
  len : BitVec 64
  deriving DecidableEq, Repr, Inhabited

inductive Byte where
  | undef
  | int (b : BitVec 8)
  /-- Byte `i` (little-endian) of the 8-byte pointer `p`. -/
  | ptrFrag (p : Ptr) (i : Fin 8)
  deriving DecidableEq, Repr, Inhabited

inductive BlockKind where
  | stack
  | heap
  | global
  deriving DecidableEq, Repr

structure Block where
  bytes : Array Byte
  align : Nat
  kind : BlockKind
  live : Bool
  /-- The address of byte 0 (`@intFromPtr`). -/
  addr : Nat
  deriving Repr

/-! ## Threads (`ZigLean/Mem/Thread.lean`, `docs/std-models.md` §Thread model)

Fork-join only: `std.Thread.spawn`/`.join`. Thread 0 is the thread the top-level call runs on;
every other id is a spawned thread, in spawn order. `Mem.clocks`/`Mem.threads` are indexed by
`ThreadId` and always the same size. -/

abbrev ThreadId := Nat

/-- A Lamport vector clock: component `i` is how many of thread `i`'s own recorded accesses the
clock's owner has observed (its own, plus every other thread's up to the last fork/join edge
with it). -/
abbrev VClock := Array Nat

namespace VClock

def get (c : VClock) (i : ThreadId) : Nat := c.getD i 0

/-- Bump `t`'s own component: one more of `t`'s own accesses. -/
def bump (c : VClock) (t : ThreadId) : VClock :=
  let c := if t < c.size then c else c ++ Array.replicate (t + 1 - c.size) 0
  c.set! t (c.get t + 1)

/-- Component-wise max: what a thread adopts when it observes another (a join edge). -/
def merge (a b : VClock) : VClock :=
  (Array.range (Nat.max a.size b.size)).map fun i => Nat.max (a.get i) (b.get i)

/-- `a` happened-before-or-equal `b`: every component of `a` is `≤` the same component of `b`. -/
def le (a b : VClock) : Bool :=
  (Array.range (Nat.max a.size b.size)).all fun i => Nat.ble (a.get i) (b.get i)

/-- Neither happened-before the other: two accesses with concurrent clocks are a race candidate
if their byte ranges overlap (`recordAccess`). -/
def concurrent (a b : VClock) : Bool := !le a b && !le b a

end VClock

/-- `std.builtin.AtomicRmwOp` groups whose op commutes with itself, for the model's race check
(`docs/generated-code.md` §Atomics and threads). Never `Xchg` or `Nand` (they don't commute),
and never mixed groups. `Air2Lean/Memory.lean`'s `rmwResultUnused` and `Zig.RmwOp.group`
decide, per call site, whether a concrete unused-result RMW gets one of these. -/
inductive RmwGroup where
  | addSub | or | and | xor
  /-- `Min`/`Max` carry the signedness: a signed and an unsigned `Min` on the same bytes do not
  commute. -/
  | min (signed : Bool) | max (signed : Bool)
  deriving BEq, Repr, Inhabited

/-- One memory access, for the race check. `atomicWrite`'s `commute`: `some g` only for an
eligible, result-unused RMW (`RmwGroup`); a plain atomic store or a used-result RMW is
`atomicWrite none`. -/
inductive AccessKind where
  | read
  | write
  | atomicRead
  | atomicWrite (commute : Option RmwGroup)
  deriving Repr, Inhabited

def AccessKind.isWrite : AccessKind → Bool
  | .write | .atomicWrite _ => true
  | _ => false

/-- `none`: `a` and `b`, both touching the same bytes with concurrent clocks, do not race.
`some e`: they do, and `e` is the `Zig.Error` the later access throws (`docs/generated-code.md`
§Atomics and threads): a non-atomic write racing with anything is `.illegal`; any other pair
with a write that does not commute is `.nondet`. `sameRange`: `a` and `b` cover the same bytes. -/
def racePair (a b : AccessKind) (sameRange : Bool) : Option Error :=
  match a, b with
  | .read, .read | .read, .atomicRead | .atomicRead, .read | .atomicRead, .atomicRead => none
  -- Two RMWs of one group commute only on the same bytes (so the same width): a 1-byte and a
  -- 4-byte `Add` on overlapping bytes give different results in the two orders (the carry).
  | .atomicWrite (some g1), .atomicWrite (some g2) =>
    if g1 == g2 && sameRange then none else some .nondet
  | .write, _ | _, .write => some .illegal
  | _, _ => some .nondet

/-- Who spawned thread `id` (the parent thread's own `ThreadId` at the time), and whether
`Thread.join` has run on it. Index 0 (main) is unused: nothing ever joins it. -/
structure ThreadRec where
  spawner : ThreadId
  joined : Bool
  deriving Repr, Inhabited

/-- One recorded access, kept so a later overlapping access can check it for a race. -/
structure FootprintEntry where
  tid : ThreadId
  clock : VClock
  block : BlockId
  off : Nat
  len : Nat
  kind : AccessKind
  deriving Repr, Inhabited

structure Mem where
  blocks : Array Block := #[]
  /-- The lowest address that the next block can get. Never 0. -/
  nextAddr : Nat := 4096
  /-- The number of allocations so far (`Zig.rawAlloc`, `ZigLean/Mem/Alloc.lean`). -/
  allocs : Nat := 0
  /-- The allocation that fails: allocation number `failAt` (from 0), or none. -/
  failAt : Option Nat := none
  /-- The thread that is running right now. -/
  current : ThreadId := 0
  /-- `clocks[t]`: thread `t`'s own vector clock. Same size as `threads`. -/
  clocks : Array VClock := #[#[]]
  /-- `threads[t]`: bookkeeping for thread `t`, `t > 0` (`ZigLean/Mem/Thread.lean`). -/
  threads : Array ThreadRec := #[{ spawner := 0, joined := true }]
  /-- Every access recorded so far, across every thread. -/
  footprint : Array FootprintEntry := #[]
  deriving Repr, Inhabited

/-- The state of a function that uses memory. -/
abbrev MemM (α : Type) := StateT Mem Result α

/-- The body monad of a function that uses memory: its locals over `MemM`. -/
abbrev MM (σ α : Type) := StateT σ MemM α

/-- `n` rounded up to a multiple of `a` (`a = 0`: `n`). -/
def alignUp (n a : Nat) : Nat := if a = 0 then n else (n + a - 1) / a * a

/-- The block and the offset of an access of `n` bytes at `p` that needs alignment `align`.
Throws `.illegal` if the block is dead, the bytes are not all in the block, or the address is
not a multiple of `align`. -/
def Mem.access (m : Mem) (p : Ptr) (n align : Nat) : Result (BlockId × Block × Nat) :=
  match p.block with
  | none => throw .illegal
  | some b =>
    match m.blocks[b]? with
    | none => throw .illegal
    | some blk =>
      if blk.live ∧ 0 ≤ p.off ∧ p.off + n ≤ blk.bytes.size ∧ (blk.addr + p.off.toNat) % align = 0
      then pure (b, blk, p.off.toNat) else throw .illegal

/-- `a` with the bytes from offset `o` on replaced by `bs` (`o + bs.size ≤ a.size`). -/
def writeBytes (a : Array Byte) (o : Nat) (bs : Array Byte) : Array Byte :=
  a.extract 0 o ++ bs ++ a.extract (o + bs.size) a.size

/-- The race error of the first (chronologically earliest) footprint entry of `fp` that overlaps
`block`/`off`/`len` with a concurrent clock and does not commute with `kind` (`racePair`); `none`
if every overlapping concurrent entry commutes. `Array.findSome?` searches in order, so this
matches recording the accesses one at a time and stopping at the first conflict. -/
def raceAt (fp : Array FootprintEntry) (clock : VClock) (block : BlockId) (off len : Nat)
    (kind : AccessKind) : Option Error :=
  fp.findSome? fun e =>
    if e.block == block && off < e.off + e.len && e.off < off + len &&
        VClock.concurrent e.clock clock then racePair e.kind kind (e.off == off && e.len == len)
    else none

/-- Record one access at `block`/`off`/`len` by the current thread (`ZigLean/Mem/Thread.lean`),
checking it against every earlier overlapping access from a concurrent thread (`racePair`, via
`raceAt`). Throws the race's error before recording anything. -/
def recordAccess (block : BlockId) (off len : Nat) (kind : AccessKind) : MemM Unit := do
  let m ← get
  let t := m.current
  let clock := VClock.bump (m.clocks[t]!) t
  match raceAt m.footprint clock block off len kind with
  | some err => throw err
  | none =>
    set { m with
      clocks := m.clocks.set! t clock,
      footprint := m.footprint.push { tid := t, clock, block, off, len, kind } }

def loadBytes (p : Ptr) (n align : Nat) (kind : AccessKind := .read) : MemM (Array Byte) := do
  let (b, blk, o) ← (← get).access p n align
  recordAccess b o n kind
  pure (blk.bytes.extract o (o + n))

def storeBytes (p : Ptr) (align : Nat) (bs : Array Byte) (kind : AccessKind := .write) : MemM Unit := do
  let m ← get
  let (b, blk, o) ← m.access p bs.size align
  recordAccess b o bs.size kind
  let m ← get
  set { m with blocks := m.blocks.set! b { blk with bytes := writeBytes blk.bytes o bs } }

/-- A new block of `size` undefined bytes. -/
def alloc (kind : BlockKind) (size align : Nat) : MemM Ptr := do
  let m ← get
  let addr := alignUp m.nextAddr align
  set { m with
    blocks := m.blocks.push { bytes := Array.replicate size .undef, align, kind, live := true, addr }
    nextAddr := addr + size + 1 }
  pure ⟨some m.blocks.size, 0⟩

/-- Free the block that `p` points to the start of. A dead block or an inner pointer throws
`.illegal`. -/
def free (p : Ptr) : MemM Unit := do
  let m ← get
  match p.block with
  | none => throw .illegal
  | some b =>
    match m.blocks[b]? with
    | some blk =>
      if blk.live ∧ p.off = 0 then set { m with blocks := m.blocks.set! b { blk with live := false } }
      else throw .illegal
    | none => throw .illegal

/-- The stack block of a local whose address escapes: made at function entry. -/
@[inline] def allocStack (size align : Nat) : MemM Ptr := alloc .stack size align

/-! ## Typed access -/

/-- The memory encoding of a Lean type: its size and alignment in bytes (the Zig ABI values),
and the bytes of a value. `decode` throws `.unspecified` if a byte that the value uses is
undefined; padding bytes are ignored. -/
class Enc (α : Type) where
  size : Nat
  align : Nat
  encode : α → Array Byte
  decode : Array Byte → Result α

/-- `load`/`store` take the alignment of the pointer type (`*align(N) T`), which can differ from
the type's own alignment. -/
def load (α : Type) [Enc α] (align : Nat) (p : Ptr) : MemM α := do
  let bs ← loadBytes p (Enc.size α) align
  Enc.decode bs

def store {α : Type} [Enc α] (align : Nat) (p : Ptr) (v : α) : MemM Unit :=
  storeBytes p align (Enc.encode v)

/-- `is_non_null_ptr` for `?T`, `T` not a pointer: the flag byte after the payload. -/
def optIsSome (α : Type) [Enc α] (p : Ptr) : MemM Bool := do
  match ((← loadBytes (p.add (Enc.size α)) 1 1)[0]? : Option Byte) with
  | some (.int x) => if x = 0 then pure false else if x = 1 then pure true else throw .illegal
  | _ => throw .unspecified

/-- `optional_payload_ptr_set` for `?T`, `T` not a pointer: set the flag byte; the payload is at
offset 0. -/
def optSetSome (α : Type) [Enc α] (p : Ptr) : MemM Ptr := do
  storeBytes (p.add (Enc.size α)) 1 #[.int 1]
  pure p

/-- A store of `undefined`: every byte of the value becomes undefined. -/
def storeUndef (α : Type) [Enc α] (align : Nat) (p : Ptr) : MemM Unit :=
  storeBytes p align (Array.replicate (Enc.size α) .undef)

/-! ## Memory ops

`@memset`, `@memcpy` and `@memmove` do nothing for 0 items, also through a pointer that is not
valid. For more items, the access is checked before the bytes are made. -/

/-- `@memset`: each of the `n` items at `p` becomes `v`. `v = none`: `undefined`, every byte of
the items becomes undefined. -/
def memset {α : Type} [Enc α] (align : Nat) (p : Ptr) (n : BitVec 64) (v : Option α) :
    MemM Unit := do
  if n.toNat = 0 then return
  let _ ← (← get).access p (n.toNat * Enc.size α) align
  let item := match v with
    | some x => Enc.encode x
    | none => Array.replicate (Enc.size α) .undef
  storeBytes p align (Array.replicate n.toNat item).flatten

/-- `@memcpy` and `@memmove`: copy `n` items of `size` bytes from `src` to `dst`. All bytes are
read before the first write, so an overlap copies the old bytes (`@memmove`). For `@memcpy`, the
AIR checks before that the two ranges do not overlap. -/
def memmove (size dstAlign srcAlign : Nat) (dst src : Ptr) (n : BitVec 64) : MemM Unit := do
  if n.toNat = 0 then return
  let _ ← (← get).access dst (n.toNat * size) dstAlign
  let bs ← loadBytes src (n.toNat * size) srcAlign
  storeBytes dst dstAlign bs

/-- The items of `s`, for a call to a pure function with a `[]const T` parameter. An undefined
byte in any item throws `.unspecified`, also in an item that the function does not read. -/
def readSlice (α : Type) [Enc α] (align : Nat) (s : Slice) : MemM (Array α) := do
  if s.len.toNat = 0 then return #[]
  let bs ← loadBytes s.ptr (s.len.toNat * Enc.size α) align
  (Array.range s.len.toNat).mapM fun i =>
    (Enc.decode (bs.extract (i * Enc.size α) ((i + 1) * Enc.size α)) : Result α)

/-- The address of `p`: the address of its block plus the offset. A pointer without a block has
the address `p.off`. -/
def ptrAddr (p : Ptr) : MemM Int := do
  match p.block with
  | none => pure p.off
  | some b =>
    match (← get).blocks[b]? with
    | some blk => pure (blk.addr + p.off)
    | none => throw .illegal

/-- The pointer to address `n`: inside the block whose byte range covers `n`, at the matching
offset, or `⟨none, n⟩` if no block covers it (`@ptrFromInt`). A dead block still counts (its
`addr` does not change on `free`), so the pointer this returns can still be a dangling one; the
existing liveness check in `Mem.access` catches a later access through it. Round-trips with
`ptrAddr`: `ptrFromAddr (← ptrAddr p) = p` for `p` inside its block's bytes. -/
def ptrFromAddr (n : Nat) : MemM Ptr := do
  let m ← get
  match m.blocks.zipIdx.findSome? fun (blk, b) =>
      if blk.addr ≤ n ∧ n < blk.addr + blk.bytes.size then some (b, blk.addr) else none with
  | some (b, addr) => pure ⟨some b, (n : Int) - (addr : Int)⟩
  | none => pure ⟨none, n⟩

/-- `<`, `<=`, `>`, `>=` on pointers compare the addresses. Two blocks have the order of their
addresses in the model, which can differ from the compiled code. -/
def ptrLt (a b : Ptr) : MemM Bool := do pure (decide ((← ptrAddr a) < (← ptrAddr b)))
def ptrLe (a b : Ptr) : MemM Bool := do pure (decide ((← ptrAddr a) ≤ (← ptrAddr b)))

/-! ## Globals -/

/-- `m` with one more global block: `bytes` at the next free address, aligned to `align`. -/
def Mem.addGlobal (m : Mem) (bytes : Array Byte) (align : Nat) : Mem :=
  let addr := alignUp m.nextAddr align
  { blocks := m.blocks.push { bytes, align, kind := .global, live := true, addr }
    nextAddr := addr + bytes.size + 1 }

/-- The memory at program start: block `k` is global `k`, with its initial bytes and
alignment. -/
def Mem.ofGlobals (gs : List (Array Byte × Nat)) : Mem :=
  gs.foldl (fun m (bs, a) => m.addGlobal bs a) {}

/-! ## Calls -/

/-- A call from a function that uses memory to another one. -/
@[inline] def callM {σ α : Type} (r : MemM α) : MM σ α := StateT.lift r

/-- A call from a function that uses memory to a pure function. -/
@[inline] def callR {σ α : Type} (r : Result α) : MM σ α := StateT.lift (StateT.lift r)

section Monotone
open Lean.Order

/-- `callM` for `partial_fixpoint`, as `monotone_call` for `call` (`ZigLean/Basic.lean`). -/
@[partial_fixpoint_monotone]
theorem monotone_callM {σ α γ : Type} [PartialOrder γ]
    (f : γ → MemM α) (hmono : monotone f) :
    monotone (fun (x : γ) => (callM (f x) : MM σ α)) := by
  apply monotone_of_monotone_apply
  intro s
  show monotone (fun x => (f x) >>= fun a => pure (a, s))
  exact monotone_bind _ _ _ hmono (monotone_const _)

/-- `monotone_run'` (`ZigLean/Basic.lean`) for a function that uses memory. -/
@[partial_fixpoint_monotone]
theorem monotone_runMM' {σ α γ : Type} [PartialOrder γ]
    (f : γ → MM σ α) (hmono : monotone f) (s : σ) :
    monotone (fun (x : γ) => (f x).run' s) := by
  have h := Functor.monotone_map (fun x => StateT.run (f x) s) (·.1) (monotone_stateTRun f hmono s)
  simpa [StateT.run', StateT.run] using h

/-- `monotone_loop` (`ZigLean/Basic.lean`) for a function that uses memory. -/
@[partial_fixpoint_monotone]
theorem monotone_loopMM {σ ε γ : Type} [PartialOrder γ] (f : γ → MM σ ε) (again : ε → Bool)
    (hmono : monotone f) : monotone (fun (x : γ) => loop (f x) again) := by
  intro x1 x2 hx
  have hle : f x1 ⊑ f x2 := hmono x1 x2 hx
  apply loop.fixpoint_induct (f x1) again (motive := fun v => v ⊑ loop (f x2) again)
  · exact fun _ hc h => csup_le hc h
  · intro l hl
    rw [loop.eq_1 (f x2) again]
    apply PartialOrder.rel_trans (MonoBind.bind_mono_left hle)
    apply MonoBind.bind_mono_right
    intro e
    split
    · exact hl
    · exact PartialOrder.rel_refl

end Monotone

end Zig
