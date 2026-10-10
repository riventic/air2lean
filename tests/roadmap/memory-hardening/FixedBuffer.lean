import ZigLean

/-! MM-10 regression: a fixed-buffer allocation and its buffer.

Zig 0.16.0 ReleaseSafe (`var buf: [8]u8`, `FixedBufferAllocator.init(&buf)`, `p = create(u8)`,
`p.* = 7`, `buf[0] = 9`) prints `p.* == 9` and `p == &buf[0]`: the allocation is the buffer's
first byte. The model keeps an allocation in a block of its own, so before the fix it read 7.
`FixedBuffer.init` now takes the buffer's block: a direct access to the buffer is `.illegal`,
and a placement can give an allocation its native address inside the buffer. The runs are
evaluated (`#guard`). -/

open Zig

/-- The outcome of a run from the empty memory under the placement `σ`. -/
def outcome {α : Type} (σ : Placement) (r : MemM α) : Option (Except Error α) :=
  (r.run' { place := σ }).run

/-- An 8-byte stack buffer with a fixed-buffer allocator over it, and one `u8` from it. -/
def withAlloc {α : Type} (k : Ptr → Ptr → MemM α) : MemM α := do
  let buf ← allocStack 8 1
  let a ← FixedBuffer.init buf 8
  match ← AllocRef.create (.owned a) 1 1 with
  | .error _ => throw .panic
  | .ok p => k buf p

/-- The counterexample: write the allocation, then the buffer, read the allocation. -/
def aliasRun : MemM (BitVec 8) := withAlloc fun buf p => do
  store 1 p (7 : BitVec 8)
  store 1 buf (9 : BitVec 8)
  load (BitVec 8) 1 p

-- The direct write to the lent buffer is illegal (it was a silent 7, natively 9).
#guard outcome .fresh aliasRun = some (.error .illegal)

-- Reading the buffer, or freeing its block at the end of the frame, is illegal too.
#guard outcome .fresh (withAlloc fun buf _ => load (BitVec 8) 1 buf) = some (.error .illegal)
#guard outcome .fresh (withAlloc fun buf _ => free buf) = some (.error .illegal)

-- The allocation itself works.
#guard outcome .fresh (withAlloc fun _ p => do store 1 p (7 : BitVec 8); load (BitVec 8) 1 p) =
  some (.ok 7)

/-- The placement that puts block 1 (the allocation) at the address of block 0 (the buffer,
at 4096 by the fallback). -/
def native : Placement := ⟨fun b => if b = 1 then some 4096 else none⟩

-- With the buffer's block dead, the native address is a valid placement: `p == &buf[0]`.
-- (Before the fix the live buffer covered it, and the allocation went past the buffer.)
#guard outcome native (withAlloc fun buf p => do pure ((← ptrAddr p) == (← ptrAddr buf))) =
  some (.ok true)

-- The buffer stays lent after `reset`; the allocation is dead.
#guard outcome .fresh (do
  let buf ← allocStack 8 1
  let a ← FixedBuffer.init buf 8
  Owned.reset a
  load (BitVec 8) 1 buf) = some (.error .illegal)

-- A buffer must be live and writable; an empty one lends nothing and has no room.
#guard outcome .fresh (do let buf ← allocStack 4 1; FixedBuffer.init buf 8) =
  some (.error .illegal)
#guard outcome .fresh (do
  let a ← FixedBuffer.init ⟨none, 4096⟩ 0
  match ← AllocRef.create (.owned a) 1 1 with
  | .ok _ => pure false
  | .error e => pure (e == "OutOfMemory")) = some (.ok true)
