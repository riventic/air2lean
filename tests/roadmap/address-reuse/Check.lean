import ZigLean.Mem.Owned

/-! Executable regressions of the address-reuse policy and provenance recovery (M05,
`docs/address-reuse.md`). Run: `lake env lean --run tests/roadmap/address-reuse/Check.lean`. -/

open Zig

/-- The outcome of a run: the value, or the name of the error. -/
private def outcome {α : Type} [ToString α] (x : MemM α) (m : Mem) : String :=
  match ((x.run m).run : Option (Except Error (α × Mem))) with
  | some (.ok (v, _)) => s!"ok {v}"
  | some (.error .illegal) => "illegal"
  | some (.error .unspecified) => "unspecified"
  | some (.error _) => "other-error"
  | none => "diverges"

private def expect (name got want : String) : IO Unit := do
  unless got = want do throw (IO.userError s!"{name}: {got}, expected {want}")
  IO.println s!"{name}: {got}"

/-- A memory whose placement proposes `pick b` for block `b`, with provenance mode `pm`. -/
private def reuseMem (pick : BlockId → Option Nat) (pm : ProvenanceMode := .strict) : Mem :=
  { place := ⟨pick⟩, allocPolicy := { provenance := pm } }

private def addr (p : Ptr) : MemM Int := ptrAddr p

/-- Two heap blocks of 8 bytes, the first freed before the second: both addresses. -/
private def twoAddrs (k₁ k₂ : BlockKind) (freeFirst : Bool := true) : MemM (Int × Int) := do
  let p ← alloc k₁ 8 8
  if freeFirst then free p
  let q ← alloc k₂ 8 8
  pure (← addr p, ← addr q)

def main : IO Unit := do
  let at4096 : BlockId → Option Nat := fun b => if b = 1 then some 4096 else none
  -- The default policy keeps fresh addresses (unchanged behaviour).
  expect "default fresh" (outcome (twoAddrs .heap .heap false) {}) "ok (4096, 4112)"
  expect "default ignores freed address" (outcome (twoAddrs .heap .heap) {}) "ok (4096, 4112)"
  -- The opt-in policy reuses a freed heap block's address.
  expect "heap reuse" (outcome (twoAddrs .heap .heap) (reuseMem at4096)) "ok (4096, 4096)"
  -- A proposal is taken exactly when Zig allows it: not over a live block, aligned, nonzero.
  -- Adjacency and any order are allowed. Each invalid proposal falls back to a fresh address.
  expect "live overlap refused" (outcome (twoAddrs .heap .heap false) (reuseMem at4096))
    "ok (4096, 4112)"
  expect "adjacent accepted" (outcome (twoAddrs .heap .heap false)
    (reuseMem fun b => if b = 1 then some 4104 else none)) "ok (4096, 4104)"
  expect "overlap by one refused" (outcome (twoAddrs .heap .heap false)
    (reuseMem fun b => if b = 1 then some 4096 else none)) "ok (4096, 4112)"
  expect "below accepted" (outcome (twoAddrs .heap .heap false)
    (reuseMem fun b => if b = 0 then some 8192 else if b = 1 then some 64 else none))
    "ok (8192, 64)"
  expect "misaligned refused" (outcome (twoAddrs .heap .heap)
    (reuseMem fun b => if b = 1 then some 4097 else none)) "ok (4096, 4112)"
  expect "zero refused" (outcome (twoAddrs .heap .heap)
    (reuseMem fun b => if b = 1 then some 0 else none)) "ok (4096, 4112)"
  expect "far address accepted" (outcome (twoAddrs .heap .heap)
    (reuseMem fun b => if b = 1 then some 8192 else none)) "ok (4096, 8192)"
  expect "last 8 bytes accepted" (outcome (twoAddrs .heap .heap)
    (reuseMem fun b => if b = 1 then some (2 ^ 64 - 8) else none)) "ok (4096, 18446744073709551608)"
  expect "past 2^64 refused" (outcome (twoAddrs .heap .heap)
    (reuseMem fun b => if b = 1 then some (2 ^ 64) else none)) "ok (4096, 4112)"
  -- Stack blocks and globals are placed the same way (MM-1).
  expect "stack reuse" (outcome (twoAddrs .stack .stack) (reuseMem at4096)) "ok (4096, 4096)"
  -- An arena reuses a reset block's address under the policy (owned blocks).
  let arenaReset : MemM (Int × Int × Bool) := do
    let a ← Arena.init
    let s₁ ← match ← (AllocRef.owned a).alloc 1 8 8 with
      | .ok s => pure s | .error _ => throw .panic
    Owned.reset a
    let s₂ ← match ← (AllocRef.owned a).alloc 1 8 8 with
      | .ok s => pure s | .error _ => throw .panic
    pure (← addr s₁.ptr, ← addr s₂.ptr, s₁.ptr.block = s₂.ptr.block)
  expect "arena reset reuse" (outcome arenaReset (reuseMem at4096)) "ok (4096, (4096, false))"
  -- std.mem.Allocator: create, destroy, create again at the same address; the stale pointer
  -- is still dead (use after free, double free).
  let stdReuse (stale : Ptr → Ptr → MemM Unit) : MemM (Int × Int) := do
    let p ← match ← Allocator.create ⟨⟩ 8 8 with | .ok p => pure p | .error _ => throw .panic
    Allocator.destroy ⟨⟩ 8 p
    let q ← match ← Allocator.create ⟨⟩ 8 8 with | .ok p => pure p | .error _ => throw .panic
    store 8 q (7#64)
    stale p q
    pure (← addr p, ← addr q)
  expect "std reuse" (outcome (stdReuse fun _ _ => pure ()) (reuseMem at4096)) "ok (4096, 4096)"
  expect "std use after free" (outcome (stdReuse fun p _ => discard (load (BitVec 64) 8 p))
    (reuseMem at4096)) "illegal"
  expect "std double free" (outcome (stdReuse fun p _ => Allocator.destroy ⟨⟩ 8 p)
    (reuseMem at4096)) "illegal"
  expect "std new block live" (outcome (stdReuse fun _ q => discard (load (BitVec 64) 8 q))
    (reuseMem at4096)) "ok (4096, 4096)"
  -- @ptrFromInt of an address that a dead and a live block share.
  let fromInt (useOld : Bool) : MemM Nat := do
    let p ← alloc .heap 8 8
    let n ← addr p
    free p
    let q ← alloc .heap 8 8
    store 8 q (7#64)
    let nq ← addr q
    let r ← ptrFromAddr (if useOld then n else nq).toNat
    pure (← load (BitVec 64) 8 r).toNat
  expect "stale int strict" (outcome (fromInt true) (reuseMem at4096)) "unspecified"
  expect "fresh int strict" (outcome (fromInt false) (reuseMem at4096)) "unspecified"
  expect "stale int liveBlock" (outcome (fromInt true) (reuseMem at4096 .liveBlock)) "ok 7"
  expect "stale int fresh model" (outcome (fromInt true) {}) "illegal"
  expect "new int fresh model" (outcome (fromInt false) {}) "ok 7"
  -- One past a dead block that a live block's start shares: still ambiguous under strict.
  let onePast : MemM (Option BlockId) := do
    let p ← alloc .heap 4 4
    free p
    let _ ← alloc .heap 4 4
    pure (← ptrFromAddr ((← addr p) + 4).toNat).block
  expect "one-past shared strict" (outcome onePast (reuseMem fun b =>
    if b = 1 then some 4096 else none)) "unspecified"
  expect "one-past shared liveBlock" (outcome onePast (reuseMem (fun b =>
    if b = 1 then some 4096 else none) .liveBlock)) "ok (some 1)"
  -- The dead block alone still recovers its own (dangling) provenance.
  let deadAlone : MemM (Option BlockId) := do
    let p ← alloc .heap 8 8
    free p
    pure (← ptrFromAddr (← addr p).toNat).block
  expect "dead block alone" (outcome deadAlone (reuseMem at4096)) "ok (some 0)"
  IO.println "address-reuse regressions passed"
