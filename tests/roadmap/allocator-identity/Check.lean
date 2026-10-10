import ZigLean.Sep.ArenaClient

/-! Executable regressions of the allocator-identity model (`docs/allocator-identity.md`).
Run: `lake env lean --run tests/roadmap/allocator-identity/Check.lean`. -/

open Zig

/-- The outcome of a run: `ok`, or the name of the error. -/
private def outcome {α : Type} (r : Result (α × Mem)) : String :=
  match r.run with
  | some (.ok _) => "ok"
  | some (.error .illegal) => "illegal"
  | some (.error _) => "other-error"
  | none => "diverges"

private def expect (name got want : String) : IO Unit := do
  unless got = want do throw (IO.userError s!"{name}: {got}, expected {want}")
  IO.println s!"{name}: {got}"

private def slice! (r : Except ErrName Slice) : MemM Slice :=
  match r with
  | .ok s => pure s
  | .error _ => throw .panic

private def u8 (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

/-- A block of one allocator freed through another. -/
private def crossFree (src dst : Option Nat) : MemM Unit := do
  let a ← Arena.init
  let b ← Arena.init
  let ref : Option Nat → AllocRef := fun
    | none => .std
    | some 0 => .owned a
    | some _ => .owned b
  let s ← slice! (← (ref src).alloc 1 1 (u8 4))
  (ref dst).free 1 s

/-- A fixed buffer of 8 bytes: LIFO frees give bytes back, other frees do not. -/
private def fixedBufferLifo : MemM (List Bool) := do
  let r := AllocRef.owned (← FixedBuffer.init (← allocStack 8 1) 8)
  let x ← r.alloc 1 1 (u8 4)
  let y ← r.alloc 1 1 (u8 4)
  let z ← r.alloc 1 1 (u8 1)
  r.free 1 (← slice! y)
  let w ← r.alloc 1 1 (u8 4)
  r.free 1 (← slice! x)
  let v ← r.alloc 1 1 (u8 1)
  let ok : Except ErrName Slice → Bool := fun | .ok _ => true | .error _ => false
  pure [ok x, ok y, ok z, ok w, ok v]

/-- Arena reset: the arena's blocks die, a `std.mem.Allocator` block and another arena's
block stay. `use` selects the block read after the reset. -/
private def resetThenUse (use : Nat) : MemM Unit := do
  let a ← Arena.init
  let b ← Arena.init
  let sa ← slice! (← (AllocRef.owned a).alloc 1 1 (u8 4))
  let sb ← slice! (← (AllocRef.owned b).alloc 1 1 (u8 4))
  let sh ← slice! (← AllocRef.std.alloc 1 1 (u8 4))
  storeBytes sa.ptr 1 #[.int 1, .int 2, .int 3, .int 4]
  storeBytes sb.ptr 1 #[.int 5, .int 6, .int 7, .int 8]
  storeBytes sh.ptr 1 #[.int 9, .int 9, .int 9, .int 9]
  Owned.reset a
  let s := match use with | 0 => sa | 1 => sb | _ => sh
  let _ ← loadBytes s.ptr 4 1
  -- A reset arena allocates again.
  let _ ← slice! (← (AllocRef.owned a).alloc 1 1 (u8 4))

private def afterDeinit : MemM Unit := do
  let a ← Arena.init
  Arena.deinit a
  let _ ← (AllocRef.owned a).alloc 1 1 (u8 4)

private def arenaDoubleFree : MemM Unit := do
  let r := AllocRef.owned (← Arena.init)
  let s ← slice! (← r.alloc 1 1 (u8 4))
  r.free 1 s
  r.free 1 s

private def arenaRemapForeign : MemM Unit := do
  let a ← Arena.init
  let s ← slice! (← AllocRef.std.alloc 1 1 (u8 4))
  let _ ← (AllocRef.owned a).remap 1 s (u8 2)

private def stdRemapForeign : MemM Unit := do
  let a ← Arena.init
  let s ← slice! (← (AllocRef.owned a).alloc 1 1 (u8 4))
  let _ ← AllocRef.std.remap 1 s (u8 2)

def main : IO Unit := do
  expect "std-free-std" (outcome ((crossFree none none).run {})) "ok"
  expect "arena-free-own" (outcome ((crossFree (some 0) (some 0)).run {})) "ok"
  expect "arena-block-std-free" (outcome ((crossFree (some 0) none).run {})) "illegal"
  expect "std-block-arena-free" (outcome ((crossFree none (some 0)).run {})) "illegal"
  expect "arena-block-other-arena-free" (outcome ((crossFree (some 0) (some 1)).run {})) "illegal"
  expect "arena-double-free" (outcome (arenaDoubleFree.run {})) "illegal"
  expect "arena-remap-std-block" (outcome (arenaRemapForeign.run {})) "illegal"
  expect "std-remap-arena-block" (outcome (stdRemapForeign.run {})) "illegal"
  expect "reset-own-block" (outcome ((resetThenUse 0).run {})) "illegal"
  expect "reset-other-arena-block" (outcome ((resetThenUse 1).run {})) "ok"
  expect "reset-std-block" (outcome ((resetThenUse 2).run {})) "ok"
  expect "alloc-after-deinit" (outcome (afterDeinit.run {})) "illegal"
  match (fixedBufferLifo.run' {}).run with
  | some (.ok oks) => expect "fixed-buffer-lifo" (toString oks) "[true, true, false, true, false]"
  | _ => throw (IO.userError "fixed-buffer-lifo: no result")
  let reqs := [[#[1, 2], #[3]], [#[], #[250, 10]], [#[7]]]
  for (name, failures, want) in [("session", ([] : List Nat), "[ok 6, ok 260, ok 7]"),
      ("session-failures", [1, 3], "[error OutOfMemory, ok 260, error OutOfMemory]")] do
    let m : Mem := { allocPolicy := { failures } }
    match ((session reqs).run m).run with
    | some (.ok (rs, final)) =>
      let shown := rs.map fun | .ok n => s!"ok {n}" | .error e => s!"error {e}"
      expect name (toString shown) want
      unless final.blocks.all (fun b => !b.live) do throw (IO.userError s!"{name}: live block")
    | _ => throw (IO.userError s!"{name}: no result")
