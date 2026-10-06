import ZigLean.Sep.Sentinel
open Zig
deriving instance DecidableEq for Except
private def good : MemM Bool := do
  match ← Allocator.allocSentinel {} 3 42 with
  | .error _ => pure false
  | .ok s =>
    let m ← get
    let some b := s.ptr.block | throw .illegal
    let some blk := m.blocks[b]? | throw .illegal
    if s.len != 3 || blk.bytes != #[.undef, .undef, .undef, .int 42] then throw .illegal
    store 1 s.ptr (17#8)
    let last ← load (BitVec 8) 1 (s.ptr.add 3)
    if last != 42 then throw .illegal
    Allocator.freeSentinel {} 1 s
    pure true
private def result (f : MemM α) (m : Mem := {}) := (f.run m).run
-- Kernel computation, without native_decide, detects both extra-byte and offset mutants.
example : (result good).map (fun r => r.map (fun (ok, m) => ok && m.blocks.all (fun b => !b.live))) =
    some (.ok true) := by decide +kernel
private def capFailure : Bool := match result (Allocator.allocSentinel {} 0 42)
    { allocPolicy := { maxBytes := 0 } } with
  | some (.ok (.error "OutOfMemory", m)) => m.allocs == 1 && m.blocks.isEmpty
  | _ => false
example : capFailure = true := by decide
private def illegalOrPanic (f : MemM α) (panic : Bool := false) : Bool := match result f with
  | some (.error e) => e == (if panic then .panic else .illegal)
  | _ => false
example : illegalOrPanic (Allocator.allocSentinel {} (BitVec.ofNat 64 (2^64-1)) 42) true = true := by decide
-- An allocation without its final byte is not a valid sentinel allocation.
private def shortBlock : MemM Unit := do
  let p ← alloc .heap 3 1
  store 1 (p.add 3) (42#8)
example : illegalOrPanic shortBlock = true := by decide +kernel
-- Whole-block free rejects a payload-only release.
private def shortFree : MemM Unit := do
  match ← Allocator.allocSentinel {} 3 42 with
  | .error _ => pure ()
  | .ok s => Allocator.free {} 1 s
example : illegalOrPanic shortFree = true := by decide +kernel
