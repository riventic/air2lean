import ZigLean.Sep.RawAlloc
open Zig

/-! Executable regressions for sentinel reallocation and the raw allocator contracts. Run with
`lake env lean --run tests/roadmap/sentinel-realloc/Check.lean`; any failed assertion exits
nonzero. -/

private def require (ok : Bool) (what : String) : IO Unit :=
  unless ok do throw (IO.userError s!"sentinel-realloc check failed: {what}")

private def result (f : MemM α) (m : Mem := {}) := (f.run m).run

private def blockOf (m : Mem) (p : Ptr) : Option Block := p.block.bind (m.blocks[·]?)

private def illegal (f : MemM α) (m : Mem := {}) : Bool := match result f m with
  | some (.error .illegal) => true
  | _ => false

/-- A one-byte frame, then `ab` with sentinel 0, reallocated to `n` under `mode`. -/
private def grow (n : BitVec 64) : MemM (Ptr × Slice × Except ErrName Slice) := do
  let frame ← match ← Allocator.alloc {} 1 1 1 with
    | .ok f => pure f.ptr | .error _ => throw .illegal
  store 1 frame (41#8)
  let s ← match ← Allocator.allocSentinel {} 2 0 with
    | .ok s => pure s | .error _ => throw .illegal
  store 1 s.ptr (0x61#8)
  store 1 (s.ptr.add 1) (0x62#8)
  let r ← Allocator.reallocSentinel {} s n 0
  pure (frame, s, r)

private def checkGrow (mode : ByteRemapMode) (failures : List Nat := []) : IO Unit := do
  let m0 : Mem := { allocPolicy := { byteRemap := mode, failures } }
  match result (grow 4) m0 with
  | some (.ok ((frame, s, r), m)) =>
    require ((blockOf m frame).map (·.bytes) == some #[.int 41]) s!"{repr mode}: frame"
    match r with
    | .ok g =>
      let some blk := blockOf m g.ptr | throw (IO.userError "no block")
      -- Payload, retained old sentinel byte, undefined growth, new sentinel at the new length.
      require (g.len == 4 && blk.live &&
        blk.bytes == #[.int 0x61, .int 0x62, .int 0, .undef, .int 0]) s!"{repr mode}: grown bytes"
      require ((mode == .inPlace) == (g.ptr == s.ptr)) s!"{repr mode}: in place iff policy"
      unless g.ptr == s.ptr do
        require (!((blockOf m s.ptr).map (·.live)).getD true) s!"{repr mode}: old block freed"
      -- Release of the whole buffer, including its sentinel, leaves only the frame.
      match result (Allocator.freeSentinel {} 1 g) m with
      | some (.ok ((), m')) =>
        require ((m'.blocks.filter (·.live)).size == 1) s!"{repr mode}: whole release"
      | _ => throw (IO.userError "release failed")
      -- Releasing only the payload of the reallocated buffer is illegal.
      require (illegal (Allocator.free {} 1 g) m) s!"{repr mode}: payload-only free"
    | .error e =>
      require (!failures.isEmpty && e == "OutOfMemory") s!"{repr mode}: unexpected failure"
      let some blk := blockOf m s.ptr | throw (IO.userError "no block")
      require (blk.live && blk.bytes == #[.int 0x61, .int 0x62, .int 0])
        s!"{repr mode}: failure keeps the original bytes and sentinel"
  | some (.error e) => throw (IO.userError s!"{repr mode}: grow errored: {repr e}")
  | none => throw (IO.userError s!"{repr mode}: grow did not return")

/-- Reallocating the payload without its sentinel byte is not a whole-block request. -/
private def payloadOnly : MemM Unit := do
  match ← Allocator.allocSentinel {} 3 0 with
  | .error _ => pure ()
  | .ok s => let _ ← Allocator.realloc {} s 5; pure ()

/-- A fresh 8-byte block with alignment 8, then `f`. -/
private def withBlock (f : Ptr → MemM α) : MemM α := do
  let some p ← vtableAlloc {} 8 8 | throw .illegal
  f p

def main : IO Unit := do
  checkGrow .fail
  checkGrow .inPlace
  checkGrow .move
  checkGrow .fail [2]
  checkGrow .inPlace [2]
  -- Overflow of n + 1 panics before any allocator decision.
  match result (do
      let s ← match ← Allocator.allocSentinel {} 1 0 with
        | .ok s => pure s | .error _ => throw .illegal
      Allocator.reallocSentinel {} s (BitVec.ofNat 64 (2 ^ 64 - 1)) 0) with
  | some (.error .panic) => pure ()
  | _ => throw (IO.userError "overflow must panic")
  require (illegal payloadOnly) "payload-only realloc"
  -- Raw preconditions: alignment a power of two ≤ 2^63, nonzero size, matching whole block.
  require (illegal (vtableAlloc {} 8 3)) "non-power-of-two alignment"
  require (illegal (vtableAlloc {} 8 0)) "zero alignment"
  require (illegal (vtableAlloc {} 8 (2 ^ 64))) "alignment above 2^63"
  require (illegal (vtableAlloc {} 0 8)) "zero length"
  require (illegal (withBlock fun p => vtableFree {} ⟨p, 8⟩ 16)) "free with another alignment"
  require (illegal (withBlock fun p => vtableFree {} ⟨p, 4⟩ 8)) "partial free"
  require (illegal (withBlock fun p => vtableFree {} ⟨p.add 1, 7⟩ 8)) "inner free"
  require (illegal (withBlock fun p => vtableResize {} ⟨p, 8⟩ 8 0)) "zero resize"
  require (illegal (withBlock fun p => vtableRemap {} ⟨p, 8⟩ 4 16)) "remap with another alignment"
  require (match result (withBlock fun p => vtableRemap {} ⟨p, 8⟩ 8 16) with
    | some (.ok (none, _)) => true | _ => false) "default remap fails without change"
  -- Under `move`, resize never moves (false), remap moves to an aligned fresh block.
  let moveCycle : MemM Bool := do
    let some p ← vtableAlloc {} 8 16 | pure false
    let r ← vtableResize {} ⟨p, 8⟩ 16 4
    let some q ← vtableRemap {} ⟨p, 8⟩ 16 12 | pure false
    let m ← get
    let ok := !r && q != p && (blockOf m q).any (fun b => b.addr % 16 == 0 && b.bytes.size == 12)
    vtableFree {} ⟨q, 12⟩ 16
    pure ok
  require (match result moveCycle { allocPolicy := { byteRemap := .move } } with
    | some (.ok (true, m)) => m.blocks.all (!·.live) | _ => false) "move policy remap"
  -- Under `inPlace`, shrink and latest-block growth keep the pointer and address.
  let inPlaceCycle : MemM Bool := do
    let some p ← vtableAlloc {} 8 16 | pure false
    let shrunk ← vtableResize {} ⟨p, 8⟩ 16 4
    let some q ← vtableRemap {} ⟨p, 4⟩ 16 12 | pure false
    vtableFree {} ⟨q, 12⟩ 16
    pure (shrunk && q == p)
  require (match result inPlaceCycle { allocPolicy := { byteRemap := .inPlace } } with
    | some (.ok (true, m)) => m.blocks.all (!·.live) | _ => false) "in-place resize/remap"
  IO.println "sentinel-realloc model checks passed: 5 policy/failure grows, overflow, payload-only, 12 raw contract checks"
