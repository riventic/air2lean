import Gen

open Zig

private def check [DecidableEq α] [Repr α] (name : String) (actual expected : α) : IO Unit := do
  unless actual = expected do
    throw (IO.userError s!"{name}: expected {reprStr expected}, got {reprStr actual}")

private def execute (name : String) (program : MemM α) (memory : Mem := GlobalPayload.mem0) : IO (α × Mem) := do
  match (program.run memory).run with
  | some (.ok answer) => pure answer
  | some (.error error) => throw (IO.userError s!"{name}: unexpected model error {reprStr error}")
  | none => throw (IO.userError s!"{name}: model did not terminate")

private def bytes (memory : Mem) (block : Nat) : IO (Array Byte) := do
  let some b := memory.blocks[block]? | throw (IO.userError "missing actual global block")
  pure b.bytes

private def frozen : Ptr := ⟨some 0, 0⟩

-- These offsets derive from the public source/profile, not the stored AIR address.
private def optionalOffset : Nat := 8 + 16 + 4
private def smallOffset : Nat := 8 + 28 + 2
private def wideOffset : Nat := 8 + 0
private def equalOffset : Nat := 8 + 32

private def unchangedExcept (name : String) (memory : Mem) (start count : Nat) : IO Unit := do
  check (name ++ ":block-count") memory.blocks.size GlobalPayload.mem0.blocks.size
  check (name ++ ":allocations") memory.allocs GlobalPayload.mem0.allocs
  check (name ++ ":frozen-frame") (← bytes memory 0) (← bytes GlobalPayload.mem0 0)
  let before ← bytes GlobalPayload.mem0 1
  let after ← bytes memory 1
  check (name ++ ":object-size") after.size before.size
  for (byte, index) in before.zipIdx do
    if index < start || start + count ≤ index then
      check (name ++ s!":untouched-byte-{index}") after[index]? (some byte)

private def observeWrites : IO Unit := do
  let (optionalResult, optionalMemory) ← execute "writeOptional" (GlobalPayload.writeOptional 23)
  check "writeOptional:return" optionalResult (23 : BitVec 8)
  unchangedExcept "writeOptional" optionalMemory optionalOffset 1
  let (optionalStored, _) ← execute "writeOptional:actual-heap" (load (BitVec 8) 1 ⟨some 1, optionalOffset⟩) optionalMemory
  check "writeOptional:actual-heap" optionalStored (23 : BitVec 8)
  let (smallResult, smallMemory) ← execute "writeSmall" (GlobalPayload.writeSmall 31)
  check "writeSmall:return" smallResult (31 : BitVec 8)
  unchangedExcept "writeSmall" smallMemory smallOffset 1
  let (smallStored, _) ← execute "writeSmall:actual-heap" (load (BitVec 8) 1 ⟨some 1, smallOffset⟩) smallMemory
  check "writeSmall:actual-heap" smallStored (31 : BitVec 8)
  let (wideResult, wideMemory) ← execute "writeWide" (GlobalPayload.writeWide 123)
  check "writeWide:return" wideResult (123 : BitVec 64)
  unchangedExcept "writeWide" wideMemory wideOffset 8
  let (wideStored, _) ← execute "writeWide:actual-heap" (load (BitVec 64) 8 ⟨some 1, wideOffset⟩) wideMemory
  check "writeWide:actual-heap" wideStored (123 : BitVec 64)

def main : IO Unit := do
  let (optional, _) ← execute "optionalPtr" GlobalPayload.optionalPtr
  let (small, _) ← execute "smallPtr" GlobalPayload.smallPtr
  let (wide, _) ← execute "widePtr" GlobalPayload.widePtr
  let (equal, _) ← execute "equalPtr" GlobalPayload.equalPtr
  let (same, _) ← execute "sameOptionalPtr" GlobalPayload.sameOptionalPtr
  let (slice, _) ← execute "optionalSlice" GlobalPayload.optionalSlice
  check "optional provenance/address" optional (frozen.add optionalOffset)
  check "small provenance/address" small (frozen.add smallOffset)
  check "wide provenance/address" wide (frozen.add wideOffset)
  check "equal provenance/address" equal (frozen.add equalOffset)
  check "same optional alias" same optional
  check "slice ptr alias" slice.ptr optional
  check "slice length" slice.len (1 : BitVec 64)
  let (optionalValue, _) ← execute "optional actual pointer load" (load (BitVec 8) 1 optional)
  let (smallValue, _) ← execute "small actual pointer load" (load (BitVec 8) 1 small)
  let (wideValue, _) ← execute "wide actual pointer load" (load (BitVec 64) 8 wide)
  let (equalValue, _) ← execute "equal actual pointer load" (load (BitVec 16) 2 equal)
  check "optional actual pointer load" optionalValue (7 : BitVec 8)
  check "small actual pointer load" smallValue (19 : BitVec 8)
  check "wide actual pointer load" wideValue (41 : BitVec 64)
  check "equal actual pointer load" equalValue (23 : BitVec 16)
  check "optional source folded read" GlobalPayload.optionalRead.run (some (.ok (7 : BitVec 8)))
  check "small source folded read" GlobalPayload.smallRead.run (some (.ok (19 : BitVec 8)))
  check "wide source folded read" GlobalPayload.wideRead.run (some (.ok (41 : BitVec 64)))
  observeWrites
  -- Model constness control uses an actual generated getter, not an invented source export.
  let constResult := ((store 1 optional (99 : BitVec 8)).run GlobalPayload.mem0).run
  match constResult with
  | some (.error .illegal) => pure ()
  | _ => throw (IO.userError "actual frozen getter allowed model store or failed for the wrong reason")
  IO.println "actual Global Gen: six getters/slice, three folded reads, four heap reads, three writes/full byte frames, const-store guard passed"
