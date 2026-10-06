import ErrorUnionABI.Gen

open Zig

private def result (action : MemM α) : Option (Except Error α) :=
  (action.run {}).run.map (·.map Prod.fst)

private def scalarRead : MemM (BitVec 16) := do
  let p ← alloc .heap 4 2
  storeBytes p 2 #[.int 0x34, .int 0x12, .int 0, .int 0]
  ErrorUnionABI.scalar p

private def pairRead : MemM (BitVec 16) := do
  let p ← alloc .heap 6 2
  storeBytes p 2 #[.int 0x34, .int 0x12, .int 0x78, .int 0x56, .int 0, .int 0]
  ErrorUnionABI.pair p

private def arrayRead : MemM (BitVec 16) := do
  let p ← alloc .heap 6 2
  storeBytes p 2 #[.int 0x34, .int 0x12, .int 0x78, .int 0x56, .int 0, .int 0]
  ErrorUnionABI.array p

private def aliasedWrite : MemM (BitVec 16) := do
  let p ← alloc .heap 4 2
  storeBytes p 2 #[.int 0x34, .int 0x12, .int 0, .int 0]
  ErrorUnionABI.writeScalar p 0xabcd
  -- Read through the independent ABI payload alias, rather than the union decoder.
  load (BitVec 16) 2 p

private def payloadAlias : MemM (BitVec 16) := do
  let p ← alloc .heap 4 2
  storeBytes p 2 #[.int 0x34, .int 0x12, .int 0, .int 0]
  let q ← ErrorUnionABI.payloadPointer p
  unless q = p do throw .illegal
  store 2 q (0xabcd : BitVec 16)
  ErrorUnionABI.scalar p

private def errorRead : MemM (BitVec 16) := do
  let p ← alloc .heap 4 2
  storeBytes p 2 #[.undef, .undef, .errFrag "Bad" 0, .errFrag "Bad" 1]
  ErrorUnionABI.scalar p

private def check (name : String) (action : MemM (BitVec 16)) (expected : Nat) : IO Unit :=
  match result action with
  | some (.ok got) =>
    unless got.toNat = expected do
      throw (IO.userError s!"generated ABI {name}: expected {expected}, got {got.toNat}")
  | other => throw (IO.userError s!"generated ABI {name}: failed with {reprStr other}")

def main : IO Unit := do
  check "scalar raw layout" scalarRead 0x1234
  check "struct raw layout" pairRead 0x1234
  check "array raw layout" arrayRead 0x5678
  check "write visible through payload alias" aliasedWrite 0xabcd
  check "payload pointer alias" payloadAlias 0xabcd
  check "error at compiler offset" errorRead 0
  IO.println "Generated error-union ABI memory checks passed"
