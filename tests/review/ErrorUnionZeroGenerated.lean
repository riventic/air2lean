import ErrorUnionZero.Gen

open Zig

def main : IO Unit := do
  let action : MemM Bool := do
    let p ← alloc .heap 8 8
    storeBytes p 8 #[.int 0, .int 0, .undef, .undef, .undef, .undef, .undef, .undef]
    ErrorUnionZero.zeroArray p
  match (action.run {}).run with
  | some (.ok (true, _)) => IO.println "Generated zero-payload ABI check passed"
  | other => throw (IO.userError s!"generated zero-payload ABI failed: {reprStr other}")
