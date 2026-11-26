-- Appended to the freshly emitted OpaquePtrs translation of `air-recover/<version>` under
-- `--allocator-model translated` by check.sh: the model's last transcript line of `main`.
private def observed (x : Zig.MemM α) : IO α :=
  match (x.run (OpaquePtrs.mem0 .fresh)).run with
  | some (.ok (v, _)) => pure v
  | some (.error e) => throw (IO.userError s!"unexpected modeled error: {reprStr e}")
  | none => throw (IO.userError "unexpected modeled divergence")

def main : IO Unit := do
  let (a, b, c) ← observed (do
    let x ← Zig.alloc .heap 4 4
    Zig.store 4 x (41 : BitVec 32)
    let a ← OpaquePtrs.Handle_value (← OpaquePtrs.erase x)
    let b ← OpaquePtrs.roundTrip x
    pure (a.toNat, b.toNat, (← Zig.load (BitVec 32) 4 x).toNat))
  IO.println s!"value {a} roundTrip {b} {c}"
  -- Model only (the native `main` would end here): a handle of misaligned storage, on which
  -- the recovery's `@alignCast` check panics.
  let misaligned := ((do
    let block ← Zig.alloc .heap 8 4
    discard <| OpaquePtrs.recover (← OpaquePtrs.erase (block.add 1))) : Zig.MemM Unit)
  match (misaligned.run (OpaquePtrs.mem0 .fresh)).run with
  | some (.error .panic) => IO.println "model recover misaligned panic"
  | _ => throw (IO.userError "a misaligned recovery did not panic")
