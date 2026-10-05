-- Appended to the freshly emitted NullableNative translation by check.sh.
private def observed (x : Zig.MemM α) : IO α :=
  match (x.run {}).run with
  | some (.ok (v, _)) => pure v
  | some (.error e) => throw (IO.userError s!"unexpected modeled error: {reprStr e}")
  | none => throw (IO.userError "unexpected modeled divergence")

def main : IO Unit := do
  for n in ([0, 1, 8, 4095, 65535, 18446744073709551615] : List Nat) do
    let arg : BitVec 64 := BitVec.ofNat 64 n
    let isNull ← observed (NullableNative.cNull arg)
    let address ← observed (NullableNative.allowzeroAddress arg)
    let manyAddress ← observed (NullableNative.allowzeroManyAddress arg)
    let cast ← observed (NullableNative.castChecked arg)
    IO.println s!"{n} {if isNull then 1 else 0} {address.toNat} {manyAddress.toNat} {if cast then 1 else 0}"
  let empty ← observed (NullableNative.cRead Zig.Ptr.null)
  let live ← observed (do
    let p ← Zig.alloc .heap 1 1
    Zig.store 1 p (37#8)
    NullableNative.cRead p)
  IO.println s!"read {empty.toNat} {live.toNat}"
  let zero ← observed (do Zig.ptrAddr (← NullableNative.cZero))
  IO.println s!"zero {zero}"
