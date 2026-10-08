-- Appended to the freshly emitted NullableNative translation by check.sh.
private def observed (x : Zig.MemM α) : IO α :=
  match (x.run {}).run with
  | some (.ok (v, _)) => pure v
  | some (.error e) => throw (IO.userError s!"unexpected modeled error: {reprStr e}")
  | none => throw (IO.userError "unexpected modeled divergence")

/-- `.illegal` is the model's verdict; any other outcome is unexpected. -/
private def illegal (x : Zig.MemM α) : IO Bool :=
  match (x.run {}).run with
  | some (.error .illegal) => pure true
  | _ => pure false

private def addr (p : Zig.Ptr) : Zig.MemM Nat := do pure (← Zig.ptrAddr p).toNat
/-- The address of a field pointer of address zero, or `illegal` where the compiler types it as a
nonnullable pointer (Zig ≤0.15, `Zig.ptrProjectNonnull`; check.sh expects that only there). -/
private def addrOrIllegal (x : Zig.MemM Zig.Ptr) : IO String := do
  if ← illegal x then pure "illegal" else pure (toString (← observed (do addr (← x))))
private def bit (b : Bool) : Nat := if b then 1 else 0
/-- A two-byte heap block holding 7, 9 (the native `byte2`). -/
private def live2 : Zig.MemM Zig.Ptr := do
  let p ← Zig.alloc .heap 2 1
  Zig.store 1 p (7#8)
  Zig.store 1 (p.add 1) (9#8)
  pure p
/-- An 8-aligned C-pointer slot holding `v`. -/
private def slotWith (v : Zig.Ptr) : Zig.MemM Zig.Ptr := do
  let s ← Zig.alloc .heap 8 8
  letI : Zig.Enc Zig.Ptr := Zig.nullablePtrEnc
  Zig.store 8 s v
  pure s
private def nodeWith (n : NullableNative.Node) : Zig.MemM Zig.Ptr := do
  let s ← Zig.alloc .heap 16 8
  Zig.store 8 s n
  pure s

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
  -- L05 storage, aggregate, projection and optional-conversion cases.
  let (a, b) ← observed (do
    let live ← live2
    let slot ← slotWith live
    let a ← addr (← NullableNative.storeLoad slot Zig.Ptr.null)
    pure (a, bit ((← NullableNative.storeLoad slot live) = live)))
  IO.println s!"storeLoad {a} {b}"
  let (a, b) ← observed (do
    let live ← live2
    let a ← NullableNative.storedIsNull (← slotWith Zig.Ptr.null)
    pure (bit a, bit (← NullableNative.storedIsNull (← slotWith live))))
  IO.println s!"storedIsNull {a} {b}"
  let (a, b) ← observed (do
    let live ← live2
    let slot ← slotWith live
    let a ← addr (← NullableNative.allowzeroStoreLoad slot Zig.Ptr.null)
    let q ← NullableNative.allowzeroStoreLoad slot live
    pure (a, bit ((← addr q) = (← addr live))))
  IO.println s!"allowzeroStoreLoad {a} {b}"
  let (a, b, c) ← observed (do
    let live ← live2
    let a ← addr (← NullableNative.nodeNext (← nodeWith { next := Zig.Ptr.null, val := 0#8 }))
    let node ← nodeWith { next := live, val := 5#8 }
    pure (a, bit ((← NullableNative.nodeNext node) = live), (← NullableNative.nodeVal node).toNat))
  IO.println s!"nodeNext {a} {b} nodeVal {c}"
  let v ← observed (do NullableNative.nodeRoundTrip (← nodeWith { next := Zig.Ptr.null, val := 0#8 }) 9#8)
  IO.println s!"nodeRoundTrip {v.toNat}"
  let (a, b) ← observed (do
    let live ← live2
    let items ← Zig.alloc .heap 16 8
    letI : Zig.Enc Zig.Ptr := Zig.nullablePtrEnc
    Zig.store 8 items live
    Zig.store 8 (items.add 8) Zig.Ptr.null
    let a ← NullableNative.arrayItem items 0
    pure (bit (a = live), ← addr (← NullableNative.arrayItem items 1)))
  IO.println s!"arrayItem {a} {b}"
  let (a, b) ← observed (do
    let live ← live2
    pure (← addr (← NullableNative.cAdd Zig.Ptr.null 0), (← addr (← NullableNative.cAdd live 1)) - (← addr live)))
  IO.println s!"cAdd {a} {b}"
  let (a, b) ← observed (do
    let live ← live2
    pure (← addr (← NullableNative.cSub Zig.Ptr.null 0), (← addr live) - (← addr (← NullableNative.cSub (live.add 1) 1))))
  IO.println s!"cSub {a} {b}"
  let (a, b) ← observed (do
    let live ← live2
    pure (← addr (← NullableNative.cIndex Zig.Ptr.null 0), (← addr (← NullableNative.cIndex live 1)) - (← addr live)))
  IO.println s!"cIndex {a} {b}"
  let (a, b) ← observed (do
    let live ← live2
    pure ((← NullableNative.cElem live 0).toNat, (← NullableNative.cElem live 1).toNat))
  IO.println s!"cElem {a} {b}"
  let a ← addrOrIllegal (NullableNative.nextPtr Zig.Ptr.null)
  let b ← observed (do
    let node ← nodeWith { next := Zig.Ptr.null, val := 0#8 }
    pure ((← addr (← NullableNative.nextPtr node)) - (← addr node)))
  IO.println s!"nextPtr {a} {b}"
  let a ← observed (do
    let node ← nodeWith { next := Zig.Ptr.null, val := 0#8 }
    pure ((← addr (← NullableNative.valPtr node)) - (← addr node)))
  IO.println s!"valPtr {a}"
  let a ← addrOrIllegal (NullableNative.allowzeroNextPtr Zig.Ptr.null)
  IO.println s!"allowzeroNextPtr {a}"
  let (a, b) ← observed (do
    let live ← live2
    pure (← addr (← NullableNative.allowzeroAdd Zig.Ptr.null 0), (← addr (← NullableNative.allowzeroAdd live 1)) - (← addr live)))
  IO.println s!"allowzeroAdd {a} {b}"
  let (a, b) ← observed (do
    let live ← live2
    pure (bit ((← NullableNative.toOptional Zig.Ptr.null) = none), bit ((← NullableNative.toOptional live) = some live)))
  IO.println s!"toOptional {a} {b}"
  let (a, b) ← observed (do
    let live ← live2
    pure (← addr (← NullableNative.fromOptional none), bit ((← NullableNative.fromOptional (some live)) = live)))
  IO.println s!"fromOptional {a} {b}"
  let zeroOffset ← observed (NullableNative.addIsNull Zig.Ptr.null 0)
  let nonzero ← illegal (NullableNative.addIsNull Zig.Ptr.null 1)
  IO.println s!"addIsNull {bit zeroOffset} {if nonzero then "illegal" else "address"}"
  -- Nonzero offsets from address zero that native code never executes (LLVM poison).
  for (name, x) in [("cAdd", NullableNative.cAdd Zig.Ptr.null 1), ("cSub", NullableNative.cSub Zig.Ptr.null 1),
      ("cIndex", NullableNative.cIndex Zig.Ptr.null 3), ("valPtr", NullableNative.valPtr Zig.Ptr.null),
      ("allowzeroAdd", NullableNative.allowzeroAdd Zig.Ptr.null 1)] do
    unless ← illegal x do throw (IO.userError s!"{name}: nonzero offset from address zero is not illegal")
