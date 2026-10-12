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
/-- The value, or the model's error (`illegal`, `panic`, ...). -/
private def outcome (x : Zig.MemM Nat) : IO String :=
  match (x.run {}).run with
  | some (.ok (v, _)) => pure (toString v)
  | some (.error e) => pure ((reprStr e).replace "Zig.Error." "")
  | none => pure "divergence"
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
/-- A `?*allowzero u8` slot holding `v`: the payload, then the flag byte. -/
private def optSlotWith (v : Option Zig.Ptr) : Zig.MemM Zig.Ptr := do
  let s ← Zig.alloc .heap 16 8
  letI : Zig.Enc (Option Zig.Ptr) := Zig.Enc.optionWith Zig.nullablePtrEnc
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
  let b ← observed (do
    let node ← nodeWith { next := Zig.Ptr.null, val := 0#8 }
    pure ((← addr (← NullableNative.nextPtr node)) - (← addr node)))
  IO.println s!"nextPtr {b}"
  let a ← observed (do
    let node ← nodeWith { next := Zig.Ptr.null, val := 0#8 }
    pure ((← addr (← NullableNative.valPtr node)) - (← addr node)))
  IO.println s!"valPtr {a}"
  IO.println s!"allowzeroNextPtr {← outcome (do addr (← NullableNative.allowzeroNextPtr Zig.Ptr.null))}"
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
  -- L05 completion: optionals of nullable pointers, unions, tuples, error unions, nullable
  -- slices, bulk memory, parent recovery and a provenance-free offset.
  let s0 : Option Zig.Ptr := some Zig.Ptr.null
  let (a, b, c, d, e, f, g) ← observed (do
    let live ← live2
    pure (bit (← NullableNative.optIsNull none), bit (← NullableNative.optIsNull s0),
      (← NullableNative.optUnwrap s0).toNat, bit (← NullableNative.optEq none s0),
      bit (← NullableNative.optEq s0 s0), bit (← NullableNative.optEq none none),
      bit (← NullableNative.optEq s0 (some live))))
  IO.println s!"optional {a} {b} {c} {d} {e} {f} {g}"
  let (a, b) ← observed (do
    let live ← live2
    let q ← NullableNative.optWrap live
    pure (bit ((← NullableNative.optWrap Zig.Ptr.null) = none), (← addr (q.getD Zig.Ptr.null)) - (← addr live)))
  IO.println s!"optWrap {a} {b}"
  let (a, b, c) ← observed (do
    let live ← live2
    let slot ← optSlotWith (some live)
    let a := bit ((← NullableNative.optStoreLoad slot none) = none)
    let b ← addr ((← NullableNative.optStoreLoad slot s0).getD live)
    pure (a, b, bit ((← NullableNative.optStoreLoad slot (some live)) = some live)))
  IO.println s!"optStoreLoad {a} {b} {c}"
  let (a, b) ← observed (do
    pure ((← NullableNative.optPayloadPtr (← optSlotWith s0)).toNat,
      (← NullableNative.optPayloadPtr (← optSlotWith none)).toNat))
  IO.println s!"optPayloadPtr {a} {b}"
  let (a, b) ← observed (do
    pure (bit (← NullableNative.optCIsNull none), bit (← NullableNative.optCIsNull s0)))
  IO.println s!"optC {a} {b}"
  let (a, b) ← observed (do
    let q ← NullableNative.optFromOrdinary none
    pure (bit (q = none), ← addr (q.getD ⟨none, 1⟩)))
  IO.println s!"optFromOrdinary {a} {b}"
  let (a, b, c) ← observed (do
    let live ← live2
    let box ← Zig.alloc .heap 16 8
    Zig.store 8 box (NullableNative.Box.ptr Zig.Ptr.null)
    let a := (← NullableNative.boxPtr box).toNat
    NullableNative.boxSet box live
    let b := bit ((← NullableNative.boxPtr box).toNat = (← addr live))
    Zig.store 8 box (NullableNative.Box.num 5#32)
    pure (a, b, (← NullableNative.boxPtr box).toNat))
  IO.println s!"box {a} {b} {c}"
  let (a, b) ← observed (do
    let live ← live2
    pure ((← NullableNative.pairFirst Zig.Ptr.null).toNat,
      bit ((← NullableNative.pairFirst live).toNat = (← addr live))))
  IO.println s!"pair {a} {b}"
  let (a, b, c, d) ← observed (do
    let live ← live2
    let a ← match ← NullableNative.errPtr false Zig.Ptr.null with
      | .ok p => addr p
      | .error _ => pure 99
    let b ← match ← NullableNative.errPtr true live with
      | .ok p => addr p
      | .error _ => pure 99
    let slot ← Zig.alloc .heap 16 8
    let c := (← NullableNative.errStore slot Zig.Ptr.null).toNat
    pure (a, b, c, bit ((← NullableNative.errStore slot live).toNat = (← addr live))))
  IO.println s!"errPtr {a} {b} errStore {c} {d}"
  let (a, b, c, d, e, f) ← observed (do
    let live ← live2
    let empty ← NullableNative.sliceAz Zig.Ptr.null 0 0
    let part ← NullableNative.sliceAz live 1 2
    let whole ← NullableNative.arrayAz Zig.Ptr.null
    pure (← addr empty.ptr, empty.len.toNat, (← addr part.ptr) - (← addr live), part.len.toNat,
      ← addr whole.ptr, whole.len.toNat))
  IO.println s!"sliceAz {a} {b} {c} {d} arrayAz {e} {f}"
  let (a, b, c, d, e, f) ← observed (do
    let live ← live2
    let empty ← NullableNative.sliceAz Zig.Ptr.null 0 0
    NullableNative.memsetAz empty 1#8
    NullableNative.memcpyAz empty empty
    NullableNative.memsetAz (← NullableNative.sliceAz live 0 2) 5#8
    let a := (← Zig.load (BitVec 8) 1 live).toNat
    let b := (← Zig.load (BitVec 8) 1 (live.add 1)).toNat
    Zig.store 1 (live.add 1) (6#8)
    NullableNative.memcpyAz (← NullableNative.sliceAz live 0 1) (← NullableNative.sliceAz live 1 2)
    let c := (← Zig.load (BitVec 8) 1 live).toNat
    NullableNative.memsetC live 2 3#8
    pure (a, b, c, (← Zig.load (BitVec 8) 1 live).toNat, (← Zig.load (BitVec 8) 1 (live.add 1)).toNat,
      (← NullableNative.sliceC live 0 2).len.toNat))
  IO.println s!"memsetAz {a} {b} memcpyAz {c} memsetC {d} {e} sliceC {f}"
  let (a, b) ← observed (do
    let parent ← Zig.alloc .heap 16 8
    pure (bit ((← NullableNative.parentSecond (parent.add 8)) = parent),
      ← addr (← NullableNative.parentFirst Zig.Ptr.null)))
  IO.println s!"parent {a} {b}"
  let zeroOffset ← observed (NullableNative.mmioIsNull 4096 0)
  let wraps ← illegal (NullableNative.mmioIsNull 18446744073709551612 1)
  IO.println s!"mmioIsNull {bit zeroOffset} {if wraps then "illegal" else "address"}"
  IO.println s!"nullNextPtr {← outcome (do addr (← NullableNative.nextPtr Zig.Ptr.null))}"
  -- Model only: nonzero offsets from address zero that native code never executes (LLVM poison;
  -- Zig 0.17.0 checks the field pointer of a null C pointer first and panics).
  let mut line := "model nonzeroFromNull"
  for (name, x) in [("cAdd", NullableNative.cAdd Zig.Ptr.null 1), ("cSub", NullableNative.cSub Zig.Ptr.null 1),
      ("cIndex", NullableNative.cIndex Zig.Ptr.null 3), ("valPtr", NullableNative.valPtr Zig.Ptr.null),
      ("allowzeroAdd", NullableNative.allowzeroAdd Zig.Ptr.null 1)] do
    line := line ++ s!" {name} {← outcome (do addr (← x))}"
  IO.println line
  -- Model only: illegal behaviour that no safety check catches, which native code runs as an
  -- address or a wrapped value (LLVM poison) or a fault, and a premise-relative offset of a
  -- provenance-free address no declared object covers (docs/null-pointers.md).
  line := "model nullableIllegal"
  for (name, x) in [("sliceAz", do addr (← NullableNative.sliceAz Zig.Ptr.null 1 1).ptr),
      ("parentSecond", do addr (← NullableNative.parentSecond Zig.Ptr.null)),
      ("parentSecondRaw", do addr (← NullableNative.parentSecond ⟨none, 8⟩)),
      ("memsetAz", do NullableNative.memsetAz ⟨Zig.Ptr.null, 1⟩ 1#8; pure 0),
      ("mmioIsNull", do pure (bit (← NullableNative.mmioIsNull 4096 1)))] do
    line := line ++ s!" {name} {← outcome x}"
  IO.println line
  -- The native `case` runs (`check.sh --native`): each ends the process.
  IO.println s!"case sliceCNull {← outcome (do pure (← NullableNative.sliceC Zig.Ptr.null 1 1).len.toNat)}"
  IO.println s!"case memsetCNull {← outcome (do NullableNative.memsetC Zig.Ptr.null 0 1#8; pure 0)}"
  IO.println s!"case optUnwrapNull {← outcome (do pure (← NullableNative.optUnwrap none).toNat)}"
  IO.println s!"case memsetAzNull {← outcome (do NullableNative.memsetAz (← NullableNative.sliceAz Zig.Ptr.null 0 1) 1#8; pure 0)}"
