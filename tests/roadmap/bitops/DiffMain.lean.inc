
/-! Append to the compiler-generated Bitops namespace translation, then run this file.
It does not import an uncommitted generated module or choose opaque runtime outcomes. -/
private def bitopsValue {α : Type} (label : String) (r : Zig.Result α) : IO α :=
  match r.run with
  | some (.ok value) => pure value
  | _ => throw (IO.userError s!"unexpected bitops result: {label}")

def main : IO Unit := do
  for i in [0:256] do
    let x := BitVec.ofNat 8 i
    let a ← bitopsValue "counts8" (Bitops.counts8 x)
    let b ← bitopsValue "countsSigned8" (Bitops.countsSigned8 x)
    let c ← bitopsValue "countsNarrow" (Bitops.countsNarrow x)
    let d ← bitopsValue "countsOne" (Bitops.countsOne x)
    IO.println s!"counts {i} {a.toNat} {b.toNat} {c.toNat} {d.toNat}"
    for k in [0:8] do
      let amount := BitVec.ofNat 8 k
      let a ← bitopsValue "shiftUnsigned8" (Bitops.shiftUnsigned8 x amount)
      let b ← bitopsValue "shiftSigned8" (Bitops.shiftSigned8 x amount)
      IO.println s!"shift {i} {k} {a.toNat} {b.toNat}"
    -- Count 3 is an explicit illegal-domain exclusion, tested in Runtime/Cases.
    for k in [0:3] do
      let amount := BitVec.ofNat 8 k
      let a ← bitopsValue "shiftNarrow" (Bitops.shiftNarrow x amount)
      let b ← bitopsValue "shiftSignedNarrow" (Bitops.shiftSignedNarrow x amount)
      IO.println s!"narrow {i} {k} {a.toNat} {b.toNat}"
  let vectors : Array (Zig.Vec (BitVec 8) 4) :=
    #[⟨#v[0, 255, 128, 1]⟩, ⟨#v[2, 64, 127, 129]⟩, ⟨#v[0, 0, 0, 0]⟩]
  let shifts : Zig.Vec (BitVec 8) 4 := ⟨#v[7, 1, 6, 0]⟩
  for i in [0:vectors.size] do
    let x := vectors[i]!
    let a ← bitopsValue "leadingLanes" (Bitops.leadingLanes x)
    let b ← bitopsValue "trailingLanes" (Bitops.trailingLanes x)
    let c ← bitopsValue "populationLanes" (Bitops.populationLanes x)
    let d ← bitopsValue "shiftLanes" (Bitops.shiftLanes x shifts)
    let e ← bitopsValue "shiftSignedLanes" (Bitops.shiftSignedLanes x shifts)
    for lane in [0:4] do
      IO.println s!"vector {i} {lane} {a.lanes.toArray[lane]!.toNat} {b.lanes.toArray[lane]!.toNat} {c.lanes.toArray[lane]!.toNat} {d.lanes.toArray[lane]!.toNat} {e.lanes.toArray[lane]!.toNat}"
  let bitsets : Array Nat :=
    #[0, 1, 2, 65535, 18446744073709551615, 9223372036854775808, 9223372036854775809, 6148914691236517205]
  for i in bitsets do
    let x := BitVec.ofNat 64 i
    let a ← bitopsValue "firstSet" (Bitops.firstSet x)
    let b ← bitopsValue "clearLowest" (Bitops.clearLowest x)
    let c ← bitopsValue "cardinality" (Bitops.cardinality x)
    IO.println s!"bitset {i} {a.toNat} {b.toNat} {c.toNat}"
