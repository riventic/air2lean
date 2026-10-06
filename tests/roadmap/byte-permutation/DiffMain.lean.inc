
private def permutationValue {α : Type} (r : Zig.Result α) : IO α :=
  match r.run with
  | some (.ok value) => pure value
  | _ => throw (IO.userError "unexpected permutation result")

def main : IO Unit := do
  for i in [0:256] do
    let x := BitVec.ofNat 8 i
    let a ← permutationValue (Permutations.reverse8 x)
    let b ← permutationValue (Permutations.reverseSigned8 x)
    let c ← permutationValue (Permutations.reverse1 x)
    let d ← permutationValue (Permutations.reverse3 x)
    let e ← permutationValue (Permutations.reverseSigned3 x)
    let f ← permutationValue (Permutations.swap8 x)
    let g ← permutationValue (Permutations.swapSigned8 x)
    IO.println s!"small {i} {a.toNat} {b.toNat} {c.toNat} {d.toNat} {e.toNat} {f.toNat} {g.toNat}"
  for i in [0:512] do
    let x := BitVec.ofNat 16 i
    let a ← permutationValue (Permutations.reverse9 x)
    let b ← permutationValue (Permutations.reverseSigned9 x)
    IO.println s!"nine {i} {a.toNat} {b.toNat}"
  let words : Array Nat := #[0, 1, 0x1234, 0x8001, 0xffff, 0x123456, 0x800001, 0xffffff, 0xffffffff]
  for i in words do
    let x := BitVec.ofNat 32 i
    let y := BitVec.ofNat 16 i
    let a ← permutationValue (Permutations.swap16 y)
    let b ← permutationValue (Permutations.swapSigned16 y)
    let c ← permutationValue (Permutations.swap24 x)
    let d ← permutationValue (Permutations.swapSigned24 x)
    IO.println s!"word {i} {a.toNat} {b.toNat} {c.toNat} {d.toNat}"
  let wide : Array Nat := #[0, 1, 0x0123456789abcdef, 0x8000000000000001,
    0xffffffffffffffff, 0x0123456789abcdeffedcba9876543210,
    0x80000000000000000000000000000001, 0xffffffffffffffffffffffffffffffff]
  for i in wide do
    let x := BitVec.ofNat 128 i
    let y := BitVec.ofNat 64 i
    let a ← permutationValue (Permutations.reverse64 y)
    let b ← permutationValue (Permutations.reverseSigned64 y)
    let c ← permutationValue (Permutations.swap64 y)
    let d ← permutationValue (Permutations.swapSigned64 y)
    let e ← permutationValue (Permutations.reverse128 x)
    let f ← permutationValue (Permutations.reverseSigned128 x)
    let g ← permutationValue (Permutations.swap128 x)
    let h ← permutationValue (Permutations.swapSigned128 x)
    IO.println s!"wide {i} {a.toNat} {b.toNat} {c.toNat} {d.toNat} {e.toNat} {f.toNat} {g.toNat} {h.toNat}"
  let vectors : Array (Zig.Vec (BitVec 16) 3) :=
    #[⟨#v[0x1234, 0x8001, 0x00ff]⟩, ⟨#v[1, 2, 3]⟩, ⟨#v[0, 65535, 256]⟩]
  for i in [0:vectors.size] do
    let x := vectors[i]!
    let a ← permutationValue (Permutations.reverseLanes x)
    let b ← permutationValue (Permutations.reverseSignedLanes x)
    let c ← permutationValue (Permutations.swapLanes x)
    let d ← permutationValue (Permutations.swapSignedLanes x)
    let e ← permutationValue (Permutations.reverseNarrowLanes (Zig.Vec.map (BitVec.setWidth 8) x))
    for lane in [0:3] do
      IO.println s!"lane {i} {lane} {a.lanes.toArray[lane]!.toNat} {b.lanes.toArray[lane]!.toNat} {c.lanes.toArray[lane]!.toNat} {d.lanes.toArray[lane]!.toNat} {e.lanes.toArray[lane]!.toNat}"
  let a ← permutationValue Permutations.reverseZero
  let b ← permutationValue Permutations.reverseSignedZero
  let c ← permutationValue Permutations.swapZero
  let d ← permutationValue Permutations.swapSignedZero
  IO.println s!"zero {a.toNat} {b.toNat} {c.toNat} {d.toNat}"
