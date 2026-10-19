import Air2Lean.CanonCertificate

/-! Native debug-ID binding evidence. These controls exercise complete Func equality,
nested instruction families and metadata; none is represented as a kernel proof of Raw.
The generic semantic theorem is checked once in CanonSem, independently of this fixture. -/

namespace CanonBinding

open Air2Lean

def widths : Array Nat := #[0, 1, 31, 32, 33, 63, 64, 65, 127, 128, 129]

def longName : String := String.ofList (List.replicate 120 'x') ++ "\n\"quoted\""

def leaf (n : Nat) : Array Inst := (Array.range n).map fun k =>
  if k == 0 then ⟨0, 0, .arg 0⟩
  else if k % 5 == 0 then ⟨10000 + k, 2, .line k⟩
  else ⟨k, 0, .call (.func longName false none) #[.int 0 (Int.ofNat k), .inst 0]⟩

def nested (n : Nat) : Array Inst :=
  let child : Array Inst := #[⟨10000, 2, .dbg (some longName) (some (.inst 0))⟩,
    ⟨1, 2, .block (leaf 33)⟩, ⟨2, 2, .condBr (.bool true) (leaf 31) (leaf 32)⟩]
  let cases : Array SwitchCase := (Array.range n).map fun k =>
    { items := #[Val.int 0 (Int.ofNat k)],
      ranges := #[(Val.int 0 (Int.ofNat k), Val.int 0 (Int.ofNat (k + 1)))],
      body := if k == 0 then child else leaf 1 }
  #[⟨0, 0, .arg 0⟩, ⟨1, 2, .block child⟩, ⟨2, 2, .loop (leaf 65)⟩,
    ⟨3, 2, .condBr (.bool true) child (leaf 63)⟩,
    ⟨4, 2, .switchBr (.int 0 0) cases (leaf 64)⟩,
    ⟨5, 2, .loopSwitchBr (.int 0 0) cases (leaf 1)⟩,
    ⟨6, 2, .«try» (.inst 0) child⟩, ⟨7, 2, .tryPtr (.inst 0) child⟩]

def sample (name : String) (body : Array Inst) : Func :=
  { dialect := .ofVersion .v0_17_0, name, params := #[0], ret := 0, body,
    types := #[.int false 64, .bool, .void],
    layouts := #[{ size := some 8, align := some 8 },
      { size := some 1, align := some 1 }, { size := some 0, align := some 1 }],
    globals := #[] }

def snapshot (f : Func) : Nat × Func × Func :=
  (10000, f, { f with body := DebugIds.mapDebugArray (fun id => id - 10000) f.body })

def metadataSamples : Array Func :=
  let f := sample "metadata" (leaf 1)
  let types : Array Ty := #[.int false 64, .bool, .int false 64]
  let layouts : Array Layout := #[{ size := some 8, align := some 8 },
    { size := some 1, align := some 1 }, { size := some 8, align := some 8 }]
  let a : Global := {
    name := some "shared", ty := 0, isConst := true,
    threadlocal := false, isExtern := false, init := some (.int 0 1) }
  let b := { a with init := some (.int 0 2) }
  #[{ f with name := "metadataA", types, layouts, globals := #[a, b, a] },
    { f with
      name := "metadataB", types := #[types[1]!, types[0]!, types[0]!],
      layouts := #[layouts[1]!, layouts[0]!, layouts[0]!], globals := #[b, a, a] },
    { f with name := "metadataC", types, layouts, globals := #[a, b, a] }]

def snapshots : Array (Nat × Func × Func) :=
  (widths.map fun n => snapshot (sample s!"leaf{n}" (leaf n))) ++
  (#[33, 65, 129].map fun n => snapshot (sample s!"nested{n}" (nested n))) ++
  metadataSamples.map snapshot

end CanonBinding

open Air2Lean

private def reject (label : String) (snapshots : Array (Nat × Air2Lean.Func × Air2Lean.Func)) : IO Unit :=
  match Air2Lean.CanonCertificate.checkBindings snapshots with
  | .error _ => IO.println s!"native-debug-binding: {label} rejected"
  | .ok _ => throw (IO.userError s!"native debug binding accepted {label}")

def main : IO Unit := do
  let changed ← IO.ofExcept (CanonCertificate.checkBindings CanonBinding.snapshots)
  unless changed do throw (IO.userError "native debug binding did not exercise changed IDs")
  IO.println s!"native-debug-binding: {CanonBinding.snapshots.size} complete snapshots checked"
  let (offset, before, after) := CanonBinding.snapshot
    (CanonBinding.sample "negative-controls" (CanonBinding.nested 33))
  reject "wrong live ID" #[(offset, before,
    { after with body := after.body.modify 0 (fun i => { i with id := i.id + 1000000 }) })]
  reject "wrong nested body" #[(offset, before,
    { after with body := after.body.modify 1 (fun i => { i with op := .block #[] }) })]
  reject "wrong layout" #[(offset, before,
    { after with layouts := after.layouts.modify 0 (fun l => { l with size := some 999999 }) })]
  reject "wrong function metadata" #[(offset, before, { after with targetOs := "wrong" })]
  reject "wrong offset" #[(offset - 1, before, after)]
  let some metadata := CanonBinding.metadataSamples[0]?
    | throw (IO.userError "missing global metadata control")
  let (offset, before, after) := CanonBinding.snapshot metadata
  reject "wrong global initializer" #[(offset, before,
    { after with globals := after.globals.modify 0 (fun g => { g with init := some (.int 0 999999) }) })]
  -- A genuine batch must fail if just one item is wrong, even after valid items.
  reject "one bad item" (CanonBinding.snapshots.push (offset, before, { after with name := "wrong" }))
  let report ← IO.ofExcept (CanonCertificate.emit CanonBinding.snapshots)
  IO.print report
