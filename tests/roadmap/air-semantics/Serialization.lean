import Air2Lean.CanonCertificate

/-! Structural layout regression for the actual certificate emitter. Generated Lean must
kernel-check and reconstruct every offset and complete Func, including wrapping at balanced
array boundaries. These are data-shape tests; their proof instances are emitted uniformly. -/

namespace CanonSerialization

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

def snapshots : Array (Nat × Func × Func) :=
  (widths.map fun n => snapshot (sample s!"leaf{n}" (leaf n))) ++
  (#[33, 65, 129].map fun n => snapshot (sample s!"nested{n}" (nested n)))

end CanonSerialization

def main (args : List String) : IO Unit := do
  let [out] := args | throw (IO.userError "expected a private certificate output path")
  let source ← IO.ofExcept (Air2Lean.CanonCertificate.emit CanonSerialization.snapshots "SerializedLayout")
  IO.FS.writeFile out ("import Serialization\n" ++ source ++
    "\n#eval do\n" ++
    "  let _ ← Air2Lean.CanonCertificate.checkSnapshots CanonSerialization.snapshots SerializedLayout.snapshots\n" ++
    "  IO.println s!\"serializer-layout: {CanonSerialization.snapshots.size} complete snapshots checked\"\n")
