import Air2Lean
import Air2Lean.Check
open Air2Lean

private def get (out : Except String α) : IO α := match out with
  | .ok value => pure value
  | .error message => throw (IO.userError message)
private def require (test : Bool) (why : String) : IO Unit :=
  unless test do throw (IO.userError why)
private def reject (f : Func) : IO Unit :=
  match check f with
  | .ok _ => throw (IO.userError "accepted a representation-changing recursive cast")
  | .error _ => pure ()

def main : IO Unit := do
  -- Exact retained schema-11 list client; neither AIR nor historical Gen is rewritten.
  let raw ← get <| Raw.parseFile (← IO.FS.readFile "tests/golden/0.15.2/lists/air/lists.listSum.json")
  require (raw.body.any fun i => i.id == 66 && i.tag == "bitcast" &&
    i.ty == some 21 && i.args == #[.inst 65]) "retained raw list inst66 qualifier cast drift"
  let f ← get <| normalize raw
  let some (.optional sourcePointer) := f.types[5]?
    | throw (IO.userError "retained list source optional shape drift")
  let some (.optional targetPointer) := f.types[21]?
    | throw (IO.userError "retained list target optional shape drift")
  require (f.types[sourcePointer]? == some (.ptr "one" false 25) &&
    f.types[targetPointer]? == some (.ptr "one" true 25)) "retained list qualifier type shape drift"
  discard (get <| check f)
  -- Full callee-closure generation/proofs are checked by ROOT affected gates;
  -- this exact retained client control checks every per-function instruction.
  -- The exception requires identical complete layouts, including pointer alignment.
  let original := f.layouts[targetPointer]!
  reject {f with layouts := f.layouts.set! targetPointer {original with ptrAlign := some 4}}
  reject {f with layouts := f.layouts.set! targetPointer {original with sentinel := true}}
  reject {f with layouts := f.layouts.set! targetPointer {original with hostSize := 8, bitOffset := 1}}
  -- Same child alone is insufficient: a one/many conversion is not const-only.
  reject {f with types := f.types.set! targetPointer (.ptr "many" true 25)}
  -- No blanket identical-child exception: unchanged constness still requires the scan.
  reject {f with types := f.types.set! targetPointer (.ptr "one" false 25)}
  IO.println "retained recursive list qualifier controls passed"
