import Air2Lean.Check

open Air2Lean

-- Actual eager exporter layouts differ for this edge between the approved versions.
private def types : Array Ty :=
  #[.errorSet (some #["Bad"]), .int false 64, .array 0 1 false, .errorUnion 0 2]
private def layouts (size align : Nat) : Array Layout :=
  #[{ size := some 2, align := some 2 }, { size := some 8, align := some 8 },
    { size := some 0, align := some 8 }, { size := some size, align := some align }]

def main : IO Unit := do
  let current := checkMemTy "zeroArray16" types (layouts 8 8) 1 3
  unless current.toOption.isSome do
    throw (IO.userError s!"0.16 zero-payload layout rejected: {current}")
  for version in ["0.14.1", "0.15.2"] do
    let legacy := checkMemTy version types (layouts 2 2) 1 3
    match legacy with
    | .ok _ => throw (IO.userError s!"accepted incompatible {version} zero-payload layout")
    | .error message =>
      unless message.contains "size 8 and alignment 8, the compiler 2 and 2" do
        throw (IO.userError s!"wrong rejection for {version}: {message}")
  IO.println "Error-union version layout checks passed"
